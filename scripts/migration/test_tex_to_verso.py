#!/usr/bin/env python3
"""Unit tests for ``tex_to_verso.py`` (standard library only).

Run from the repository root with either of

    python3 -I scripts/migration/test_tex_to_verso.py
    python3 -I -m unittest discover -s scripts/migration -p 'test_tex_to_verso.py'

The tests that need the real blueprint sources / the golden sample / ``baseline_inventory.json``
skip themselves when those files are not present.
"""
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

import tex_to_verso as t  # noqa: E402

SRC = REPO / "blueprint" / "src"
GOLDEN = REPO / "ComplexAnalysisCourse" / "Chapters" / "ComplexNumbers.lean"
BASELINE = HERE / "baseline_inventory.json"
SCRIPT = HERE / "tex_to_verso.py"

MODULES = [m for _n, m, _g in t.CHAPTER_TABLE]


def ws(s: str) -> str:
    """Whitespace-normalise (collapse every run of whitespace)."""
    return " ".join(s.split())


# --------------------------------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------------------------------

TITLES = ["One", "Two", "Three", "Four", "Five", "Six", "Alpha", "Beta"]


def stub(n: str) -> str:
    return (f"\\section{{Stub {n}}}\n\\begin{{definition}}[Stub]\n  \\label{{def:stub_{n}}}\n"
            f"  Stub text.\n\\end{{definition}}\n")


def make_tree(root: Path, chapters: dict) -> Path:
    """Write a minimal ``blueprint/src``-like tree.  ``chapters`` maps a chapter number ("1".."6",
    "A", "B") to a TeX body or to a list of bodies (several ``\\input`` files).  Missing chapters get
    a one-node stub."""
    src = root / "src"
    src.mkdir(parents=True, exist_ok=True)
    content = ["Intro text with \\emph{emphasis}.\n"]
    for (num, _m, _g), title in zip(t.CHAPTER_TABLE, TITLES):
        if num == "A":
            content.append("\\appendix\n")
        content.append(f"\\chapter{{{title}}}\n")
        bodies = chapters.get(num, stub(num))
        if isinstance(bodies, str):
            bodies = [bodies]
        for k, body in enumerate(bodies):
            name = f"ch{num}_{k}.tex"
            (src / name).write_text(body, encoding="utf8")
            content.append(f"\\input{{{name}}}\n")
    (src / "content.tex").write_text("\n".join(content), encoding="utf8")
    return src


def convert_tree(chapters: dict, **kw):
    """Convert a synthetic tree; returns ``(Converter, {module: text})``."""
    with tempfile.TemporaryDirectory() as d:
        src = make_tree(Path(d), chapters)
        conv = t.Converter(src, **kw)
        conv.load()
        return conv, {ch.module: conv.render_chapter(ch) for ch in conv.chapters}


def one_node(body: str, env: str = "lemma", extra_header: str = "") -> str:
    """Convert a single node in chapter 2 and return the lines of its directive block."""
    tex = (f"\\section{{S}}\n\\begin{{{env}}}[T]\n  \\label{{lem:x}}\n{extra_header}\n{body}\n"
           f"\\end{{{env}}}\n")
    _c, mods = convert_tree({"2": tex})
    return mods["ComplexDerivative"]


def frag(tex: str, labels=None) -> str:
    return t.convert_fragment(tex, labels)


MATH = re.compile(r"\$\$`(.*?)`|\$`([^`]*)`", re.S)


def parse_modules(out_dir: Path):
    """Parse generated modules: ordered ``[(kind, label, opts, body_text)]`` of all directives and the
    ordered outline of headings."""
    blocks = []
    outline = []
    for mod in MODULES:
        path = out_dir / "Chapters" / f"{mod}.lean"
        lines = path.read_text(encoding="utf8").split("\n")
        i = 0
        while i < len(lines):
            m = re.match(r'#doc \(Manual\) "(.*)" =>$', lines[i])
            if m:
                outline.append(("chapter", m.group(1)))
            m = re.match(r"(#{1,2}) (.*)$", lines[i])
            if m:
                outline.append(("section" if len(m.group(1)) == 1 else "subsection", m.group(2)))
            m = re.match(r':::(definition|lemma_|theorem|corollary|proof|group) "([^"]*)"((?: \(\w+ := "[^"]*"\))*)$',
                         lines[i])
            if m:
                j = i + 1
                body = []
                while lines[j] != ":::":
                    body.append(lines[j])
                    j += 1
                opts = dict(re.findall(r'\((\w+) := "([^"]*)"\)', m.group(3)))
                blocks.append((m.group(1), m.group(2), opts, "\n".join(body)))
                if m.group(1) not in ("group", "proof"):
                    outline.append(("node", m.group(2)))
                i = j
            i += 1
    return blocks, outline


def math_spans(text: str):
    return [("display", ws(m.group(1))) if m.group(1) is not None else ("inline", ws(m.group(2)))
            for m in MATH.finditer(text)]


# --------------------------------------------------------------------------------------------------
# comments, maths, text
# --------------------------------------------------------------------------------------------------


class TestComments(unittest.TestCase):
    def strip(self, s):
        return t.strip_comments(s)[0]

    def test_comment_only_line_vanishes_without_paragraph_break(self):
        self.assertEqual(self.strip("a\n  %comment\nb"), "a\nb")
        self.assertEqual(frag("one\n  % hidden\ntwo"), "one\ntwo")

    def test_trailing_comment_keeps_line_break(self):
        self.assertEqual(self.strip("a b % c\nd"), "a b \nd")

    def test_glued_comment_joins_lines_like_tex(self):
        self.assertEqual(self.strip("foo%bar\n   baz"), "foobaz")

    def test_blank_line_after_glued_comment_is_a_paragraph_break(self):
        self.assertEqual(frag("foo%x\n\nbaz"), "foo\n\nbaz")

    def test_escaped_percent_is_not_a_comment(self):
        self.assertEqual(self.strip(r"50\% of $x\%y$ % gone"), r"50\% of $x\%y$ ")
        self.assertEqual(frag(r"50\% of it"), "50% of it")

    def test_line_numbers_survive_comment_removal(self):
        src = t.Src("f.tex", "% c1\n% c2\ntext\n  % c3\nmore")
        self.assertEqual(src.text, "text\nmore")
        self.assertEqual((src.line(0), src.line(src.text.index("more"))), (3, 5))


class TestMath(unittest.TestCase):
    def test_inline_math_and_whitespace_collapse(self):
        self.assertEqual(frag("Let $x \\in \\bC$ be."), "Let $`x \\in \\bC` be.")
        self.assertEqual(frag("$a\n    +   b$"), "$`a + b`")

    def test_math_with_comment_spanning_lines(self):
        tex = "denote $-z %= -x - \\ii \\, y\n    = (-x,-y) \\in \\bC$ and"
        self.assertEqual(frag(tex), "denote $`-z = (-x,-y) \\in \\bC` and")

    def test_math_content_is_verbatim(self):
        body = r"\Big\{ z_1 \; \Big| \; \sqrt[n]{z} \Big\} \, \\ \text{ for } a_{-1}^{*} [x]"
        self.assertEqual(frag(f"${body}$"), f"$`{body}`")

    def test_dollar_inside_braces_of_inline_math_is_nested_math(self):
        self.assertEqual(frag("$a \\text{ if $w \\ne 0$ } b$ end"), "$`a \\text{ if $w \\ne 0$ } b` end")

    def test_backtick_in_math_uses_longer_fence(self):
        self.assertEqual(t.fmt_inline_math("a ` b"), "$``a ` b``")

    def test_display_environment_is_verbatim_and_dedented(self):
        tex = ("text\n  \\begin{align*}\n    a &= b \\\\\n  % comment line\n    c &= d .\n"
               "  \\end{align*}\n\nnext")
        self.assertEqual(frag(tex), "text\n$$`\n\\begin{align*}\n  a &= b \\\\\n  c &= d .\n\\end{align*}\n`\n\nnext")

    def test_two_consecutive_displays_and_text_after(self):
        tex = "Have\n\\begin{align*}\n a\n\\end{align*}\n\\begin{align*}\n b\n\\end{align*}\nAlso."
        self.assertEqual(frag(tex),
                         "Have\n$$`\n\\begin{align*}\n a\n\\end{align*}\n`\n$$`\n\\begin{align*}\n b\n"
                         "\\end{align*}\n`\nAlso.")

    def test_display_in_the_middle_of_a_line(self):
        out = frag("where \\begin{align*} x \\end{align*} holds.")
        self.assertEqual(out, "where\n$$`\n\\begin{align*} x \\end{align*}\n`\nholds.")

    def test_unsupported_math_forms_fail_closed(self):
        for bad in ("$$x$$", "\\[ x \\]", "\\(x\\)", "\\begin{equation} x \\end{equation}",
                    "$unterminated", "$$"):
            with self.assertRaises(t.ConvError, msg=bad):
                frag(bad)


class TestText(unittest.TestCase):
    def test_roles(self):
        self.assertEqual(frag("a \\term{linear map} b"), "a {term}[linear map] b")
        self.assertEqual(frag("a \\term{pole of order $m \\in \\bN$} b"),
                         "a {term}[pole of order $`m \\in \\bN`] b")
        self.assertEqual(frag("See \\MetSpCourse{} and \\MetSpCourse."),
                         "See {metSpCourse}[] and {metSpCourse}[].")
        self.assertEqual(frag("\\textbf{Remark:} \\emph{x} and \\emph{ y z }."),
                         "*Remark:* _x_ and _y z_ .")

    def test_typography(self):
        self.assertEqual(frag("f(x),\\ldots, n--m and a---b"), "f(x),\u2026, n\u2013m and a\u2014b")
        self.assertEqual(frag("a~b"), "a\u00a0b")
        self.assertEqual(frag("``quoted'' and Cauchy's"), "\u201cquoted\u201d and Cauchy's")
        self.assertEqual(frag("M\\\"obius Poincar\\'e fa\\c{c}ade"), "M\u00f6bius Poincar\u00e9 fa\u00e7ade")

    def test_special_characters_are_escaped(self):
        self.assertEqual(frag("a * b [c,d] and \\{x\\} and \\$ and \\_"),
                         "a \\* b \\[c,d\\] and \\{x\\} and \\$ and \\_")

    def test_line_starting_with_block_opener(self):
        # inside a paragraph: rejoined to the previous line; first line of a paragraph: escaped
        self.assertEqual(frag("text\n- dash\n1. num\nend"), "text - dash 1. num\nend")
        self.assertEqual(frag("- dash\n\n+ plus\n\n3) n"), "\\- dash\n\n\\+ plus\n\n\\3) n")
        # a literal star is already escaped and thus never an opener
        self.assertEqual(frag("a\n* b"), "a\n\\* b")

    def test_leading_and_internal_whitespace_is_normalised(self):
        self.assertEqual(frag("   a   b  \n\t c  "), "a b\nc")
        self.assertEqual(frag("a\n\n\n\nb"), "a\n\nb")

    def test_fail_closed_on_unknown_constructs(self):
        for bad in ("\\textit{x}", "\\footnote{x}", "\\cite{x}", "\\\\", "a \\, b", "\\begin{center}x\\end{center}",
                    "x_y", "{bare}", "50 }", "\\verb|x|", "\\label{a}", "\\uses{a}", "a & b", "a ` b",
                    "\\section*{x}", "\\emph{}", "\\term{}"):
            with self.assertRaises(t.ConvError, msg=bad):
                frag(bad)

    def test_error_carries_file_and_line(self):
        with self.assertRaises(t.ConvError) as cm:
            t.convert_fragment("ok\n% comment\nfine\nbad \\unknowncmd here", name="demo.tex")
        self.assertEqual((cm.exception.file, cm.exception.line), ("demo.tex", 4))
        self.assertTrue(str(cm.exception).startswith("demo.tex:4: "))


class TestLists(unittest.TestCase):
    def test_itemize(self):
        tex = "Intro:\n  \\begin{itemize}\n    \\item one $x$\n      more\n    \\item two\n  \\end{itemize}\nAfter."
        self.assertEqual(frag(tex), "Intro:\n\n* one $`x`\n  more\n* two\n\nAfter.")

    def test_enumerate_uses_numbers(self):
        self.assertEqual(frag("\\begin{enumerate}\\item a\\item b\\end{enumerate}"), "1. a\n1. b")

    def test_nested_lists_are_indented(self):
        tex = ("\\begin{itemize}\n\\item outer\n \\begin{enumerate}\n \\item inner\n \\end{enumerate}\n"
               "\\item next\n\\end{itemize}")
        self.assertEqual(frag(tex), "* outer\n\n  1. inner\n* next")

    def test_paragraph_and_display_inside_an_item(self):
        tex = ("\\begin{itemize}\n\\item a\n\n  second\n\\item b\n\\begin{align*}\n x\n\\end{align*}\n"
               "\\end{itemize}")
        self.assertEqual(frag(tex), "* a\n\n  second\n* b\n  $$`\n  \\begin{align*}\n   x\n  \\end{align*}\n  `")

    def test_item_comments_vanish_and_item_starts_on_bullet_line(self):
        tex = "\\begin{itemize}\n\\item %for any $z$, and $-z %= q\n  %= r$ satisfies\n  $w$ ok\n\\end{itemize}"
        self.assertEqual(frag(tex), "* $`w` ok")

    def test_explicit_labels_description_bold_enumerate_plain(self):
        d = frag("\\begin{description}\\item[(R-1)] a\n b \\item[(R-2)] c\\end{description}")
        self.assertEqual(d, "* *(R-1)* a\n  b\n* *(R-2)* c")
        e = frag("\\begin{enumerate}\\item[(a)] a \\item[(b)] b\\end{enumerate}")
        self.assertEqual(e, "* (a) a\n* (b) b")
        i = frag("\\begin{itemize}\\item[(i)] a \\item[(ii)] b\\end{itemize}")
        self.assertEqual(i, "* (i) a\n* (ii) b")

    def test_list_errors(self):
        for bad in ("\\begin{itemize} text \\item a\\end{itemize}", "\\begin{itemize}\\item a",
                    "\\item a", "\\end{itemize}", "\\begin{itemize}\\item[]a\\end{itemize}"):
            with self.assertRaises(t.ConvError, msg=bad):
                frag(bad)


class TestRefs(unittest.TestCase):
    LABELS = {"lem:a": "lemma", "thm:b": "theorem", "cor:c": "corollary", "def:d": "definition"}

    def test_kind_word_and_tilde_are_dropped(self):
        self.assertEqual(frag("by Lemma~\\ref{lem:a} and Theorem~\\ref{thm:b},", self.LABELS),
                         'by {bpref "lem_a"}[] and {bpref "thm_b"}[],')
        self.assertEqual(frag("see\nCorollary~\\ref{cor:c}\nnow Definition \\ref{def:d}.", self.LABELS),
                         'see\n{bpref "cor_c"}[]\nnow {bpref "def_d"}[].')

    def test_bare_defref(self):
        self.assertEqual(frag("(\\defref{def:d}).", self.LABELS), '({bpref "def_d"}[]).')

    def test_ref_without_kind_word_fails(self):
        with self.assertRaises(t.ConvError):
            frag("see \\ref{lem:a}", self.LABELS)

    def test_dangling_ref_fails(self):
        with self.assertRaisesRegex(t.ConvError, "dangling"):
            frag("Lemma~\\ref{lem:zzz}", self.LABELS)

    def test_case_insensitive_unique_match_is_used_and_reported(self):
        ctx = t.Ctx({"thm:FOO": {"env": "theorem", "file": "f", "line": 1, "verso": "thm_FOO"}})
        parser = t.Parser(t.Src("f.tex", "Theorem~\\ref{thm:foo}"), ctx)
        blocks, _ = parser.parse_blocks()
        lines = t.Renderer(ctx).render_blocks(blocks, "f.tex")
        self.assertEqual(ctx.resolve_refs("\n".join(lines)), '{bpref "thm_FOO"}[]')
        cats = [n[0] for n in ctx.notices]
        self.assertEqual(cats, [t.CAT_REFFIX])

    def test_ambiguous_case_insensitive_match_fails(self):
        ctx = t.Ctx({"thm:Foo": {"env": "theorem", "file": "f", "line": 1, "verso": "thm_Foo"},
                     "thm:FOO": {"env": "theorem", "file": "f", "line": 2, "verso": "thm_FOO"}})
        with self.assertRaisesRegex(t.ConvError, "several labels"):
            ctx.resolve_label("thm:foo", "f", 3, "\\ref")

    def test_kind_word_mismatch_is_reported(self):
        ctx = t.Ctx({"lem:k": {"env": "corollary", "file": "f", "line": 1, "verso": "lem_k"}})
        parser = t.Parser(t.Src("f.tex", "Lemma~\\ref{lem:k}"), ctx)
        blocks, _ = parser.parse_blocks()
        text = "\n".join(t.Renderer(ctx).render_blocks(blocks, "f.tex"))
        self.assertEqual(ctx.resolve_refs(text), '{bpref "lem_k"}[]')
        self.assertEqual([n[0] for n in ctx.notices], [t.CAT_KIND])
        self.assertIn("Corollary", ctx.notices[0][3])


# --------------------------------------------------------------------------------------------------
# structure: nodes, proofs, titles, chapters
# --------------------------------------------------------------------------------------------------


class TestStructure(unittest.TestCase):
    def test_module_header_and_group_block(self):
        _c, mods = convert_tree({})
        text = mods["ComplexNumbers"]
        self.assertTrue(text.startswith(t.MODULE_HEADER + '\n#doc (Manual) "One" =>\n\n'
                                        ':::group "grp_complex_numbers"\nOne\n:::\n\n# Stub 1\n\n'))
        self.assertTrue(text.endswith(":::\n"))
        self.assertEqual(text.count("\n\n\n"), 0)

    def test_kind_comes_from_the_environment_not_the_label_prefix(self):
        tex = ("\\section{S}\n\\begin{corollary}[C]\n \\label{lem:looks_like_a_lemma}\n x\n\\end{corollary}\n"
               "\\begin{theorem}[T]\n \\label{def:odd}\n y\n\\end{theorem}\n"
               "\\begin{lemma}[L]\n \\label{lem:l}\n z\n\\end{lemma}\n"
               "\\begin{definition}[D]\n \\label{def:d}\n w\n\\end{definition}\n")
        _c, mods = convert_tree({"2": tex})
        text = mods["ComplexDerivative"]
        self.assertIn(':::corollary "lem_looks_like_a_lemma" (parent := "grp_complex_derivative")', text)
        self.assertIn(':::theorem "def_odd"', text)
        self.assertIn(':::lemma_ "lem_l"', text)
        self.assertIn(':::definition "def_d"', text)

    def test_labels_keep_case_and_replace_every_colon(self):
        conv, _m = convert_tree({"2": "\\begin{theorem}[T]\\label{thm:CAUCHY:Formula_2}x\\end{theorem}"})
        self.assertEqual(conv.label_map()["thm:CAUCHY:Formula_2"], "thm_CAUCHY_Formula_2")

    def test_uses_options_for_statement_and_proof(self):
        tex = ("\\section{S}\n\\begin{definition}[D]\n \\label{def:a}\n x\n\\end{definition}\n"
               "\\begin{lemma}[L]\n \\label{lem:b}\n \\uses{def:a}\n y\n\\end{lemma}\n"
               "\\begin{proof}\n \\uses{def:a, lem:b}\n z\n\\end{proof}\n"
               "\\begin{theorem}[T]\n \\label{thm:c}\n \\uses{}\n y\n\\end{theorem}\n"
               "\\begin{proof}\n \\uses{}\n z\n\\end{proof}\n")
        _c, mods = convert_tree({"2": tex})
        text = mods["ComplexDerivative"]
        self.assertIn(':::definition "def_a" (parent := "grp_complex_derivative")\n', text)
        self.assertIn(':::lemma_ "lem_b" (parent := "grp_complex_derivative") (uses := "def_a")\n', text)
        self.assertIn(':::proof "lem_b" (uses := "def_a, lem_b")\nz\n:::', text)
        self.assertIn(':::theorem "thm_c" (parent := "grp_complex_derivative")\n', text)
        self.assertIn(':::proof "thm_c"\nz\n:::', text)

    def test_title_and_palka_lead_in(self):
        def lead(arg):
            tex = f"\\section{{S}}\n\\begin{{lemma}}{arg}\n \\label{{lem:x}}\n Body.\n\\end{{lemma}}\n"
            _c, mods = convert_tree({"2": tex})
            m = re.search(r':::lemma_ "lem_x"[^\n]*\n(.*?)\n:::', mods["ComplexDerivative"], re.S)
            return m.group(1)
        self.assertEqual(lead("[Goursat's lemma \\Palka{Lem~V.1.1}]"),
                         "{nodetitle}[Goursat's lemma] {palka}[Lem V.1.1]\n\nBody.")
        self.assertEqual(lead("[Only a title]"), "{nodetitle}[Only a title]\n\nBody.")
        self.assertEqual(lead("[\\Palka{Thm~V.1.5}]"), "{palka}[Thm V.1.5]\n\nBody.")
        self.assertEqual(lead("[Math $n$th root of \\term{x} \\Palka{Sec.~I.1--3 and~(1.2)}]"),
                         "{nodetitle}[Math $`n`th root of {term}[x]] {palka}[Sec. I.1\u20133 and (1.2)]\n\nBody.")
        self.assertEqual(lead("[Title\n   over two lines \\Palka{X}]"),
                         "{nodetitle}[Title over two lines] {palka}[X]\n\nBody.")
        self.assertEqual(lead(""), "Body.")

    def test_missing_title_is_reported(self):
        tex = "\\section{S}\n\\begin{lemma}\\label{lem:x}\n Body.\n\\end{lemma}\n"
        conv, _m = convert_tree({"2": tex})
        conv.render_chapter(conv.chapters[1])
        self.assertTrue(any("no optional [Title]" in n[3] for n in conv.ctx.notices))

    def test_prose_between_nodes_and_headings(self):
        tex = ("\\section{First $x$}\nProse before.\n\n\\textbf{Remark:} a remark.\n"
               "\\begin{definition}[D]\\label{def:d}x\\end{definition}\nProse after.\n"
               "\\subsection{Sub}\n\\begin{lemma}[L]\\label{lem:l}y\\end{lemma}\n")
        _c, mods = convert_tree({"2": tex})
        body = mods["ComplexDerivative"].split(":::\n\n", 1)[1]
        self.assertEqual(
            body,
            "# First $`x`\n\nProse before.\n\n*Remark:* a remark.\n\n"
            ':::definition "def_d" (parent := "grp_complex_derivative")\n{nodetitle}[D]\n\nx\n:::\n\n'
            "Prose after.\n\n## Sub\n\n"
            ':::lemma_ "lem_l" (parent := "grp_complex_derivative")\n{nodetitle}[L]\n\ny\n:::\n')

    def test_chapters_one_and_four_merge_two_files_in_input_order(self):
        a = "\\section{A1}\n\\begin{definition}[D]\\label{def:a}x\\end{definition}\n"
        b = "\\section{B1}\n\\begin{definition}[E]\\label{def:b}y\\end{definition}\n"
        for num, mod in (("1", "ComplexNumbers"), ("4", "CauchyTheorem")):
            _c, mods = convert_tree({num: [a, b]})
            text = mods[mod]
            self.assertLess(text.index("# A1"), text.index("def_a"))
            self.assertLess(text.index("def_a"), text.index("# B1"))
            self.assertLess(text.index("# B1"), text.index("def_b"))

    def test_appendix_prefix_applies_to_document_titles_only(self):
        _c, mods = convert_tree({})
        self.assertIn('#doc (Manual) "Appendix: Alpha" =>', mods["TopologyBackground"])
        self.assertIn(':::group "grp_topology_background"\nAlpha\n:::', mods["TopologyBackground"])
        self.assertIn('#doc (Manual) "Appendix: Beta" =>', mods["CalculusBackground"])
        self.assertIn('#doc (Manual) "Six" =>', mods["Singularities"])
        _c, mods = convert_tree({}, appendix_prefix="App. ")
        self.assertIn('#doc (Manual) "App. Alpha" =>', mods["TopologyBackground"])

    def test_group_ids(self):
        _c, mods = convert_tree({})
        ids = re.findall(r':::group "(grp_\w+)"', "\n".join(mods[m] for m in MODULES))
        self.assertEqual(ids, ["grp_complex_numbers", "grp_complex_derivative", "grp_contour_integration",
                               "grp_cauchy_theorem", "grp_power_series", "grp_singularities",
                               "grp_topology_background", "grp_calculus_background"])

    def test_references_across_chapters_and_uses_forward_refs(self):
        tex2 = ("\\section{S}\n\\begin{lemma}[L]\\label{lem:two}\\uses{thm:later}\n"
                "By Theorem~\\ref{thm:later}.\\end{lemma}\n")
        tex3 = "\\section{S}\n\\begin{theorem}[T]\\label{thm:later}x\\end{theorem}\n"
        _c, mods = convert_tree({"2": tex2, "3": tex3})
        self.assertIn('(uses := "thm_later")\nBy', mods["ComplexDerivative"].replace("{nodetitle}[L]\n\n", ""))
        self.assertIn('{bpref "thm_later"}[]', mods["ComplexDerivative"])

    def test_case_insensitive_fix_in_uses_and_report(self):
        tex = ("\\section{S}\n\\begin{theorem}[T]\\label{thm:BIG}x\\end{theorem}\n"
               "\\begin{lemma}[L]\\label{lem:l}\\uses{thm:big}\nBy Theorem~\\ref{thm:Big}.\\end{lemma}\n")
        conv, mods = convert_tree({"2": tex})
        self.assertIn('(uses := "thm_BIG")', mods["ComplexDerivative"])
        self.assertIn('{bpref "thm_BIG"}[]', mods["ComplexDerivative"])
        rep = conv.report([], None)
        self.assertIn("## Reference fixes", rep)
        self.assertEqual(rep.count("case-insensitive match `thm:BIG`"), 2)

    def test_report_lists_commented_out_environments_lists_and_mismatches(self):
        tex = ("\\section{S}\n\\begin{theorem}[T]\\label{thm:t}x\n"
               "\\begin{description}\\item[(A-1)] a \\item[(A-2)] b\\end{description}\\end{theorem}\n"
               "\\begin{lemma}[L]\\label{lem:l}By Theorem~\\ref{lem:l}.\\end{lemma}\n"
               "%\\begin{theorem}[Old \\Palka{Thm~I.1}]\n%  \\label{thm:t}\n%  old text\n%\\end{theorem}\n"
               "%\\begin{proof}\n%  \\ldots\n%\\end{proof}\n"
               "%\\begin{lemma}\n%  \\label{lem:gone}\n%\\end{lemma}\n")
        conv, mods = convert_tree({"2": tex})
        rep = conv.report(["ComplexDerivative"], None, mods)
        self.assertIn("ch2_0.tex:5-11`: commented-out `theorem` (with a commented proof), label `thm:t`", rep)
        self.assertIn("title `Old \\Palka{Thm~I.1}`; the same label is live", rep)
        self.assertIn("commented-out `lemma`, label `lem:gone`", rep)
        self.assertNotIn("old text", "\n".join(mods.values()))
        self.assertIn("`description` with explicit item labels (A-1), (A-2)", rep)
        self.assertIn("the source says \"Theorem\" but `lem:l` is a lemma", rep)
        self.assertIn("## Labels whose prefix does not match the environment kind", rep)

    def test_proof_must_follow_its_statement(self):
        base = "\\section{S}\n\\begin{lemma}[L]\\label{lem:l}x\\end{lemma}\n"
        for bad in ("\\begin{proof}x\\end{proof}\n",                                  # no statement
                    base + "Prose.\n\\begin{proof}x\\end{proof}\n",                    # prose in between
                    base + "\\begin{proof}x\\end{proof}\n\\begin{proof}y\\end{proof}\n",  # two proofs
                    base + "\\begin{proof}\\end{proof}\n"):                            # empty proof
            with self.assertRaises(t.ConvError, msg=bad):
                convert_tree({"2": bad})
        # comments between a statement and its proof are fine
        convert_tree({"2": base + "% comment\n\n\\begin{proof}x\\end{proof}\n"})

    def test_dangling_uses_and_ref_fail(self):
        with self.assertRaisesRegex(t.ConvError, r"\\uses\{lem:nope\}.*dangling"):
            convert_tree({"2": "\\begin{lemma}[L]\\label{lem:l}\\uses{lem:nope}x\\end{lemma}"})
        with self.assertRaisesRegex(t.ConvError, r"\\ref\{lem:nope\}.*dangling"):
            convert_tree({"2": "\\begin{lemma}[L]\\label{lem:l}Lemma~\\ref{lem:nope}\\end{lemma}"})

    def test_label_errors(self):
        for bad, pat in (("\\begin{lemma}[L]x\\end{lemma}", "without a \\\\label"),
                         ("\\begin{lemma}[L]\\label{lem:a}x\\end{lemma}\\begin{lemma}[L]\\label{lem:a}y\\end{lemma}",
                          "duplicate label"),
                         ("\\begin{lemma}[L]\\label{a:b}x\\end{lemma}\\begin{lemma}[L]\\label{a_b}y\\end{lemma}",
                          "collide"),
                         ("\\begin{lemma}[L]\\label{a b}x\\end{lemma}", "characters outside"),
                         ("\\begin{lemma}[L]\\label{lem:a}x", "missing \\\\end"),
                         ("\\begin{lemma}[L]\\label{lem:a}x\\label{lem:b}\\end{lemma}", "only supported directly"),
                         ("\\begin{lemma}[L]\\label{lem:a}\\begin{lemma}[M]\\label{lem:b}y\\end{lemma}\\end{lemma}",
                          "unexpected")):
            with self.assertRaisesRegex(t.ConvError, pat, msg=bad):
                convert_tree({"2": bad})

    def test_unknown_top_level_constructs_fail_with_file_and_line(self):
        tex = "\\section{S}\n\n\\begin{lemma}[L]\\label{lem:l}\n  \\begin{tabular}{c}a\\end{tabular}\n\\end{lemma}\n"
        with self.assertRaises(t.ConvError) as cm:
            convert_tree({"2": tex})
        self.assertEqual((cm.exception.file, cm.exception.line), ("ch2_0.tex", 4))
        self.assertIn("tabular", cm.exception.msg)
        for bad in ("\\subsubsection{x}", "\\chapter{x}", "\\input{x}", "\\paragraph{x}"):
            with self.assertRaises(t.ConvError, msg=bad):
                convert_tree({"2": bad})

    def test_content_tex_errors(self):
        with tempfile.TemporaryDirectory() as d:
            src = make_tree(Path(d), {})
            (src / "content.tex").write_text("\\chapter{A}\n\\input{ch1_0.tex}\n", encoding="utf8")
            with self.assertRaisesRegex(t.ConvError, "expected 8 chapters"):
                t.Converter(src).load()
            src = make_tree(Path(d), {})
            (src / "ch1_0.tex").unlink()
            with self.assertRaisesRegex(t.ConvError, "does not exist"):
                t.Converter(src).load()

    def test_output_is_deterministic(self):
        tex = "\\section{S}\n\\begin{lemma}[L \\Palka{X}]\\label{lem:l}\\uses{def:stub_1}\nText $x$.\\end{lemma}\n"
        outs = [convert_tree({"2": tex})[1] for _ in range(2)]
        self.assertEqual(outs[0], outs[1])


# --------------------------------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------------------------------


class TestCli(unittest.TestCase):
    def run_cli(self, *args):
        return subprocess.run([sys.executable, "-I", str(SCRIPT), *args], capture_output=True, text=True)

    def test_writes_modules_label_map_and_report_and_only_filter(self):
        with tempfile.TemporaryDirectory() as d:
            src = make_tree(Path(d), {})
            out = Path(d) / "out"
            r = self.run_cli("--src", str(src), "--out", str(out), "--only", "2,a")
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(sorted(p.name for p in (out / "Chapters").glob("*.lean")),
                             ["ComplexDerivative.lean", "TopologyBackground.lean"])
            lm = json.loads((out / "label_map.json").read_text(encoding="utf8"))
            self.assertEqual(lm["def:stub_B"], "def_stub_B")
            self.assertEqual(len(lm), 8)
            self.assertIn("# TeX to Verso conversion report", (out / "report.md").read_text(encoding="utf8"))
            r = self.run_cli("--src", str(src), "--out", str(out), "--appendix-prefix", "Anhang: ")
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn('"Anhang: Alpha"', (out / "Chapters" / "TopologyBackground.lean").read_text(encoding="utf8"))

    def test_unknown_selector_is_a_usage_error(self):
        with tempfile.TemporaryDirectory() as d:
            src = make_tree(Path(d), {})
            r = self.run_cli("--src", str(src), "--out", str(Path(d) / "o"), "--only", "9")
            self.assertEqual(r.returncode, 2)

    def test_fail_closed_exit_status_and_location(self):
        with tempfile.TemporaryDirectory() as d:
            src = make_tree(Path(d), {"3": "\\section{S}\nline two \\weird{x}\n"})
            out = Path(d) / "out"
            r = self.run_cli("--src", str(src), "--out", str(out))
            self.assertEqual(r.returncode, 1)
            self.assertIn("ch3_0.tex:2: unsupported command \\weird", r.stderr)
            self.assertFalse((out / "Chapters").exists())


# --------------------------------------------------------------------------------------------------
# real sources: golden sample and baseline parity
# --------------------------------------------------------------------------------------------------


@unittest.skipUnless(SRC.is_dir() and (SRC / "content.tex").is_file(), "blueprint/src not available")
class TestRealSources(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.out = Path(cls.tmp.name) / "out"
        cls.conv = t.run(SRC, cls.out)
        cls.blocks, cls.outline = parse_modules(cls.out)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    @unittest.skipUnless(GOLDEN.is_file(), "golden sample not available")
    def test_golden_first_section_of_chapter_one(self):
        gen = (self.out / "Chapters" / "ComplexNumbers.lean").read_text(encoding="utf8")
        first = gen.split("\n# ")
        head = "\n# ".join(first[:2])          # preamble + first section only
        self.assertEqual(ws(head), ws(GOLDEN.read_text(encoding="utf8")))

    def test_all_eight_modules_exist_with_expected_titles(self):
        titles = [o[1] for o in self.outline if o[0] == "chapter"]
        self.assertEqual(titles, [
            "The complex number system", "Complex derivatives and analytic functions", "Contour integration",
            "Cauchy's theorem and consequences", "Power series", "Isolated singularities and residues",
            "Appendix: Topological preliminaries", "Appendix: Preliminaries from calculus"])

    def test_known_source_defect_is_fixed_and_reported(self):
        text = (self.out / "Chapters" / "CauchyTheorem.lean").read_text(encoding="utf8")
        self.assertIn('{bpref "thm_FUNDAMENTAL_THEOREM_OF_ALGEBRA"}[]', text)
        self.assertNotIn("thm_fundamental_theorem_of_algebra", text)
        rep = (self.out / "report.md").read_text(encoding="utf8")
        self.assertIn("cauchy_consequences.tex:153", rep)
        self.assertIn("thm:FUNDAMENTAL_THEOREM_OF_ALGEBRA", rep.split("## Commented-out")[0])

    def test_commented_out_statements_are_reported_not_ported(self):
        rep = (self.out / "report.md").read_text(encoding="utf8")
        sec = rep.split("## Commented-out statement environments")[1].split("\n## ")[0]
        self.assertEqual(sec.count("\n* "), 6)
        self.assertEqual(sec.count("singularities.tex"), 3 + 3)   # three entries + "live at" mentions
        self.assertEqual(sec.count("topology_background.tex"), 3)
        text = (self.out / "Chapters" / "TopologyBackground.lean").read_text(encoding="utf8")
        self.assertNotIn("def_function_limit", text)
        self.assertNotIn("Riemann extension theorem", (self.out / "Chapters" / "Singularities.lean").read_text(encoding="utf8"))

    def test_description_lists_are_reported(self):
        rep = (self.out / "report.md").read_text(encoding="utf8")
        self.assertEqual(rep.count("`description` with explicit item labels"), 3)
        self.assertIn("(R-1), (R-2), (R-3), (R-4)", rep)

    def test_no_tex_leftovers_outside_maths(self):
        for mod in MODULES:
            text = (self.out / "Chapters" / f"{mod}.lean").read_text(encoding="utf8")
            plain = MATH.sub(" ", text)
            self.assertNotRegex(plain, r"\\(term|Palka|ref|defref|label|uses|emph|textbf|item|begin|end|ldots|"
                                       r"MetSpCourse|section|subsection)\b", mod)
            self.assertNotIn("~", plain)
            self.assertNotIn("\x00", text)
            self.assertNotIn("``", plain.replace("$$`", "").replace("`\n", ""))

    def test_output_has_no_trailing_whitespace_or_triple_newlines(self):
        for mod in MODULES:
            text = (self.out / "Chapters" / f"{mod}.lean").read_text(encoding="utf8")
            self.assertNotRegex(text, r"[ \t]\n", mod)
            self.assertNotIn("\n\n\n", text, mod)
            self.assertTrue(text.endswith(":::\n"))

    def test_run_is_deterministic(self):
        with tempfile.TemporaryDirectory() as d:
            t.run(SRC, Path(d))
            for p in sorted(self.out.rglob("*")):
                if p.is_file():
                    self.assertEqual(p.read_bytes(), (Path(d) / p.relative_to(self.out)).read_bytes(), p.name)

    # -- baseline parity ---------------------------------------------------------------------------
    @unittest.skipUnless(BASELINE.is_file(), "baseline_inventory.json not available")
    def test_baseline_parity(self):
        base = json.loads(BASELINE.read_text(encoding="utf8"))
        kinds = {"definition": "definition", "lemma": "lemma_", "theorem": "theorem", "corollary": "corollary"}
        nodes = {}
        proofs = {}
        order = []
        for kind, label, opts, body in self.blocks:
            if kind == "group":
                continue
            uses = [u.strip() for u in opts.get("uses", "").split(",") if u.strip()]
            if kind == "proof":
                proofs[label] = (uses, body)
            else:
                nodes[label] = (kind, uses, body, opts.get("parent"))
                order.append(label)
        bn = base["nodes"]
        # counts per kind, proofs, edges
        self.assertEqual(len(nodes), base["counts"]["nodes"])
        by_kind = {k: sum(1 for v in nodes.values() if v[0] == kinds[k]) for k in kinds}
        self.assertEqual(by_kind, base["counts"]["by_kind"])
        self.assertEqual(len(proofs), base["counts"]["proofs"])
        self.assertEqual(sum(len(v[1]) for v in nodes.values()), base["counts"]["statement_edges"])
        self.assertEqual(sum(len(v[0]) for v in proofs.values()), base["counts"]["proof_edges"])
        # labels (after ':' -> '_') in document order, label_map, kinds
        self.assertEqual(order, [n["label_verso"] for n in bn])
        lm = json.loads((self.out / "label_map.json").read_text(encoding="utf8"))
        self.assertEqual(lm, {n["label"]: n["label_verso"] for n in bn})
        self.assertEqual(len(set(lm.values())), len(lm))
        chapter_groups = {num: "grp_" + m for num, m in
                          zip(["1", "2", "3", "4", "5", "6", "A", "B"],
                              ["complex_numbers", "complex_derivative", "contour_integration", "cauchy_theorem",
                               "power_series", "singularities", "topology_background", "calculus_background"])}
        for n in bn:
            v = n["label_verso"]
            kind, uses, body, parent = nodes[v]
            self.assertEqual(kind, kinds[n["env"]], v)
            self.assertEqual(parent, chapter_groups[n["chapter"]], v)
            self.assertEqual(uses, n["statement_uses_verso"], v)
            self.assertEqual(v in proofs, n["has_proof"], v)
            # maths spans: the title is rendered as the first paragraph; the baseline has body spans only
            lead, _sep, rest = body.partition("\n\n")
            if not lead.startswith(("{nodetitle}", "{palka}")):
                lead, rest = "", body
            title_spans = [("inline", ws(m)) for m in re.findall(r"\$`([^`]*)`", lead)]
            raw_title = [("inline", ws(m.group(1))) for m in
                         re.finditer(r"(?<!\\)\$(.+?)(?<!\\)\$", n["title_raw"].replace("\n", " "))]
            self.assertEqual(title_spans, raw_title, v)
            expected = [(s["kind"], ws(s["tex"])) for s in n["math_spans"]]
            self.assertEqual(math_spans(rest), expected, v)
            if n["has_proof"]:
                puses, pbody = proofs[v]
                self.assertEqual(puses, n["proof_uses_verso"], v)
                self.assertEqual(math_spans(pbody), [(s["kind"], ws(s["tex"])) for s in n["proof_math_spans"]], v)
            # one {palka} per node that has a reference; {term}/{ref} counts per node
            self.assertEqual(lead.count("{palka}["), 1 if "\\Palka" in n["title_raw"] else 0, v)
            self.assertEqual(body.count("{term}["), n["n_term"], v)
        # overall counts
        allbody = "\n".join(b[3] for b in self.blocks)
        self.assertEqual(allbody.count("{palka}["), base["counts"]["palka"])
        self.assertEqual(allbody.count("{term}["), base["counts"]["term"])
        modtext = "\n".join((self.out / "Chapters" / f"{m}.lean").read_text(encoding="utf8") for m in MODULES)
        self.assertEqual(modtext.count("{bpref \""), 14)
        # outline: chapters, sections, subsections and nodes in document order
        base_outline = []
        for o in base["outline"]:
            if o["type"] == "chapter":
                base_outline.append(("chapter", ("Appendix: " if o["number"].isalpha() else "") + o["title"]))
            elif o["type"] in ("section", "subsection"):
                base_outline.append((o["type"], o["title"]))
            elif o["type"] == "node":
                base_outline.append(("node", o["label_verso"]))
        self.assertEqual(len(self.outline), len(base_outline))
        for (gk, gv), (bk, bv) in zip(self.outline, base_outline):
            self.assertEqual(gk, bk)
            if gk == "node":
                self.assertEqual(gv, bv)
            else:
                gv = ws(re.sub(r"\$`([^`]*)`", r"$\1$", gv).replace("\u00a0", " "))
                self.assertEqual(gv, ws(bv.replace("~", " ")))

    @unittest.skipUnless(BASELINE.is_file(), "baseline_inventory.json not available")
    def test_summary_counts_match_baseline(self):
        base = json.loads(BASELINE.read_text(encoding="utf8"))["counts"]
        c = self.conv.counts()
        self.assertEqual(c["by_kind"], base["by_kind"])
        self.assertEqual((c["nodes"], c["proofs"]), (base["nodes"], base["proofs"]))
        self.assertEqual((c["statement_edges"], c["proof_edges"]), (base["statement_edges"], base["proof_edges"]))
        self.assertEqual((c["sections"], c["subsections"], c["palka"]),
                         (base["sections"], base["subsections"], base["palka"]))


if __name__ == "__main__":
    unittest.main(verbosity=1)

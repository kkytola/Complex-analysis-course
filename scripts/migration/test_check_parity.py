#!/usr/bin/env python3
"""Unit tests for check_parity.py (standard library only).

Run:  python3 scripts/migration/test_check_parity.py          (or: python3 -m unittest discover -s scripts/migration)

The tests fabricate small Verso trees / inventories / manifests (see `Tree`, `render_tree`, `make_manifest`), check that
the clean tree passes and that each deliberate defect is detected by the intended check.  A realistic full-size tree is
rendered from the real baseline_inventory.json when that file is present (193 nodes, all of chapters 1-6 and A, B).
"""
from __future__ import annotations

import contextlib
import copy
import io
import json
import os
import re
import stat
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_parity as cp  # noqa: E402

REAL_INVENTORY = os.path.join(HERE, "baseline_inventory.json")
KIND = {"definition": "definition", "lemma": "lemma_", "theorem": "theorem", "corollary": "corollary"}


# ----------------------------------------------------------------------------------------------------------------------
# fabricated inventory
# ----------------------------------------------------------------------------------------------------------------------

def dump_json(path, obj):
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(obj, fh)


def dump_text(path, text):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


def sp(kind, tex):
    return {"kind": kind, "tex": tex}


def mk_node(order, ch, number, env, label, title, su=(), pu=(), proof=False, spans=(), pspans=(), nterm=0, npalka=0, nref=0):
    return {
        "order": order, "chapter": ch, "number": number, "file": f"ch{ch}.tex", "line": order, "env": env,
        "label": label, "label_verso": label.replace(":", "_"), "title_raw": title,
        "statement_uses": list(su), "statement_uses_verso": [u.replace(":", "_") for u in su],
        "has_proof": proof, "proof_uses": list(pu), "proof_uses_verso": [u.replace(":", "_") for u in pu],
        "math_spans": list(spans), "proof_math_spans": list(pspans), "n_term": nterm, "n_palka": npalka, "n_ref": nref,
    }


def small_inventory():
    nodes = [
        mk_node(1, "1", "1.1", "definition", "def:c", r"Complex numbers \Palka{Sec.~I.1}",
                spans=[sp("inline", r"\bC = \bR^2"), sp("display", r"\begin{align*} a &= b \\ c &= d \end{align*}")],
                nterm=1, npalka=1),
        mk_node(2, "1", "1.2", "theorem", "thm:field", r"The field $\bC$ \Palka{Thm~I.2}", su=["def:c"], pu=["def:c"], proof=True,
                spans=[sp("inline", r"z + w = w + z")], pspans=[sp("inline", r"z = w")], nterm=2, npalka=1, nref=1),
        mk_node(3, "1", "1.3", "lemma", "lem:l1", "A lemma", su=["def:c", "thm:field"], proof=False, spans=[sp("inline", r"x \in \bC")]),
        mk_node(4, "1", "1.4", "corollary", "lem:higher", "A corollary \\Palka{Cor~V.3.2}", su=["lem:l1"], pu=["lem:l1"], proof=True,
                spans=[sp("inline", r"f \in \Smooth(U)")], npalka=1),
        mk_node(5, "2", "2.1", "definition", "def:d", "Derivative", spans=[sp("inline", r"f'(z_0)")], nterm=1),
        mk_node(6, "2", "2.2", "lemma", "lem:chain", "Chain rule \\Palka{Thm~III.1.1}", su=["def:d", "def:c"], pu=["def:d"], proof=True,
                spans=[sp("inline", r"(g \circ f)'")], npalka=1),
        mk_node(7, "A", "A.1", "definition", "def:open", "Open sets", spans=[sp("inline", r"U \subset \bC")]),
        mk_node(8, "A", "A.2", "lemma", "lem:t1", r"\Palka{Lem~A.1}", su=["def:open"], pu=["def:open"], proof=True,
                spans=[sp("inline", r"\bdry U")], npalka=1),
    ]
    outline = [
        {"type": "chapter", "title": "Numbers", "number": "1"},
        {"type": "section", "title": "Basics", "chapter": "1"}, {"type": "node", "label_verso": "def_c", "chapter": "1"},
        {"type": "node", "label_verso": "thm_field", "chapter": "1"},
        {"type": "section", "title": "More about $\\bC$", "chapter": "1"},
        {"type": "subsection", "title": "Sub A", "chapter": "1"},
        {"type": "node", "label_verso": "lem_l1", "chapter": "1"}, {"type": "node", "label_verso": "lem_higher", "chapter": "1"},
        {"type": "chapter", "title": "Derivatives and Cauchy's theorem", "number": "2"},
        {"type": "section", "title": "Derivative", "chapter": "2"}, {"type": "node", "label_verso": "def_d", "chapter": "2"},
        {"type": "node", "label_verso": "lem_chain", "chapter": "2"},
        {"type": "chapter", "title": "Topological preliminaries", "number": "A"},
        {"type": "section", "title": "Topology", "chapter": "A"}, {"type": "node", "label_verso": "def_open", "chapter": "A"},
        {"type": "node", "label_verso": "lem_t1", "chapter": "A"},
    ]
    chapters = [
        {"title": "Numbers", "files": ["ch1.tex"], "appendix": False, "number": "1"},
        {"title": "Derivatives and Cauchy's theorem", "files": ["ch2.tex"], "appendix": False, "number": "2"},
        {"title": "Topological preliminaries", "files": ["chA.tex"], "appendix": True, "number": "A"},
    ]
    inv = cp.Inventory({"chapters": chapters, "nodes": nodes, "outline": outline, "intro": "Intro \\emph{one} text.\n\nSecond para."})
    t = inv.totals()
    inv.data["counts"] = {k: t[k] for k in ("nodes", "by_kind", "proofs", "statement_edges", "proof_edges", "sections", "subsections", "palka", "term")}
    return inv.data


# ----------------------------------------------------------------------------------------------------------------------
# rendering an inventory into a Verso tree (an independent mini "converter" used only by the tests)
# ----------------------------------------------------------------------------------------------------------------------

def fence(tex):
    k = 1
    while "`" * k in tex:
        k += 1
    return "`" * k


def span_md(s):
    f = fence(s["tex"])
    if s["kind"] == "inline":
        return "$" + f + s["tex"] + f
    return "$$" + f + "\n" + s["tex"].replace("\\\\ ", "\\\\\n") + "\n" + f


def title_md(t):
    return re.sub(r"\$([^$]*)\$", lambda m: "$`" + m.group(1) + "`", t)


def camel(title):
    return "".join(w[:1].upper() + w[1:] for w in re.findall(r"[A-Za-z]+", title.replace("'", "")))


def render_node(n, gid):
    lab = n["label_verso"]
    opts = f' (parent := "{gid}")'
    if n["statement_uses_verso"]:
        opts += f' (uses := "{", ".join(n["statement_uses_verso"])}")'
    out = [f':::{KIND[n["env"]]} "{lab}"{opts}']
    plain_title = re.sub(r"\\Palka\{[^{}]*\}", "", n["title_raw"]).strip()
    palka = re.findall(r"\\Palka\{([^{}]*)\}", n["title_raw"])
    lead = []
    if plain_title:
        lead.append("{nodetitle}[" + title_md(plain_title) + "]")
    for pk in palka:
        lead.append("{palka}[" + pk.replace("~", " ") + "]")
    if lead:
        out += [" ".join(lead), ""]
    body = []
    for i in range(n["n_term"]):
        body.append("A {term}[defined term " + chr(ord("a") + i) + "] is mentioned.")
    for s in n["math_spans"]:
        body.append("Here is " + span_md(s) + " and more." if s["kind"] == "inline" else "We have\n" + span_md(s))
    if n["n_ref"] and not n["has_proof"]:
        body += ['See {bpref "' + lab + '"}[].'] * n["n_ref"]
    out += body if body else ["Statement."]
    out.append(":::")
    if n["has_proof"]:
        po = f' (uses := "{", ".join(n["proof_uses_verso"])}")' if n["proof_uses_verso"] else ""
        out += ["", f':::proof "{lab}"{po}']
        pb = []
        for s in n["proof_math_spans"]:
            pb.append("Proof of " + span_md(s) + " here.")
        pb += ['By {bpref "' + lab + '"}[].'] * n["n_ref"] if n["n_ref"] else []
        out += pb if pb else ["…"]
        out.append(":::")
    return "\n".join(out) + "\n"


def module_header(title, imports=("Verso", "VersoManual", "VersoBlueprint", "ComplexAnalysisCourse.Macros", "ComplexAnalysisCourse.Roles")):
    return "\n".join(f"import {i}" for i in imports) + f'\n\nopen Verso.Genre\nopen Verso.Genre.Manual\nopen Informal\n\n#doc (Manual) "{title}" =>\n\n'


def render_chapter(inv, ch, offset_title=True):
    c = inv.chapter_by_number[ch]
    title = ("Appendix: " + c["title"]) if c.get("appendix") else c["title"]
    gid = "grp_ch" + ch
    out = [module_header(title), f':::group "{gid}"\n{title}\n:::\n']
    by_label = inv.by_label
    for o in inv.outline_of_chapter(ch):
        if o["type"] == "section":
            out.append("# " + title_md(o["title"]) + "\n")
        elif o["type"] == "subsection":
            out.append("## " + title_md(o["title"]) + "\n")
        else:
            out.append(render_node(by_label[o["label_verso"]], gid))
    return "\n".join(out)


def render_macros(inv):
    used = set()
    for n in inv.nodes:
        for s in n["math_spans"] + n["proof_math_spans"]:
            used |= cp.macros_in(s["tex"])
    custom = sorted(m for m in used if m not in cp.STANDARD_MACROS)
    body = "\n".join(f"\\newcommand{{\\{m}}}{{\\mathrm{{{m}}}}}" for m in custom) or "\\newcommand{\\unusedmacro}{x}"
    return ('import Verso\nimport VersoManual\nimport VersoBlueprint\n\nopen Informal\n\n-- macros\ntex_prelude\n  r#"' + body + '"#\n')


ROLES = """import VersoManual

open Verso Doc Elab
open Verso.Genre Manual

@[role]
def term : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.bold #[$content,*])

@[role]
def palka : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.concat #[Inline.text "[Palka1991, ", $content,*, Inline.text "]"])

@[role]
def nodetitle : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.emph #[$content,*])

@[role]
def metSpCourse : RoleExpanderOf Unit
  | (), _ => ``(Inline.bold #[Inline.text "MS-C1541 Metric Spaces"])
"""


def render_blueprint(inv, modnames):
    intro = re.sub(r"\\emph\{([^{}]*)\}", r"_\1_", inv["intro"] if isinstance(inv, dict) else inv.intro)
    incs = "\n".join(f"{{include 0 ComplexAnalysisCourse.Chapters.{m}}}\n" for m in modnames)
    return (module_header("MS-C1300 Complex Analysis", ("Verso", "VersoManual", "VersoBlueprint", "VersoBlueprint.Commands.Graph"))
            + "%%%\nauthors := [\"A. Author\"]\n%%%\n\n" + intro + "\n\n" + incs + "\n{blueprint_graph}\n")


class Tree:
    """A fabricated repository: relative path -> text."""

    def __init__(self, files):
        self.files = dict(files)

    @classmethod
    def from_inventory_dict(cls, data):
        inv = cp.Inventory(copy.deepcopy(data))
        files = {}
        mods = []
        for c in inv.chapters:
            m = camel(c["title"])
            mods.append(m)
            files[f"ComplexAnalysisCourse/Chapters/{m}.lean"] = render_chapter(inv, c["number"])
        files["ComplexAnalysisCourse/Macros.lean"] = render_macros(inv)
        files["ComplexAnalysisCourse/Roles.lean"] = ROLES
        files["ComplexAnalysisCourse/Blueprint.lean"] = render_blueprint(inv, mods)
        t = cls(files)
        t.modules = mods
        return t

    def chap(self, name):
        return f"ComplexAnalysisCourse/Chapters/{name}.lean"

    def edit(self, path, old, new, count=1):
        txt = self.files[path]
        assert old in txt, f"{old!r} not found in {path}"
        self.files[path] = txt.replace(old, new, count)

    def write(self, root):
        for rel, txt in self.files.items():
            p = os.path.join(root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(txt)

    def drop_modules(self, *names):
        """Remove chapter modules and their `{include}` lines (a half-ported repository)."""
        bp = "ComplexAnalysisCourse/Blueprint.lean"
        for m in names:
            del self.files[self.chap(m)]
            self.files[bp] = self.files[bp].replace(f"{{include 0 ComplexAnalysisCourse.Chapters.{m}}}\n", "")

    def copy(self):
        t = Tree(self.files)
        t.modules = list(self.modules)
        return t


# ----------------------------------------------------------------------------------------------------------------------
# fabricated generator output
# ----------------------------------------------------------------------------------------------------------------------

def make_manifest(data, offset, path_for=None):
    inv = cp.Inventory(copy.deepcopy(data))
    previews = []
    counters: dict = {}
    for n in inv.nodes:
        ch = n["chapter"]
        counters[ch] = counters.get(ch, 0) + 1
        disp = f"{cp.render_chapter(ch, offset)}.{counters[ch]}"
        base = {
            "authoredLabel": n["label_verso"], "label": n["label_verso"], "kind": n["env"], "parent": "grp_ch" + ch,
            "parentTitle": inv.chapter_by_number[ch]["title"], "targetKind": "block",
            "statementUses": [{"intent": "regular", "label": u, "origin": "manual"} for u in n["statement_uses_verso"]],
            "proofUses": [{"intent": "regular", "label": u, "origin": "manual"} for u in n["proof_uses_verso"]],
            "sourceLocation": {"ok": True, "error": None, "location": {"path": (path_for or (lambda c: f"/x/{c}.lean"))(ch),
                                                                       "range": {"start": {"line": n["order"] * 10, "character": 0}}}},
        }
        previews.append(dict(base, facet="statement", key=n["label_verso"] + "--statement", displayLabel=disp,
                             title=f"{n['env'].capitalize()} {disp}"))
        if n["has_proof"]:
            previews.append(dict(base, facet="proof", key=n["label_verso"] + "--proof", displayLabel="for " + disp, title="Proof for " + disp))
    groups = [{"label": "grp_ch" + c["number"], "title": c["title"], "declared": True,
               "entries": [{"label": n["label_verso"]} for n in inv.nodes_of_chapter[c["number"]]]} for c in inv.chapters]
    graphs = [{"key": "g", "nodes": [{"label": n["label_verso"], "warnings": {"unknownRef": False}} for n in inv.nodes], "edges": []}]
    return {"previews": previews, "groups": groups, "graphs": graphs, "vbpInternalSchemaVersion": 10, "sourceDocuments": []}


FAKE_VBP = '''#!/usr/bin/env python3
import json, os, sys
args = sys.argv[1:]
sys.stderr.write("warning: upstream noise on stderr that must be ignored\\n")
assert args[0] == "query", args
args = args[1:]
if args[:1] == ["--site"]:
    args = args[2:]
manifest = json.load(open(os.environ["FAKE_VBP_MANIFEST"]))
noise = os.environ.get("FAKE_VBP_STDOUT_NOISE")
if noise:
    print(noise)
stmts = [p for p in manifest["previews"] if p["facet"] == "statement"]
if args[0] == "stats":
    by = {}
    for p in stmts:
        by[p["kind"]] = by.get(p["kind"], 0) + 1
    print(json.dumps({"apiStability": "unstable", "statements": len(stmts), "byKind": by, "byOwner": {}, "byTag": {}}))
elif args[0] == "labels":
    print(json.dumps({"apiStability": "unstable", "labels": stmts}))
elif args[0] == "node":
    lab = args[1]
    st = [p for p in stmts if p["authoredLabel"] == lab][0]
    pr = [p for p in manifest["previews"] if p["facet"] == "proof" and p["authoredLabel"] == lab]
    print(json.dumps(dict(st, proof=(pr[0] if pr else None), apiStability="unstable")))
else:
    sys.exit(2)
'''


# ----------------------------------------------------------------------------------------------------------------------
# helpers for the test cases
# ----------------------------------------------------------------------------------------------------------------------

class Base(unittest.TestCase):
    DATA = None  # inventory dict
    EXTRA = ()   # extra CLI args

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.dir = self._tmp.name
        self.inv_path = os.path.join(self.dir, "inventory.json")
        self.root = os.path.join(self.dir, "repo")
        os.makedirs(self.root)

    def run_tree(self, tree, *extra, data=None):
        with open(self.inv_path, "w", encoding="utf-8") as fh:
            json.dump(data or self.DATA, fh)
        tree.write(self.root)
        # remove chapter files that a test deleted from the tree
        d = os.path.join(self.root, cp.CHAPTERS_DIR)
        keep = {os.path.basename(p) for p in tree.files if p.startswith(cp.CHAPTERS_DIR)}
        if os.path.isdir(d):
            for fn in os.listdir(d):
                if fn not in keep:
                    os.remove(os.path.join(d, fn))
        argv = ["--inventory", self.inv_path, "--root", self.root, *self.EXTRA, *extra]
        opts = cp.build_parser().parse_args(argv)
        results, ctx = cp.run(opts)
        self.last_argv = argv
        return {c.id: c for c in results}

    def exit_code(self, *extra):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            code = cp.main(["--inventory", self.inv_path, "--root", self.root, *self.EXTRA, *extra])
        self.last_output = buf.getvalue()
        return code

    def assertFailsOnly(self, res, *ids):
        failing = sorted(i for i, c in res.items() if c.status == cp.FAIL)
        self.assertEqual(sorted(ids), failing, "\n" + "\n".join(f"{c.status} {c.id}: {c.summary}\n   " + "\n   ".join(c.details[:8]) for c in res.values() if c.status == cp.FAIL))

    def assertFails(self, res, id_, *needles):
        c = res[id_]
        self.assertEqual(cp.FAIL, c.status, f"{id_} should FAIL: {c.summary}")
        text = c.summary + "\n" + "\n".join(c.details)
        for nd in needles:
            self.assertIn(nd, text, f"{id_} details should mention {nd!r}:\n{text}")

    def assertNoFail(self, res):
        bad = [c for c in res.values() if c.status == cp.FAIL]
        self.assertEqual([], [f"{c.id}: {c.summary} {c.details[:6]}" for c in bad])


# ----------------------------------------------------------------------------------------------------------------------
# tests on the small fabricated inventory
# ----------------------------------------------------------------------------------------------------------------------

class SmallTreeTests(Base):
    DATA = small_inventory()
    EXTRA = ("--anchors", "none", "--appendix-offset", "2")

    def tree(self):
        return Tree.from_inventory_dict(self.DATA)

    def test_clean_tree_passes_everything(self):
        res = self.run_tree(self.tree())
        self.assertNoFail(res)
        self.assertEqual(0, self.exit_code(), self.last_output)
        for id_ in ("V2.counts", "V2.labels", "V2.kinds", "V2.proofs", "V2.edges", "V2.targets", "V2.groups", "V2.order",
                    "V2.headings", "V2.outline", "V2.numbers", "V3.math", "V3.imports", "V4.counts", "V4.titles", "V4.tex",
                    "V4.escapes", "V4.intro", "V4.global"):
            self.assertEqual(cp.PASS, res[id_].status, f"{id_}: {res[id_].summary} {res[id_].details}")

    def test_missing_node(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        start = txt.index(':::lemma_ "lem_l1"')
        end = txt.index(':::corollary "lem_higher"')
        t.files[path] = txt[:start] + txt[end:]
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "missing node: lem_l1")
        self.assertFails(res, "V2.counts", "nodes: expected 8, actual 7", "lemma: expected 3, actual 2")
        self.assertFails(res, "V2.numbers", "lem_higher: expected number 1.4")
        self.assertNotEqual(0, self.exit_code())

    def test_extra_node(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::theorem "thm_field"', ':::theorem "thm_extra" (parent := "grp_ch1")\nExtra.\n:::\n\n:::theorem "thm_field"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "extra node (not in the inventory): thm_extra")
        self.assertFails(res, "V2.counts", "nodes: expected 8, actual 9")

    def test_duplicate_label(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::lemma_ "def_c"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "duplicate node label def_c")

    def test_wrong_kind(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::theorem "lem_l1"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.kinds", "lem_l1: expected kind lemma (`:::lemma_`), actual theorem")
        self.assertFails(res, "V2.counts")

    def test_lemma_without_underscore_is_unknown_directive(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::lemma "lem_l1"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "unknown directive `:::lemma`")

    def test_wrong_statement_edge(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), '(uses := "def_c, thm_field")', '(uses := "def_c")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.edges", "lem_l1 statement uses: missing ['thm_field'], extra []")

    def test_wrong_proof_edge(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), ':::proof "lem_chain" (uses := "def_d")', ':::proof "lem_chain" (uses := "def_c")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.edges", "lem_chain proof uses: missing ['def_d'], extra ['def_c']")

    def test_edge_moved_from_proof_to_statement(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::proof "lem_higher" (uses := "lem_l1")', ':::proof "lem_higher"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.edges", "lem_higher proof uses: missing ['lem_l1']")

    def test_role_uses_counts_as_edge(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::proof "lem_higher" (uses := "lem_l1")', ':::proof "lem_higher" (uses := "lem_l1")\nAnd {uses "def_c"}[].')
        res = self.run_tree(t)
        self.assertFails(res, "V2.edges", "lem_higher proof uses: missing [], extra ['def_c']")

    def test_swapped_order(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        a = txt.index(':::lemma_ "lem_l1"')
        b = txt.index(':::corollary "lem_higher"')
        end = txt.index(':::proof "lem_higher"')
        end = txt.index(":::\n", end + 5) + 4
        t.files[path] = txt[:a] + txt[b:end] + "\n" + txt[a:b] + txt[end:]
        res = self.run_tree(t)
        self.assertFails(res, "V2.order", "same elements, different order", "lem_l1")
        self.assertFails(res, "V2.numbers", "lem_l1: expected number 1.3")

    def test_altered_maths(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), r"$`z + w = w + z`", r"$`z + w = w + w`")
        res = self.run_tree(t)
        self.assertFails(res, "V3.math", "thm_field", r"z + w = w + z", r"z + w = w + w")

    def test_whitespace_changes_in_maths_are_tolerated(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), r"$`z + w = w + z`", "$`z   +\n  w = w + z`")
        res = self.run_tree(t)
        self.assertEqual(cp.PASS, res["V3.math"].status)

    def test_inline_vs_display_kind(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), r"$`\bC = \bR^2`", "$$`\\bC = \\bR^2`")
        res = self.run_tree(t)
        self.assertFails(res, "V3.math", "def_c", "inline `\\bC = \\bR^2`", "display `\\bC = \\bR^2`")

    def test_swapped_maths_spans(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "$`\\bC = \\bR^2`", "$`\\bC = \\bR^2`X")  # keep file valid; then swap below
        t.edit(t.chap("Numbers"), "$`\\bC = \\bR^2`X", "$`\\bC = \\bR^2`")
        txt = t.files[t.chap("Numbers")]
        a = "Here is $`\\bC = \\bR^2` and more."
        b = "We have\n$$`\n\\begin{align*} a &= b \\\\\nc &= d \\end{align*}\n`"
        self.assertIn(a, txt)
        self.assertIn(b, txt)
        t.files[t.chap("Numbers")] = txt.replace(a, "@@A@@").replace(b, a).replace("@@A@@", b)
        res = self.run_tree(t)
        self.assertFails(res, "V3.math", "def_c")

    def test_proof_maths_vs_statement_maths(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "Proof of $`z = w` here.", "Proof here.")
        t.edit(t.chap("Numbers"), "Here is $`z + w = w + z` and more.", "Here is $`z + w = w + z` and $`z = w` more.")
        res = self.run_tree(t)
        self.assertFails(res, "V3.math", "thm_field", "proof maths: expected 1 span(s), found 0")

    def test_title_math_not_counted_as_span(self):
        res = self.run_tree(self.tree())
        self.assertEqual(cp.PASS, res["V3.math"].status)  # `The field $\bC$` has maths in the title

    def test_missing_proof(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        a = txt.index(':::proof "thm_field"')
        b = txt.index(":::\n", a + 5) + 4
        t.files[path] = txt[:a] + txt[b:]
        res = self.run_tree(t)
        self.assertFails(res, "V2.proofs", "thm_field: TeX has a proof but there is no `:::proof \"thm_field\"`", "number of proofs: expected 4, actual 3")

    def test_extra_proof(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::proof "def_c"\n…\n:::\n\n:::lemma_ "lem_l1"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.proofs", "def_c: TeX has no proof but the Verso side has one")

    def test_orphan_and_misplaced_proof(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::proof "thm_field"', ':::proof "thm_nonexistent"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.proofs", "thm_nonexistent without a preceding statement")

    def test_proof_not_directly_after_statement(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        a = txt.index(':::proof "thm_field"')
        b = txt.index(":::\n", a + 5) + 4
        proof = txt[a:b]
        t.files[path] = txt[:a] + txt[b:]
        t.edit(path, ':::lemma_ "lem_l1"', ':::lemma_ "lem_l1"', 1)
        t.files[path] = t.files[path].replace('# More about $`\\bC`', proof + "\n# More about $`\\bC`")
        t.files[path] = t.files[path].replace(':::lemma_ "lem_l1"', ':::lemma_ "lem_l1"')
        # now the proof of thm_field comes after a heading but still before the next statement: allowed; move it past lem_l1
        t.files[path] = t.files[path].replace(proof + "\n", "").replace(':::corollary "lem_higher"', proof + "\n:::corollary \"lem_higher\"")
        res = self.run_tree(t)
        self.assertFails(res, "V2.proofs", "does not directly follow its statement")

    def test_colon_label_not_replaced(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), '"def_c"', '"def:c"', 1)
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "extra node (not in the inventory): def:c", "`:` not replaced")
        self.assertFails(res, "V2.syntax", "contains `:`")

    def test_uppercase_label_difference(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::theorem "thm_field"', ':::theorem "thm_Field"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "differs from thm_field only in case")

    def test_dangling_targets(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), '(uses := "def_c, thm_field")', '(uses := "def_c, thm_nope")')
        t.edit(t.chap("Numbers"), 'By {bpref "thm_field"}[].', 'By {bpref "def:c"}[] and {uses "lem_gone"}[].')
        res = self.run_tree(t)
        self.assertFails(res, "V2.targets", "thm_nope", "def:c", "lem_gone", "`:` not replaced")

    def test_missing_group_parent(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ' (parent := "grp_ch1") (uses := "def_c, thm_field")', ' (uses := "def_c, thm_field")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "`lem_l1` has no `(parent := \"grp_..\")`")

    def test_wrong_group_parent_and_missing_group(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ' (parent := "grp_ch1") (uses := "def_c, thm_field")', ' (parent := "grp_ch2") (uses := "def_c, thm_field")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "has parent 'grp_ch2', but this chapter's group is 'grp_ch1'")
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::group "grp_ch1"\nNumbers\n:::\n', "")
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "0 `:::group` directive(s), expected exactly one per chapter")

    def test_two_groups_and_shared_group_id(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::group "grp_ch1"\nNumbers\n:::\n', ':::group "grp_ch1"\nNumbers\n:::\n\n:::group "grp_other"\nX\n:::\n')
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "2 `:::group` directive(s)")
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), '"grp_ch2"', '"grp_ch1"', 1)
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "also used by")

    def test_group_id_prefix(self):
        t = self.tree()
        t.files[t.chap("Numbers")] = t.files[t.chap("Numbers")].replace("grp_ch1", "group1")
        res = self.run_tree(t)
        self.assertFails(res, "V2.groups", "does not start with `grp_`")

    def test_unknown_option_and_directive(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::lemma_ "lem_l1" (lean := "Foo.bar")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "unexpected option `(lean := ..)`")
        res = self.run_tree(t, "--allow-option", "lean")
        self.assertEqual(cp.PASS, res["V2.syntax"].status)
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::lemma_ "lem_l1"', ':::remark "x"\nfoo\n:::\n\n:::lemma_ "lem_l1"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "unknown directive `:::remark`")

    def test_unclosed_directive(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "Here is $`x \\in \\bC` and more.\n:::", "Here is $`x \\in \\bC` and more.\n")
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "is never closed")

    def test_unterminated_maths(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "$`z + w = w + z`", "$`z + w = w + z")
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "unterminated")
        self.assertEqual(cp.FAIL, res["V3.math"].status)

    def test_leftover_tex_commands(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), 'By {bpref "thm_field"}[].', r"By Lemma~\ref{def:c} and \term{x} and \label{foo}.")
        res = self.run_tree(t)
        self.assertFails(res, "V4.tex", r"leftover TeX command \ref", r"leftover TeX command \term", r"\label", "TeX tie")

    def test_leftover_begin_itemize_and_ldots(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), "Here is $`f'(z_0)` and more.", "\\begin{itemize} \\item x \\ldots \\end{itemize} \\textbf{b} \\emph{c} \\Palka{X} \\uses{a} \\defref{d}")
        res = self.run_tree(t)
        for name in ("begin", "item", "ldots", "end", "textbf", "emph", "Palka", "uses", "defref"):
            self.assertFails(res, "V4.tex", "leftover TeX command \\" + name)

    def test_leftover_tex_in_prose_and_headings(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "# Basics\n", "# Basics\n\nSome prose with \\textbf{Remark:} and $x$ math and ``quote'' and a--b.\n")
        res = self.run_tree(t)
        self.assertEqual(cp.FAIL, res["V4.tex"].status)
        text = "\n".join(res["V4.tex"].details)
        self.assertIn("textbf", text)
        self.assertIn("bare `$`", text)
        self.assertIn("TeX dash", text)

    def test_unescaped_specials(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), "Here is $`f'(z_0)` and more.",
               "Here is $`f'(z_0)` and a lone * star and [Palka1991, X] and a { brace and under_score here and `tick.")
        res = self.run_tree(t)
        self.assertEqual(cp.FAIL, res["V4.escapes"].status)
        text = "\n".join(res["V4.escapes"].details + res["V2.syntax"].details)
        self.assertIn("unescaped `[`", text)
        self.assertIn("unterminated role {brace", text)
        self.assertIn("odd number of unescaped `*`", text)

    def test_escaped_specials_are_fine(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), "Here is $`f'(z_0)` and more.",
               r"Here is $`f'(z_0)` and a lone \* star and \[Palka1991, X\] and a \{ brace \} and under\_score here and \`tick and *emph* and _it_.")
        res = self.run_tree(t)
        self.assertEqual(cp.PASS, res["V4.escapes"].status, res["V4.escapes"].details)
        self.assertEqual(cp.PASS, res["V4.tex"].status, res["V4.tex"].details)

    def test_block_opener_in_running_text(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), "Here is $`f'(z_0)` and more.", "Here is some text\n> not a quote\n## nor a heading")
        res = self.run_tree(t)
        self.assertFails(res, "V4.escapes", "block opener `>`", "block opener `##`")

    def test_term_and_palka_counts(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "A {term}[defined term a] is mentioned.", "A defined term a is mentioned.")
        res = self.run_tree(t)
        self.assertFails(res, "V4.counts", "def_c: {term} count expected 1, actual 0")
        t = self.tree()
        t.edit(t.chap("Numbers"), " {palka}[Sec. I.1]", "")
        res = self.run_tree(t)
        self.assertFails(res, "V4.counts", "def_c: {palka} count expected 1, actual 0")
        t = self.tree()
        t.edit(t.chap("Numbers"), "A {term}[defined term a] is mentioned.", "A {term}[defined term a] {term}[x] is mentioned.")
        res = self.run_tree(t)
        self.assertFails(res, "V4.counts", "def_c: {term} count expected 1, actual 2")

    def test_ref_count(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), 'By {bpref "thm_field"}[].', "By the definition.")
        res = self.run_tree(t)
        self.assertFails(res, "V4.counts", "thm_field: {bpref}/{uses} roles count expected 1, actual 0")

    def test_titles(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "{nodetitle}[A lemma]", "{nodetitle}[A lemmas]")
        res = self.run_tree(t)
        self.assertFails(res, "V4.titles", "lem_l1: title expected 'A lemma', actual 'A lemmas'")
        t = self.tree()
        t.edit(t.chap("Numbers"), "{nodetitle}[A lemma]\n\n", "")
        res = self.run_tree(t)
        self.assertFails(res, "V4.titles", "lem_l1: expected exactly one {nodetitle}[..]")
        t = self.tree()
        t.edit(t.chap("Numbers"), "{nodetitle}[The field $`\\bC`]", "{nodetitle}[The field $`\\bR`]")
        res = self.run_tree(t)
        self.assertFails(res, "V4.titles", "thm_field: title expected")
        t = self.tree()
        t.edit(t.chap("TopologicalPreliminaries"), "{palka}[Lem A.1]", "{nodetitle}[Surprise] {palka}[Lem A.1]")
        res = self.run_tree(t)
        self.assertFails(res, "V4.titles", "lem_t1: TeX has no title but there is a {nodetitle}[Surprise]")
        t = self.tree()
        t.edit(t.chap("Numbers"), "{palka}[Thm I.2]", "{palka}[Thm I.3]")
        res = self.run_tree(t)
        self.assertFails(res, "V4.titles", "{palka} text expected 'Thm I.2', actual 'Thm I.3'")

    def test_typographic_variants_in_titles_are_tolerated(self):
        t = self.tree()
        t.edit(t.chap("DerivativesAndCauchysTheorem"), "{nodetitle}[Chain rule]", "{nodetitle}[Chain\u00a0rule]")
        res = self.run_tree(t)
        self.assertEqual(cp.PASS, res["V4.titles"].status)

    def test_headings_and_outline(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "## Sub A", "# Sub A")
        res = self.run_tree(t)
        self.assertFails(res, "V2.headings", "# Sub A")
        t = self.tree()
        t.edit(t.chap("Numbers"), "# Basics", "# Basic")
        res = self.run_tree(t)
        self.assertFails(res, "V2.headings", "# Basic")
        t = self.tree()
        t.edit(t.chap("Numbers"), "## Sub A\n", "")
        res = self.run_tree(t)
        self.assertFails(res, "V2.headings", "## Sub A")
        t = self.tree()
        t.edit(t.chap("Numbers"), "## Sub A\n", "## Sub A\n\n### Deep\n")
        res = self.run_tree(t)
        self.assertFails(res, "V2.syntax", "heading level 3")

    def test_heading_moved_relative_to_nodes(self):
        t = self.tree()
        path = t.chap("Numbers")
        t.edit(path, "# More about $`\\bC`\n", "")
        t.edit(path, ":::theorem \"thm_field\"", "# More about $`\\bC`\n\n:::theorem \"thm_field\"")
        # the section/subsection order is untouched, but the position inside the node sequence moved
        res = self.run_tree(t)
        self.assertFails(res, "V2.outline", "headings sit at different places relative to the nodes")
        self.assertEqual(cp.PASS, res["V2.order"].status)
        self.assertEqual(cp.PASS, res["V2.headings"].status)

    def test_chapter_title_and_module_mapping(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), '#doc (Manual) "Numbers"', '#doc (Manual) "Numbersx"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "matches no chapter title; assigned to chapter 1 by its labels")
        t = self.tree()
        t.edit(t.chap("TopologicalPreliminaries"), '"Appendix: Topological preliminaries"', '"Topological preliminaries"')
        res = self.run_tree(t)
        self.assertEqual(cp.PASS, res["V2.modules"].status)  # appendix prefix is optional
        t = self.tree()
        t.edit(t.chap("Numbers"), '#doc (Manual) "Numbers"', '#doc (Manual) "Appendix: Numbers"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "unexpected `Appendix` prefix")

    def test_missing_chapter_module_full_mode(self):
        t = self.tree()
        del t.files[t.chap("TopologicalPreliminaries")]
        t.files["ComplexAnalysisCourse/Blueprint.lean"] = t.files["ComplexAnalysisCourse/Blueprint.lean"].replace(
            "{include 0 ComplexAnalysisCourse.Chapters.TopologicalPreliminaries}\n", "")
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "chapter A ('Topological preliminaries'): no chapter module")
        self.assertFails(res, "V2.labels", "missing node: def_open")

    def test_includes_order_and_missing_include(self):
        t = self.tree()
        bp = "ComplexAnalysisCourse/Blueprint.lean"
        a = "{include 0 ComplexAnalysisCourse.Chapters.Numbers}\n"
        b = "{include 0 ComplexAnalysisCourse.Chapters.DerivativesAndCauchysTheorem}\n"
        t.files[bp] = t.files[bp].replace(a, "@@").replace(b, a).replace("@@", b)
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "not included in chapter order")
        t = self.tree()
        t.files[bp] = t.files[bp].replace(a, "")
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "Numbers.lean: not included")
        t = self.tree()
        t.files[bp] = t.files[bp].replace(a, a + a)
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "included twice")
        t = self.tree()
        t.files[bp] = t.files[bp].replace(a, a + "{include 0 ComplexAnalysisCourse.Chapters.Ghost}\n")
        res = self.run_tree(t)
        self.assertFails(res, "V2.modules", "has no file")

    def test_missing_imports(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "import ComplexAnalysisCourse.Macros\n", "")
        res = self.run_tree(t)
        self.assertFails(res, "V3.imports", "Numbers.lean: missing `import ComplexAnalysisCourse.Macros`")

    def test_intro_text(self):
        t = self.tree()
        t.edit("ComplexAnalysisCourse/Blueprint.lean", "Second para.", "Second paragraph.")
        res = self.run_tree(t)
        self.assertFails(res, "V4.intro", "para.", "paragraph.")

    def test_macros_informational(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), r"$`x \in \bC`", r"$`x \in \bC \newthing`")
        res = self.run_tree(t)
        self.assertEqual(cp.INFO, res["V3.macros"].status)
        self.assertIn("\\newthing", "\n".join(res["V3.macros"].details))
        self.assertEqual(cp.FAIL, res["V3.math"].status)

    def test_global_counts(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), "# Basics\n", "# Basics\n\nProse with {term}[extra].\n")
        res = self.run_tree(t)
        self.assertFails(res, "V4.global", "total term: expected 4, actual 5")

    def test_numbers_with_appendix_offset(self):
        t = self.tree()
        res = self.run_tree(t, "--appendix-offset", "3")
        self.assertFails(res, "V2.numbers", "def_open: expected number 4.1 (legacy A.1), actual 3.1")
        res = self.run_tree(t, "--appendix-offset", "0")
        self.assertFails(res, "V2.numbers", "def_open: expected number A.1")

    def test_empty_bodies_do_not_crash(self):
        """Stress-test style tree: right labels/kinds/edges/groups but empty bodies -> clear reports, no crash."""
        data = self.DATA
        inv = cp.Inventory(copy.deepcopy(data))
        t = self.tree()
        for c in inv.chapters:
            m = camel(c["title"])
            title = ("Appendix: " + c["title"]) if c.get("appendix") else c["title"]
            out = [module_header(title), f':::group "grp_ch{c["number"]}"\n{c["title"]}\n:::\n']
            for n in inv.nodes_of_chapter[c["number"]]:
                opts = f' (parent := "grp_ch{c["number"]}")' + (f' (uses := "{", ".join(n["statement_uses_verso"])}")' if n["statement_uses_verso"] else "")
                out.append(f':::{KIND[n["env"]]} "{n["label_verso"]}"{opts}\nStatement.\n:::\n')
                if n["has_proof"]:
                    po = f' (uses := "{", ".join(n["proof_uses_verso"])}")' if n["proof_uses_verso"] else ""
                    out.append(f':::proof "{n["label_verso"]}"{po}\n…\n:::\n')
            t.files[t.chap(m)] = "\n".join(out)
        res = self.run_tree(t)
        for ok in ("V2.counts", "V2.labels", "V2.kinds", "V2.proofs", "V2.edges", "V2.targets", "V2.groups", "V2.order", "V2.numbers"):
            self.assertEqual(cp.PASS, res[ok].status, f"{ok}: {res[ok].summary} {res[ok].details}")
        self.assertFails(res, "V3.math", "NO maths at all was found")
        self.assertFails(res, "V4.counts")
        self.assertFails(res, "V4.titles", "expected exactly one {nodetitle}")
        self.assertFails(res, "V2.headings")
        self.assertEqual(1, self.exit_code())

    def test_crlf_line_endings(self):
        t = self.tree()
        for k in list(t.files):
            t.files[k] = t.files[k].replace("\n", "\r\n")
        res = self.run_tree(t)
        self.assertNoFail(res)

    def test_max_diffs_truncates(self):
        t = self.tree()
        t.files[t.chap("Numbers")] = t.files[t.chap("Numbers")].replace("{term}", "{x}")
        res = self.run_tree(t, "--max-diffs", "1")
        self.assertEqual(cp.FAIL, res["V4.counts"].status)
        self.assertLessEqual(len(res["V4.counts"].details), 2)
        self.assertIn("more", res["V4.counts"].details[-1])

    def test_exit_codes_and_report_format(self):
        t = self.tree()
        t.edit(t.chap("Numbers"), '(uses := "def_c, thm_field")', '(uses := "def_c")')
        self.run_tree(t)
        self.assertEqual(1, self.exit_code())
        self.assertIn("[FAIL] V2.edges", self.last_output)
        self.assertIn("lem_l1 statement uses: missing ['thm_field']", self.last_output)
        self.assertIn("RESULT: FAIL", self.last_output)
        t = self.tree()
        self.run_tree(t)
        self.assertEqual(0, self.exit_code())
        self.assertIn("RESULT: PASS", self.last_output)
        self.assertEqual(2, cp.main(["--inventory", os.path.join(self.dir, "nonexistent.json")]))

    def test_json_output(self):
        self.run_tree(self.tree())
        out = os.path.join(self.dir, "out.json")
        self.assertEqual(0, self.exit_code("--json", out))
        with open(out, encoding="utf-8") as fh:
            data = json.load(fh)
        self.assertTrue(any(c["id"] == "V2.labels" and c["status"] == "PASS" for c in data))


class SmallPartialTests(Base):
    DATA = small_inventory()
    EXTRA = ("--anchors", "none", "--appendix-offset", "2", "--partial")

    def tree(self):
        return Tree.from_inventory_dict(self.DATA)

    def test_only_first_chapter_ported_passes(self):
        t = self.tree()
        t.drop_modules("DerivativesAndCauchysTheorem", "TopologicalPreliminaries")
        res = self.run_tree(t)
        self.assertNoFail(res)
        self.assertEqual(cp.INFO, res["V2.coverage"].status)
        self.assertIn("not yet ported: 4 node(s)", "\n".join(res["V2.coverage"].details))
        self.assertEqual(0, self.exit_code())
        # without --partial the same tree fails
        opts = cp.build_parser().parse_args(["--inventory", self.inv_path, "--root", self.root, "--anchors", "none", "--appendix-offset", "2"])
        full = {c.id: c for c in cp.run(opts)[0]}
        self.assertEqual(cp.FAIL, full["V2.labels"].status)

    def test_partially_ported_chapter(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        cut = txt.index("# More about")
        t.files[path] = txt[:cut]  # only def_c and thm_field
        t.drop_modules("DerivativesAndCauchysTheorem", "TopologicalPreliminaries")
        res = self.run_tree(t)
        self.assertNoFail(res)
        self.assertEqual(cp.PASS, res["V2.numbers"].status)

    def test_partial_still_catches_defects_in_present_nodes(self):
        t = self.tree()
        path = t.chap("Numbers")
        t.files[path] = t.files[path][:t.files[path].index("# More about")]
        t.drop_modules("DerivativesAndCauchysTheorem", "TopologicalPreliminaries")
        t.edit(path, "$`z + w = w + z`", "$`z + w = w + w`")
        t.edit(path, ':::theorem "thm_field"', ':::lemma_ "thm_field"')
        t.edit(path, ':::group "grp_ch1"', ':::group "grp_chX"')
        t.files[path] = t.files[path].replace('(parent := "grp_ch1")', '(parent := "grp_chX")', 1)
        res = self.run_tree(t)
        self.assertFails(res, "V3.math", "thm_field")
        self.assertFails(res, "V2.kinds", "thm_field")
        self.assertFails(res, "V2.groups", "thm_field")
        # extras remain failures in partial mode
        t = self.tree()
        t.edit(t.chap("Numbers"), ':::theorem "thm_field"', ':::theorem "thm_extra" (parent := "grp_ch1")\nx\n:::\n\n:::theorem "thm_field"')
        res = self.run_tree(t)
        self.assertFails(res, "V2.labels", "thm_extra")

    def test_pending_targets_are_informational(self):
        t = self.tree()
        path = t.chap("Numbers")
        t.files[path] = t.files[path][:t.files[path].index("# More about")]
        t.drop_modules("DerivativesAndCauchysTheorem", "TopologicalPreliminaries")
        t.edit(path, '(uses := "def_c")', '(uses := "def_c, lem_chain")')
        res = self.run_tree(t)
        self.assertFails(res, "V2.edges", "thm_field statement uses")  # edge sets are compared against the inventory
        self.assertEqual(cp.PASS, res["V2.targets"].status)  # lem_chain exists in the inventory, just not ported yet
        self.assertIn("not yet ported", "\n".join(res["V2.targets"].details))

    def test_numbers_not_verifiable_when_earlier_nodes_missing(self):
        t = self.tree()
        path = t.chap("Numbers")
        txt = t.files[path]
        a = txt.index(':::definition "def_c"')
        b = txt.index(':::theorem "thm_field"')
        t.files[path] = txt[:a] + txt[b:]
        t.drop_modules("DerivativesAndCauchysTheorem", "TopologicalPreliminaries")
        res = self.run_tree(t)
        self.assertEqual(cp.PASS, res["V2.numbers"].status, res["V2.numbers"].details)
        self.assertIn("not verifiable", res["V2.numbers"].summary)

    def test_empty_verso_side_in_partial_mode(self):
        t = Tree({"ComplexAnalysisCourse/Roles.lean": ROLES})
        res = self.run_tree(t)
        self.assertNoFail(res)
        self.assertEqual(0, self.exit_code())


# ----------------------------------------------------------------------------------------------------------------------
# generator view: manifest and `vbp query`
# ----------------------------------------------------------------------------------------------------------------------

class GeneratorTests(Base):
    DATA = small_inventory()
    EXTRA = ("--anchors", "none", "--appendix-offset", "2")

    def setUp(self):
        super().setUp()
        self.manifest = make_manifest(self.DATA, 2)

    def write_manifest(self, manifest=None):
        d = os.path.join(self.root, "_out/site/html-multi/-verso-data")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "blueprint-manifest.json"), "w", encoding="utf-8") as fh:
            json.dump(manifest or self.manifest, fh)

    def run_manifest(self, manifest=None, *extra):
        t = Tree.from_inventory_dict(self.DATA)
        self.write_manifest(manifest)
        return self.run_tree(t, "--site", "_out/site", *extra)

    def test_clean_manifest(self):
        res = self.run_manifest()
        self.assertNoFail(res)
        for id_ in ("V2.counts[manifest]", "V2.labels[manifest]", "V2.kinds[manifest]", "V2.proofs[manifest]", "V2.edges[manifest]",
                    "V2.groups[manifest]", "V2.numbers[manifest]", "V2.order[manifest]", "V2.targets[manifest]"):
            self.assertEqual(cp.PASS, res[id_].status, f"{id_}: {res[id_].summary} {res[id_].details}")

    def test_wrong_rendered_number(self):
        m = copy.deepcopy(self.manifest)
        for p in m["previews"]:
            if p["authoredLabel"] == "lem_l1" and p["facet"] == "statement":
                p["displayLabel"] = "1.4"
        res = self.run_manifest(m)
        self.assertFails(res, "V2.numbers[manifest]", "lem_l1: expected number 1.3 (legacy 1.3), actual 1.4")

    def test_appendix_numbered_with_letter(self):
        m = copy.deepcopy(self.manifest)
        for p in m["previews"]:
            if p["authoredLabel"] == "def_open" and p["facet"] == "statement":
                p["displayLabel"] = "A.1"
        res = self.run_manifest(m)
        self.assertFails(res, "V2.numbers[manifest]", "def_open: expected number 3.1 (legacy A.1), actual A.1")
        res = self.run_manifest(m, "--appendix-offset", "0")
        self.assertEqual(cp.FAIL, res["V2.numbers[manifest]"].status)  # other appendix node still says 3.2 -> A.2 expected
        self.assertNotIn("def_open", "\n".join(res["V2.numbers[manifest]"].details))

    def test_manifest_edge_kind_proof_parent_defects(self):
        m = copy.deepcopy(self.manifest)
        for p in m["previews"]:
            if p["authoredLabel"] == "lem_chain":
                p["statementUses"] = p["statementUses"][:1]
                if p["facet"] == "proof":
                    p["proofUses"] = [{"intent": "regular", "label": "def_c", "origin": "manual"}]
            if p["authoredLabel"] == "thm_field" and p["facet"] == "statement":
                p["kind"] = "lemma"
            if p["authoredLabel"] == "def_d":
                p["parent"] = None
        m["previews"] = [p for p in m["previews"] if not (p["authoredLabel"] == "thm_field" and p["facet"] == "proof")]
        res = self.run_manifest(m)
        self.assertFails(res, "V2.edges[manifest]", "lem_chain statement uses: missing ['def_c']", "lem_chain proof uses: missing ['def_d'], extra ['def_c']")
        self.assertFails(res, "V2.kinds[manifest]", "thm_field: expected kind theorem")
        self.assertFails(res, "V2.proofs[manifest]", "thm_field: TeX has a proof")
        self.assertFails(res, "V2.groups[manifest]", "def_d: no group")

    def test_manifest_unknown_reference_warning_and_missing_node(self):
        m = copy.deepcopy(self.manifest)
        m["graphs"][0]["nodes"][0]["warnings"]["unknownRef"] = True
        m["previews"] = [p for p in m["previews"] if p["authoredLabel"] != "lem_t1"]
        res = self.run_manifest(m)
        self.assertFails(res, "V2.targets[manifest]", "unknownRef")
        self.assertFails(res, "V2.labels[manifest]", "missing node: lem_t1")

    def test_manifest_source_order(self):
        m = copy.deepcopy(self.manifest)
        for p in m["previews"]:
            if p["authoredLabel"] == "def_c":
                p["sourceLocation"]["location"]["range"]["start"]["line"] = 999
        res = self.run_manifest(m)
        self.assertFails(res, "V2.order[manifest]", "same elements, different order")

    def test_missing_manifest(self):
        t = Tree.from_inventory_dict(self.DATA)
        res = self.run_tree(t, "--site", "_out/nowhere")
        self.assertFails(res, "GEN.manifest", "no blueprint-manifest.json")

    def test_manifest_partial_numbers(self):
        m = copy.deepcopy(self.manifest)
        m["previews"] = [p for p in m["previews"] if p["authoredLabel"] in ("def_c", "thm_field")]
        res = self.run_manifest(m, "--partial")
        self.assertNoFail(res)

    # --- vbp query -------------------------------------------------------------------------------------------------
    def fake_vbp(self, manifest=None, noise=None):
        path = os.path.join(self.dir, "fake_vbp.py")
        dump_text(path, FAKE_VBP)
        os.chmod(path, os.stat(path).st_mode | stat.S_IXUSR)
        mf = os.path.join(self.dir, "fake_manifest.json")
        dump_json(mf, manifest or self.manifest)
        os.environ["FAKE_VBP_MANIFEST"] = mf
        if noise:
            os.environ["FAKE_VBP_STDOUT_NOISE"] = noise
        else:
            os.environ.pop("FAKE_VBP_STDOUT_NOISE", None)
        self.addCleanup(lambda: [os.environ.pop(k, None) for k in ("FAKE_VBP_MANIFEST", "FAKE_VBP_STDOUT_NOISE")])
        return f"{sys.executable} {path}"

    def test_vbp_stats_and_labels(self):
        cmd = self.fake_vbp()
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-cmd", cmd)
        self.assertNoFail(res)
        self.assertEqual(cp.PASS, res["V2.counts[vbp-stats]"].status)
        self.assertEqual(cp.PASS, res["V2.labels[vbp]"].status)
        self.assertEqual(cp.PASS, res["V2.kinds[vbp]"].status)
        self.assertNotIn("V2.numbers[vbp]", res)

    def test_vbp_nodes_full_cross_check(self):
        cmd = self.fake_vbp()
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-nodes", "--vbp-cmd", cmd)
        self.assertNoFail(res)
        for id_ in ("V2.edges[vbp]", "V2.numbers[vbp]", "V2.proofs[vbp]"):
            self.assertEqual(cp.PASS, res[id_].status, f"{id_}: {res[id_].summary}")

    def test_vbp_detects_wrong_numbers_and_edges_and_ignores_stderr(self):
        m = copy.deepcopy(self.manifest)
        for p in m["previews"]:
            if p["authoredLabel"] == "def_d" and p["facet"] == "statement":
                p["displayLabel"] = "2.5"
            if p["authoredLabel"] == "lem_l1":
                p["statementUses"] = []
        cmd = self.fake_vbp(m)
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-nodes", "--vbp-cmd", cmd)
        self.assertFails(res, "V2.numbers[vbp]", "def_d: expected number 2.1")
        self.assertFails(res, "V2.edges[vbp]", "lem_l1 statement uses: missing ['def_c', 'thm_field']")

    def test_vbp_stats_mismatch(self):
        m = copy.deepcopy(self.manifest)
        m["previews"] = [p for p in m["previews"] if p["authoredLabel"] != "def_d"]
        cmd = self.fake_vbp(m)
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-cmd", cmd)
        self.assertFails(res, "V2.counts[vbp-stats]", "stats.statements: expected 8, actual 7", "stats.byKind[definition]: expected 3, actual 2")

    def test_vbp_stdout_noise_tolerated_and_failure_reported(self):
        cmd = self.fake_vbp(noise="info: some lake chatter")
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-cmd", cmd)
        self.assertNoFail(res)
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--vbp", "--vbp-cmd", f"{sys.executable} -c 'import sys; sys.exit(3)'")
        self.assertFails(res, "GEN.vbp", "failed")

    def test_vbp_and_manifest_together(self):
        cmd = self.fake_vbp()
        self.write_manifest()
        res = self.run_tree(Tree.from_inventory_dict(self.DATA), "--site", "_out/site", "--vbp", "--vbp-nodes", "--vbp-cmd", cmd)
        self.assertNoFail(res)
        self.assertEqual(cp.PASS, res["GEN.consistency"].status)


class JsonStdoutTests(unittest.TestCase):
    def test_parse(self):
        self.assertEqual({"a": 1}, cp.parse_json_stdout('{"a": 1}\n'))
        self.assertEqual({"a": 1}, cp.parse_json_stdout('warning: x\n{"a": 1}\n'))
        self.assertEqual({"a": [1, 2]}, cp.parse_json_stdout('noise\n{\n "a": [1,\n 2]\n}\n'))
        with self.assertRaises(ValueError):
            cp.parse_json_stdout("no json here")


# ----------------------------------------------------------------------------------------------------------------------
# the scanner / parser on their own
# ----------------------------------------------------------------------------------------------------------------------

class ParserTests(unittest.TestCase):
    def test_maths_spans_inline_display_multiline_and_ticks(self):
        info = cp.analyze("A $`x_1 + [0,1]` b $$`\n\\begin{align*}\n  y &= 1 \\\\\n  z &= 2\n\\end{align*}\n` c $``a ` b`` d")
        self.assertEqual([("inline", "x_1 + [0,1]"), ("display", "\n\\begin{align*}\n  y &= 1 \\\\\n  z &= 2\n\\end{align*}\n"), ("inline", "a ` b")],
                         [(s.kind, s.tex) for s in info.spans])
        self.assertEqual([], info.problems)

    def test_math_content_is_never_text(self):
        info = cp.analyze(r"$`\ref{x} * _ [ { ~ --` ok")
        self.assertEqual([], info.problems)

    def test_roles_with_nested_content_and_math(self):
        info = cp.analyze('See {bpref "def_x"}[] and {term}[a $`[0,1]` set] and {nodetitle}[T $`n`th] {palka}[Sec. I.1].')
        self.assertEqual(["bpref", "term", "nodetitle", "palka"], [r.name for r in info.roles])
        self.assertEqual("def_x", info.roles[0].target)
        self.assertEqual("T $n$th", info.roles[2].text)
        self.assertTrue(info.spans[1].in_title and not info.spans[0].in_title)
        self.assertEqual([], info.problems)

    def test_nested_roles(self):
        info = cp.analyze("{term}[x {term}[y]] z")
        self.assertEqual(2, len(info.roles_named("term")))

    def test_list_markers_are_not_specials(self):
        info = cp.analyze("* one\n* two *b*\n  more\n1. num\n")
        self.assertEqual([], info.problems)

    def test_problems(self):
        info = cp.analyze("\\ldots and $x$ and ~ and a--b and [x] and {y} and } and ] and `t` and a lone *")
        msgs = " | ".join(p.msg for p in info.problems)
        for frag in ("leftover TeX command \\ldots", "bare `$`", "TeX tie", "TeX dash", "unescaped `[`", "unescaped `]`", "unescaped `}`",
                     "code span", "odd number"):
            self.assertIn(frag, msgs)

    def test_escapes(self):
        info = cp.analyze(r"\* \_ \[ \] \{ \} \` \$ \\ ok")
        self.assertEqual([], info.problems)
        self.assertEqual("* _ [ ] { } ` $ \\ ok", info.text())

    def test_line_numbers(self):
        info = cp.analyze("a\nb \\item\n", line0=10)
        self.assertEqual(11, info.problems[0].line)

    def test_directive_header_parsing(self):
        pos, opts, probs = cp.parse_args_string('"lem_x" (parent := "grp_a") (uses := "a, b,\n c")')
        self.assertEqual((["lem_x"], {"parent": "grp_a", "uses": "a, b,\n c"}, []), (pos, opts, probs))
        self.assertEqual(["a", "b", "c"], cp.split_uses("a, b,\n c"))
        pos, opts, probs = cp.parse_args_string('"x" (uses := a)')
        self.assertTrue(probs)

    def test_module_parse_structure(self):
        src = textwrap.dedent('''\
            import Verso
            import ComplexAnalysisCourse.Macros

            #doc (Manual) "My title" =>
            %%%
            file := "x"
            %%%

            :::group "grp_a"
            My title
            :::

            # Section one

            Some prose.

            :::lemma_ "lem_a" (parent := "grp_a")
            Text $`x
            :::
            y` more.
            :::

            ## Sub

            :::proof "lem_a"
            …
            :::
            ''')
        m = cp.parse_module("/x/M.lean", "M.lean", src)
        self.assertEqual("My title", m.title)
        self.assertEqual(["Verso", "ComplexAnalysisCourse.Macros"], m.imports)
        self.assertEqual([], m.errors)
        shape = [it[1].name if it[0] == "directive" else it[0] for it in m.items]
        self.assertEqual(["group", "heading", "prose", "lemma_", "heading", "proof"], shape)
        self.assertEqual([(1, "Section one"), (2, "Sub")], [(h[1], h[2]) for h in m.headings()])
        lem = m.statements()[0]
        self.assertEqual("lem_a", lem.label)
        self.assertEqual(1, len(lem.info.spans))  # the `:::` inside the maths is not a directive end
        self.assertIn(":::\ny", lem.info.spans[0].tex)

    def test_unknown_numbering_helpers(self):
        self.assertEqual("7", cp.render_chapter("A", 6))
        self.assertEqual("8", cp.render_chapter("B", 6))
        self.assertEqual("A", cp.render_chapter("A", 0))
        self.assertEqual("3", cp.render_chapter("3", 6))
        self.assertEqual("5.18", cp.expected_number({"number": "5.18"}, 6))
        self.assertEqual("8.3", cp.expected_number({"number": "B.3"}, 6))

    def test_canon_text(self):
        self.assertEqual("Cauchy's theorem", cp.canon_text("Cauchy\u2019s\u00a0theorem"))
        self.assertEqual("A $x$ B", cp.canon_text("A $ x $\n B"))
        self.assertEqual("a--b", cp.canon_text("a\u2013b"))
        self.assertEqual("Goursat's lemma", cp.tex_title_text("Goursat's lemma \\Palka{Lem~V.1.1}"))
        self.assertEqual(["Lem V.1.1"], cp.tex_palka_args("Goursat's lemma \\Palka{Lem~V.1.1}"))

    def test_macro_parsing(self):
        txt = 'tex_prelude\n  r#"\\newcommand{\\bN}{\\mathbb{N}}\n\\def\\set#1{x}\n\\renewcommand\\foo{y}\n\\DeclareMathOperator{\\Log}{Log}"#\n'
        self.assertEqual({"bN", "set", "foo", "Log"}, cp.parse_macros(txt))
        self.assertEqual({"frac", "bN"}, cp.macros_in(r"\frac{\bN}{2} \\ \\ x"))


# ----------------------------------------------------------------------------------------------------------------------
# full-size tree rendered from the real inventory
# ----------------------------------------------------------------------------------------------------------------------

@unittest.skipUnless(os.path.isfile(REAL_INVENTORY), "baseline_inventory.json not present")
class RealInventoryTests(Base):
    @classmethod
    def setUpClass(cls):
        with open(REAL_INVENTORY, encoding="utf-8") as fh:
            cls.DATA = json.load(fh)
        cls.base_tree = Tree.from_inventory_dict(cls.DATA)

    def tree(self):
        return self.base_tree.copy()

    def test_real_inventory_clean_tree_passes_including_anchors_and_totals(self):
        res = self.run_tree(self.tree())
        self.assertNoFail(res)
        self.assertEqual(0, self.exit_code(), self.last_output)
        self.assertIn("193 nodes", res["V2.counts"].summary)
        self.assertIn("69/81/30/13".replace("/", "/"), res["V2.inventory"].summary)
        self.assertIn("121 proofs", res["V2.counts"].summary)
        self.assertIn("330 statement + 121 proof edges", res["V2.counts"].summary)
        self.assertEqual(cp.PASS, res["V2.anchors"].status)
        self.assertIn("lem:abel=5.18", res["V2.anchors"].summary)
        self.assertIn("119 {term}, 86 {palka}", res["V4.global"].summary)
        self.assertEqual(cp.PASS, res["V3.math"].status)
        self.assertEqual(cp.PASS, res["V2.outline"].status)
        self.assertEqual("0 unknown", re.search(r"\d+ unknown", res["V3.macros"].summary).group())

    def test_real_numbers_follow_appendix_offset(self):
        res = self.run_tree(self.tree(), "--appendix-offset", "5")
        self.assertFails(res, "V2.numbers", "expected number 6.1 (legacy A.1), actual 7.1")

    def test_real_many_defects_at_once(self):
        t = self.tree()
        ch5 = [p for p in t.files if "PowerSeries" in p][0]
        t.edit(ch5, ':::lemma_ "lem_abel"', ':::theorem "lem_abel"')
        ch3 = [p for p in t.files if "ContourIntegration" in p][0]
        t.files[ch3] = t.files[ch3].replace('(uses := "def_complex_valued_integral")', "", 1) if "(uses := \"def_complex_valued_integral\")" in t.files[ch3] else t.files[ch3]
        res = self.run_tree(t)
        self.assertFails(res, "V2.kinds", "lem_abel: expected kind lemma")
        self.assertFails(res, "V2.counts", "nodes of kind lemma: expected 81, actual 80")

    def test_real_swap_two_nodes_changes_numbers_of_both(self):
        t = self.tree()
        path = [p for p in t.files if "ComplexNumbers" in p or "TheComplexNumberSystem" in p][0]
        txt = t.files[path]
        a = txt.index(':::definition "def_complex_conjugate"')
        b = txt.index(':::definition "def_absolute_value"')
        # swap whole blocks def_complex_conjugate+lemma and def_absolute_value+lemma
        c = txt.index(':::definition "def_argument"')
        t.files[path] = txt[:a] + txt[b:c] + txt[a:b] + txt[c:]
        res = self.run_tree(t)
        self.assertFails(res, "V2.order", "same elements, different order")
        self.assertFails(res, "V2.numbers", "def_absolute_value: expected number 1.5")
        self.assertFails(res, "V2.anchors", "def:absolute_value")

    def test_real_stress_style_tree_with_empty_bodies(self):
        inv = cp.Inventory(copy.deepcopy(self.DATA))
        t = self.tree()
        for c in inv.chapters:
            m = camel(c["title"])
            gid = "grp_ch" + c["number"]
            out = [module_header(c["title"] if not c.get("appendix") else "Appendix: " + c["title"]), f':::group "{gid}"\n{c["title"]}\n:::\n']
            for n in inv.nodes_of_chapter[c["number"]]:
                opts = f' (parent := "{gid}")' + (f' (uses := "{", ".join(n["statement_uses_verso"])}")' if n["statement_uses_verso"] else "")
                out.append(f':::{KIND[n["env"]]} "{n["label_verso"]}"{opts}\nStatement.\n:::\n')
                if n["has_proof"]:
                    po = f' (uses := "{", ".join(n["proof_uses_verso"])}")' if n["proof_uses_verso"] else ""
                    out.append(f':::proof "{n["label_verso"]}"{po}\n…\n:::\n')
            t.files[t.chap(m)] = "\n".join(out)
        res = self.run_tree(t)
        for ok in ("V2.counts", "V2.labels", "V2.kinds", "V2.proofs", "V2.edges", "V2.targets", "V2.groups", "V2.order", "V2.numbers", "V2.anchors"):
            self.assertEqual(cp.PASS, res[ok].status, f"{ok}: {res[ok].summary} {res[ok].details}")
        self.assertFails(res, "V3.math", "NO maths at all was found")
        self.assertEqual(1, self.exit_code())

    def test_real_manifest_and_vbp(self):
        inv = cp.Inventory(copy.deepcopy(self.DATA))
        manifest = make_manifest(self.DATA, 6)
        d = os.path.join(self.root, "_out/site/html-multi/-verso-data")
        os.makedirs(d, exist_ok=True)
        dump_json(os.path.join(d, "blueprint-manifest.json"), manifest)
        fake = os.path.join(self.dir, "fake_vbp.py")
        dump_text(fake, FAKE_VBP)
        mf = os.path.join(self.dir, "m.json")
        dump_json(mf, manifest)
        os.environ["FAKE_VBP_MANIFEST"] = mf
        self.addCleanup(lambda: os.environ.pop("FAKE_VBP_MANIFEST", None))
        res = self.run_tree(self.tree(), "--site", "_out/site", "--vbp", "--vbp-nodes", "--vbp-cmd", f"{sys.executable} {fake}")
        self.assertNoFail(res)
        self.assertEqual(cp.PASS, res["V2.anchors[manifest]"].status)
        self.assertEqual(cp.PASS, res["V2.numbers[vbp]"].status)
        self.assertIn("193 nodes", res["V2.counts[manifest]"].summary)
        # a rendered number that is off by one in chapter 5 is caught on the generator side
        for p in manifest["previews"]:
            if p["authoredLabel"] == "lem_abel" and p["facet"] == "statement":
                p["displayLabel"] = "5.19"
        dump_json(os.path.join(d, "blueprint-manifest.json"), manifest)
        res = self.run_tree(self.tree(), "--site", "_out/site")
        self.assertFails(res, "V2.numbers[manifest]", "lem_abel: expected number 5.18 (legacy 5.18), actual 5.19")
        self.assertFails(res, "V2.anchors[manifest]", "lem:abel (lem_abel): expected 5.18, actual 5.19")

    def test_real_partial_with_first_chapter_only(self):
        t = self.tree()
        t.drop_modules(*[m for m in t.modules if m != "TheComplexNumberSystem"])
        res = self.run_tree(t, "--partial")
        self.assertNoFail(res)
        self.assertEqual(cp.PASS, res["V2.anchors"].status)  # def:absolute_value = 1.5 lives in chapter 1
        self.assertIn("1 of 6", res["V2.anchors"].summary)
        self.assertEqual(cp.INFO, res["V2.coverage"].status)
        self.assertEqual(0, self.exit_code("--partial"))


if __name__ == "__main__":
    unittest.main(verbosity=1)

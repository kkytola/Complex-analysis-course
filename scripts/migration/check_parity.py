#!/usr/bin/env python3
"""Parity checker for the leanblueprint -> Verso Blueprint migration (plan section 9: V2, V3, V4).

Compares the TeX-side ground truth `baseline_inventory.json` with the Verso side:

  * the Lean sources  ComplexAnalysisCourse/Chapters/*.lean  (+ Macros.lean, Roles.lean, Blueprint.lean),
    parsed here by an independent, deliberately small markup parser ("source" view), and optionally
  * what the GENERATOR sees: the manifest `<site>/html-multi/-verso-data/blueprint-manifest.json`
    (`--site DIR`) and/or the JSON printed by `lake exe vbp query ...` (`--vbp`, `--vbp-nodes`).

Usage (standard library only; run from the repository root):

    python3 -I scripts/migration/check_parity.py [--inventory scripts/migration/baseline_inventory.json]
        [--root .] [--partial] [--appendix-offset 6]
        [--site _out/site] [--vbp [--vbp-nodes] [--vbp-cmd "lake exe vbp"]]
        [--max-diffs N] [--allow-option NAME ...] [--json OUT.json]

Prints one line per check (PASS / FAIL / INFO / SKIP) with precise diffs below failing checks and exits
with status 1 if any check FAILs (0 otherwise, 2 for unusable input).  `--partial` checks only the nodes
present on the Verso side and reports the rest as "not yet ported" (INFO; exit status unaffected).

Checks (ids):
  V2.inventory   the inventory itself is self-consistent (label rule `:` -> `_`, counts, anchors)
  V2.syntax      Verso sources parse: directives balanced, only known directive kinds/options, labels present
  V2.modules     chapter modules <-> inventory chapters, titles, imports, `{include}` order in Blueprint.lean
  V2.coverage    (INFO) how much is ported
  V2.counts      node total, per-kind counts, proofs, statement/proof edges
  V2.labels      label bijection (missing / extra / duplicate / misplaced)
  V2.kinds       node kind == TeX environment kind (definition, lemma_, theorem, corollary)
  V2.proofs      a `:::proof` exists exactly for the nodes that have a TeX proof, right after its statement
  V2.edges       statement and proof `uses` edge sets equal the inventory's
  V2.targets     every uses / {uses ..} / {bpref ..} target exists
  V2.groups      `(parent := "grp_..")` on every statement, one group per chapter, consistent
  V2.order       document order of the nodes inside every chapter
  V2.headings    `#` / `##` headings vs inventory sections/subsections
  V2.outline     interleaving of headings and nodes (complete chapters)
  V2.numbers     rendered number == legacy number (appendices shifted by --appendix-offset)
  V2.anchors     the six explicit legacy numbers
  V3.math        per node, ordered maths spans (statement and proof separately, inline vs display)
  V3.macros      (INFO) macros used in maths vs Macros.lean
  V3.imports     chapter modules import Macros and Roles
  V4.counts      per node {term}, {palka} and reference-role counts
  V4.titles      {nodetitle} text and {palka} text
  V4.tex         no leftover TeX commands in the running text
  V4.escapes     no unescaped Verso specials in the running text
  V4.intro       intro paragraphs of Blueprint.lean
  V4.global      total {term} / {palka} counts, section / subsection counts
Checks suffixed `[manifest]` / `[vbp]` run on the generator's view (rendered numbers, kinds, edges, ...).
"""
from __future__ import annotations

import argparse
import bisect
import difflib
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

PASS, FAIL, INFO, SKIP = "PASS", "FAIL", "INFO", "SKIP"

# Verso directive name -> node kind (= TeX environment name)
DIRECTIVE_KIND = {
    "definition": "definition",
    "lemma_": "lemma",
    "theorem": "theorem",
    "corollary": "corollary",
    "proposition": "proposition",
}
ENV_TO_DIRECTIVE = {"definition": "definition", "lemma": "lemma_", "theorem": "theorem", "corollary": "corollary"}
KNOWN_OPTIONS = {"parent", "uses"}
BUILTIN_ROLES = {"bpref", "uses", "include", "blueprint_graph", "blueprint_summary"}
ANCHORS = {  # legacy TeX label -> legacy number (plan section 2 / V2)
    "def:absolute_value": "1.5",
    "lem:linearity_of_complex_integral": "3.2",
    "thm:CAUCHY_FORMULA": "4.18",
    "lem:abel": "5.18",
    "cor:abel_contrapositive": "5.19",
    "cor:ANALYTIC_CONTINUATION": "5.32",
}
CHAPTERS_DIR = "ComplexAnalysisCourse/Chapters"
MACROS_FILE = "ComplexAnalysisCourse/Macros.lean"
ROLES_FILE = "ComplexAnalysisCourse/Roles.lean"
BLUEPRINT_FILE = "ComplexAnalysisCourse/Blueprint.lean"
REQUIRED_IMPORTS = ["ComplexAnalysisCourse.Macros", "ComplexAnalysisCourse.Roles"]

STANDARD_MACROS = set("""
alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa lambda mu nu xi pi varpi rho varrho
sigma varsigma tau upsilon phi varphi chi psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega
sin cos tan cot sec csc sinh cosh tanh coth arcsin arccos arctan log ln exp lim liminf limsup sup inf max min arg
det dim ker deg gcd Pr hom Re Im
in notin ni subset supset subseteq supseteq subsetneq supsetneq cap cup bigcap bigcup setminus emptyset varnothing
ne neq le leq ge geq lt gt ll gg approx sim simeq cong equiv propto to mapsto rightarrow leftarrow Rightarrow
Leftarrow Leftrightarrow leftrightarrow longrightarrow longleftarrow implies iff xrightarrow xleftarrow
hookrightarrow uparrow downarrow
frac dfrac tfrac sqrt left right big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr begin end text textbf textit
textrm mathrm mathbf mathit mathcal mathbb mathfrak mathsf mathtt boldsymbol operatorname hat widehat tilde
widetilde bar overline underline vec dot ddot overset underset stackrel not
infty partial nabla int oint iint iiint sum prod cdot cdots ldots vdots ddots dots times circ bullet pm mp ast star
ell hbar forall exists neg lnot land lor wedge vee angle triangle perp parallel mid nmid colon langle rangle lceil
rceil lfloor rfloor lvert rvert lVert rVert vert Vert quad qquad space hspace vspace displaystyle textstyle
scriptstyle limits nolimits binom choose tag mathop mathbin mathrel phantom boxed underbrace overbrace Large tiny
small mathbbm item label ref
""".split())


# ----------------------------------------------------------------------------------------------------------------------
# small helpers
# ----------------------------------------------------------------------------------------------------------------------

def norm_ws(s: str) -> str:
    """Collapse all whitespace (incl. NBSP and newlines) to single spaces and strip."""
    return re.sub(r"[\s\u00a0]+", " ", s).strip()


def norm_tex(s: str) -> str:
    return norm_ws(s)


def label_rule(label: str) -> str:
    """Decision D4: TeX label -> Verso label."""
    return label.replace(":", "_")


def strip_guillemets(s: str) -> str:
    return s.replace("\u00ab", "").replace("\u00bb", "")


def canon_text(s: str) -> str:
    """Canonical form of running text / titles for comparing TeX-side and Verso-side strings."""
    s = s.replace("\u00a0", " ").replace("~", " ")
    s = re.sub("[\u2018\u2019\u02bc]", "'", s)
    s = s.replace("\u201c", '"').replace("\u201d", '"').replace("``", '"').replace("''", '"')
    s = s.replace("\u2014", "---").replace("\u2013", "--")
    s = s.replace("\u2026", "...").replace("\\ldots", "...")
    s = re.sub(r"\$([^$]*)\$", lambda m: "$" + norm_tex(m.group(1)) + "$", s)
    return norm_ws(s)


def tex_title_text(title_raw: str) -> str:
    """Title text of a TeX node: `[Title \\Palka{..}]` content with the Palka references removed."""
    return canon_text(re.sub(r"\\Palka\{[^{}]*\}", "", title_raw))


def tex_palka_args(title_raw: str) -> List[str]:
    return [norm_ws(a.replace("~", " ")) for a in re.findall(r"\\Palka\{([^{}]*)\}", title_raw)]


def trunc(s: str, n: int = 90) -> str:
    s = s if len(s) <= n else s[: n - 3] + "..."
    return s


def is_subsequence(small: Sequence, big: Sequence) -> Tuple[bool, Optional[int]]:
    """Greedy check; returns (ok, index in `small` of the first element that cannot be matched)."""
    j = 0
    for i, x in enumerate(small):
        while j < len(big) and big[j] != x:
            j += 1
        if j >= len(big):
            return False, i
        j += 1
    return True, None


@dataclass
class Check:
    id: str
    status: str
    summary: str
    details: List[str] = field(default_factory=list)


# ----------------------------------------------------------------------------------------------------------------------
# the inventory (TeX side)
# ----------------------------------------------------------------------------------------------------------------------

class Inventory:
    def __init__(self, data: dict):
        self.data = data
        self.nodes: List[dict] = sorted(data["nodes"], key=lambda n: n["order"])
        self.by_label: Dict[str, dict] = {}
        for n in self.nodes:
            self.by_label.setdefault(n["label_verso"], n)
        self.labels: List[str] = [n["label_verso"] for n in self.nodes]
        self.chapters: List[dict] = data["chapters"]
        self.chapter_numbers = [c["number"] for c in self.chapters]
        self.chapter_by_number = {c["number"]: c for c in self.chapters}
        self.outline: List[dict] = data.get("outline", [])
        self.nodes_of_chapter: Dict[str, List[dict]] = {c: [] for c in self.chapter_numbers}
        for n in self.nodes:
            self.nodes_of_chapter.setdefault(n["chapter"], []).append(n)
        self.intro: Optional[str] = data.get("intro")

    # -- recomputed totals ---------------------------------------------------------------------------------------------
    def totals(self) -> dict:
        by_kind: Dict[str, int] = {}
        for n in self.nodes:
            by_kind[n["env"]] = by_kind.get(n["env"], 0) + 1
        return {
            "nodes": len(self.nodes),
            "by_kind": by_kind,
            "proofs": sum(1 for n in self.nodes if n["has_proof"]),
            "statement_edges": sum(len(set(n["statement_uses"])) for n in self.nodes),
            "proof_edges": sum(len(set(n["proof_uses"])) for n in self.nodes),
            "term": sum(n.get("n_term", 0) for n in self.nodes),
            "palka": sum(n.get("n_palka", 0) for n in self.nodes),
            "sections": sum(1 for o in self.outline if o["type"] == "section"),
            "subsections": sum(1 for o in self.outline if o["type"] == "subsection"),
        }

    def outline_of_chapter(self, ch: str) -> List[dict]:
        return [o for o in self.outline if o.get("chapter") == ch and o["type"] in ("section", "subsection", "node")]

    def chapter_index(self, ch: str) -> int:
        return self.chapter_numbers.index(ch)

    def self_check(self, anchors: Optional[Dict[str, str]] = None) -> List[str]:
        anchors = ANCHORS if anchors is None else anchors
        problems: List[str] = []
        seen: Dict[str, str] = {}
        for n in self.nodes:
            lab, lv = n["label"], n["label_verso"]
            if lv != label_rule(lab):
                problems.append(f"{lab}: label_verso {lv!r} != rule(:->_) {label_rule(lab)!r}")
            if lv in seen and seen[lv] != lab:
                problems.append(f"label rule not injective: {lab!r} and {seen[lv]!r} both give {lv!r}")
            seen[lv] = lab
            if n.get("statement_uses_verso") is not None and n["statement_uses_verso"] != [label_rule(u) for u in n["statement_uses"]]:
                problems.append(f"{lab}: statement_uses_verso inconsistent with statement_uses")
            if n.get("proof_uses_verso") is not None and n["proof_uses_verso"] != [label_rule(u) for u in n["proof_uses"]]:
                problems.append(f"{lab}: proof_uses_verso inconsistent with proof_uses")
            if n["proof_uses"] and not n["has_proof"]:
                problems.append(f"{lab}: proof_uses without has_proof")
            if n["env"] not in ENV_TO_DIRECTIVE:
                problems.append(f"{lab}: unexpected environment kind {n['env']!r}")
            if n["chapter"] not in self.chapter_by_number:
                problems.append(f"{lab}: unknown chapter {n['chapter']!r}")
            for u in list(n["statement_uses"]) + list(n["proof_uses"]):
                if label_rule(u) not in {m["label_verso"] for m in self.nodes}:
                    problems.append(f"{lab}: uses unknown label {u!r}")
        declared = self.data.get("counts", {})
        mine = self.totals()
        for key in ("nodes", "proofs", "statement_edges", "proof_edges", "sections", "subsections", "palka", "term"):
            if key in declared and declared[key] != mine[key]:
                problems.append(f"counts.{key}: header says {declared[key]} but nodes give {mine[key]}")
        if "by_kind" in declared and declared["by_kind"] != mine["by_kind"]:
            problems.append(f"counts.by_kind: header says {declared['by_kind']} but nodes give {mine['by_kind']}")
        for lab, num in anchors.items():
            n = next((m for m in self.nodes if m["label"] == lab), None)
            if n is None:
                problems.append(f"anchor {lab} not in the inventory")
            elif n["number"] != num:
                problems.append(f"anchor {lab}: inventory number {n['number']} != legacy {num}")
        return problems


def render_chapter(chnum: str, offset: int) -> str:
    """Chapter number as rendered by Verso: appendices A, B, ... become chapters 1+offset, 2+offset, ..."""
    if chnum.isdigit():
        return chnum
    if offset == 0:
        return chnum
    return str(ord(chnum.upper()[0]) - ord("A") + 1 + offset)


def expected_number(node: dict, offset: int) -> str:
    ch, _, rest = node["number"].partition(".")
    return f"{render_chapter(ch, offset)}.{rest}"


# ----------------------------------------------------------------------------------------------------------------------
# inline (running text) scanner
# ----------------------------------------------------------------------------------------------------------------------

@dataclass
class Span:
    kind: str  # inline | display
    tex: str
    line: int
    in_title: bool = False


@dataclass
class Role:
    name: str
    args: str
    strings: List[str]
    line: int
    text: str = ""  # content with maths as $..$
    in_title: bool = False

    @property
    def target(self) -> Optional[str]:
        return self.strings[0] if self.strings else None


@dataclass
class Problem:
    cat: str  # tex | escape | syntax
    msg: str
    line: int


@dataclass
class TextInfo:
    spans: List[Span] = field(default_factory=list)
    roles: List[Role] = field(default_factory=list)
    problems: List[Problem] = field(default_factory=list)
    pieces: List[Tuple[str, str]] = field(default_factory=list)

    def roles_named(self, name: str) -> List[Role]:
        return [r for r in self.roles if r.name == name]

    def text(self, math: bool = True) -> str:
        return render_pieces(self.pieces, math)


def render_pieces(pieces: Sequence[Tuple[str, str]], math: bool = True) -> str:
    out = []
    for kind, t in pieces:
        if kind == "math":
            out.append("$" + norm_tex(t) + "$" if math else " ")
        elif kind == "code":
            out.append("`" + t + "`")
        else:
            out.append(t)
    return "".join(out)


_ORD_RE = re.compile(r"[^\\$`{}\[\]*_\n]+")
_ROLE_NAME_RE = re.compile(r"\s*([A-Za-z_][A-Za-z0-9_.']*)")
_BLANK_RE = re.compile(r"[ \t]*(?:\n|$)")
_LINE_OPENER_RE = re.compile(r"[ ]{0,3}(>|#{1,6}[ \t]|%%%)")
_ALPHA_RE = re.compile(r"[A-Za-z]+")


def _close_run_re(ticks: int) -> "re.Pattern[str]":
    return re.compile("(?<!`)" + "`" * ticks + "(?!`)")


_BLANKLINE_RE = re.compile(r"\n[ \t]*\n")


def find_close(s: str, start: int, ticks: int) -> Optional["re.Match[str]"]:
    """Closing backtick run of exactly `ticks` backticks; inline content never crosses a blank line."""
    bl = _BLANKLINE_RE.search(s, start)
    return _close_run_re(ticks).search(s, start, bl.start() if bl else len(s))


class _Scanner:
    def __init__(self, s: str, line0: int):
        self.s = s
        self.n = len(s)
        self.line0 = line0
        self.nl = [i for i, c in enumerate(s) if c == "\n"]
        self.info = TextInfo()

    def line(self, pos: int) -> int:
        return self.line0 + bisect.bisect_left(self.nl, pos)

    def problem(self, cat: str, msg: str, pos: int) -> None:
        self.info.problems.append(Problem(cat, msg, self.line(pos)))

    def at_line_start(self, pos: int) -> bool:
        k = self.s.rfind("\n", 0, pos) + 1
        return self.s[k:pos].strip(" \t") == ""

    def check_line_start(self, pos: int) -> None:
        m = _LINE_OPENER_RE.match(self.s, pos)
        if m:
            self.problem("escape", f"line starts with block opener `{m.group(1).strip()}` inside running text", pos)

    def scan(self, i: int, in_title: bool, in_role: bool) -> Tuple[int, List[Tuple[str, str, int]]]:
        s, n = self.s, self.n
        pieces: List[Tuple[str, str, int]] = []
        delim = {"*": 0, "_": 0}

        def flush_par(pos: int) -> None:
            for d in ("*", "_"):
                if delim[d] % 2:
                    self.problem("escape", f"odd number of unescaped `{d}` in one paragraph (unmatched emphasis delimiter)", pos)
                delim[d] = 0

        if i == 0:
            self.check_line_start(0)
        while i < n:
            c = s[i]
            m = _ORD_RE.match(s, i)
            if m:
                pieces.append(("text", m.group(), i))
                i = m.end()
                continue
            if c == "\n":
                if _BLANK_RE.match(s, i + 1):
                    flush_par(i)
                pieces.append(("text", " ", i))
                i += 1
                self.check_line_start(i)
                continue
            if c == "\\":
                if i + 1 >= n:
                    i += 1
                    continue
                nx = s[i + 1]
                if nx.isalpha():
                    name = _ALPHA_RE.match(s, i + 1).group()
                    self.problem("tex", f"leftover TeX command \\{name}", i)
                    pieces.append(("text", "\\" + name, i))
                    i += 1 + len(name)
                elif nx in " \t\n":
                    self.problem("tex", "stray backslash (TeX control space / line break?)", i)
                    pieces.append(("text", "\\", i))
                    i += 1
                else:
                    pieces.append(("text", nx, i))
                    i += 2
                continue
            if c == "$":
                j = i
                while j < n and s[j] == "$" and j - i < 2:
                    j += 1
                dollars = j - i
                if j < n and s[j] == "`":
                    k = j
                    while k < n and s[k] == "`":
                        k += 1
                    mm = find_close(s, k, k - j)
                    if not mm:
                        self.problem("syntax", "unterminated maths span (no closing backtick run before the end of the paragraph)", i)
                        i = k
                        continue
                    content = s[k:mm.start()]
                    self.info.spans.append(Span("display" if dollars == 2 else "inline", content, self.line(i), in_title))
                    pieces.append(("math", content, i))
                    i = mm.end()
                else:
                    self.problem("tex", "bare `$` not followed by a backtick (TeX-style inline maths left over?)", i)
                    pieces.append(("text", "$" * dollars, i))
                    i = j
                continue
            if c == "`":
                k = i
                while k < n and s[k] == "`":
                    k += 1
                mm = find_close(s, k, k - i)
                if not mm:
                    self.problem("syntax", "unterminated code span / unescaped backtick (TeX quotes?)", i)
                    pieces.append(("text", "`" * (k - i), i))
                    i = k
                    continue
                self.problem("escape", f"code span `{trunc(s[k:mm.start()], 40)}` in running text (TeX quotes / unescaped backtick?)", i)
                pieces.append(("code", s[k:mm.start()], i))
                i = mm.end()
                continue
            if c == "{":
                m2 = _ROLE_NAME_RE.match(s, i + 1)
                if not m2:
                    self.problem("escape", "unescaped `{` (not a role)", i)
                    pieces.append(("text", "{", i))
                    i += 1
                    continue
                name = m2.group(1)
                k = m2.end()
                while k < n and s[k] != "}":
                    if s[k] == '"':
                        k += 1
                        while k < n and s[k] != '"':
                            if s[k] == "\\":
                                k += 1
                            k += 1
                    k += 1
                if k >= n:
                    self.problem("syntax", f"unterminated role {{{name} ...", i)
                    i = n
                    break
                args = s[m2.end():k]
                strings = [x for x in re.findall(r'"((?:[^"\\]|\\.)*)"', args)]
                role = Role(name, args.strip(), strings, self.line(i), in_title=in_title)
                self.info.roles.append(role)
                i = k + 1
                if i < n and s[i] == "[":
                    i, sub = self.scan(i + 1, in_title or name == "nodetitle", True)
                    role.text = render_pieces([(a, b) for a, b, _ in sub])
                    pieces.extend(sub)
                continue
            if c == "}":
                self.problem("escape", "unescaped `}`", i)
                pieces.append(("text", "}", i))
                i += 1
                continue
            if c == "[":
                self.problem("escape", "unescaped `[` in running text", i)
                pieces.append(("text", "[", i))
                i += 1
                continue
            if c == "]":
                if in_role:
                    flush_par(i)
                    return i + 1, pieces
                self.problem("escape", "unescaped `]` in running text", i)
                pieces.append(("text", "]", i))
                i += 1
                continue
            if c == "*" and i + 1 < n and s[i + 1] in " \t" and self.at_line_start(i):
                i += 1  # list marker
                continue
            if c in "*_":
                delim[c] += 1
                i += 1
                continue
            pieces.append(("text", c, i))
            i += 1
        flush_par(n)
        if in_role:
            self.problem("syntax", "unterminated role content `[` ... (no closing `]`)", n)
        return n, pieces


_LEFTOVER_TEXT_RES = [
    (re.compile(r"~"), "TeX tie `~` (should be a no-break space)"),
    (re.compile(r"--"), "TeX dash `--` (should be an en/em dash)"),
    (re.compile(r"''"), "TeX closing quote `''`"),
]


def analyze(text: str, line0: int = 1) -> TextInfo:
    """Scan one chunk of Verso running text (maths spans, roles, leftovers, unescaped specials)."""
    sc = _Scanner(text, line0)
    _, pieces = sc.scan(0, False, False)
    info = sc.info
    info.pieces = [(a, b) for a, b, _ in pieces]
    # leftovers that span plain text runs
    run: List[Tuple[str, int]] = []
    runs: List[Tuple[str, int]] = []
    for kind, t, pos in pieces + [("end", "", 0)]:
        if kind == "text":
            run.append((t, pos))
        else:
            if run:
                runs.append(("".join(x for x, _ in run), run[0][1]))
            run = []
    for rtext, pos in runs:
        for rx, msg in _LEFTOVER_TEXT_RES:
            if rx.search(rtext):
                info.problems.append(Problem("tex", msg + f" in `{trunc(norm_ws(rtext), 50)}`", sc.line(pos)))
    return info


# ----------------------------------------------------------------------------------------------------------------------
# Verso module parser (block structure)
# ----------------------------------------------------------------------------------------------------------------------

@dataclass
class Directive:
    name: str
    label: Optional[str]
    options: Dict[str, str]
    line: int
    end_line: int
    body: str
    info: TextInfo
    problems: List[str] = field(default_factory=list)

    @property
    def uses_option(self) -> List[str]:
        return split_uses(self.options.get("uses", ""))


def split_uses(s: str) -> List[str]:
    return [x for x in re.split(r"[,\s]+", s.strip()) if x]


@dataclass
class Module:
    path: str  # absolute
    rel: str   # relative to root
    title: Optional[str] = None
    title_info: Optional[TextInfo] = None
    imports: List[str] = field(default_factory=list)
    items: List[tuple] = field(default_factory=list)  # ("heading", level, text, line) | ("directive", Directive) | ("prose", TextInfo, line)
    errors: List[str] = field(default_factory=list)

    def directives(self, *names: str) -> List[Directive]:
        return [it[1] for it in self.items if it[0] == "directive" and (not names or it[1].name in names)]

    def statements(self) -> List[Directive]:
        return [d for d in self.directives() if d.name in DIRECTIVE_KIND]

    def headings(self) -> List[tuple]:
        return [it for it in self.items if it[0] == "heading"]

    @property
    def name(self) -> str:
        return os.path.splitext(os.path.basename(self.path))[0]

    def all_infos(self) -> List[Tuple[str, TextInfo, int]]:
        """(where, info, line) for every analysed text chunk of the module."""
        out = []
        for it in self.items:
            if it[0] == "directive":
                d = it[1]
                out.append((f"{d.name} {d.label or ''}".strip(), d.info, d.line))
            elif it[0] == "prose":
                out.append(("prose", it[1], it[2]))
            elif it[0] == "heading":
                out.append((f"heading {it[2]!r}", it[4], it[3]))
        return out


_DOC_RE = re.compile(r'^#doc\s*\(\s*[\w.]+\s*\)\s*"((?:[^"\\]|\\.)*)"\s*=>\s*$')
_IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+)?import\s+([\w.]+)")
_FENCE_OPEN_RE = re.compile(r"^(:{3,})\s*([A-Za-z_][\w']*)\s*(.*)$")
_FENCE_CLOSE_RE = re.compile(r"^(:{3,})\s*$")
_HEADING_RE = re.compile(r"^(#{1,6})[ \t]+(.*?)\s*$")


def masked_newlines(body: str) -> Tuple[set, List[Tuple[int, str]]]:
    """Offsets of newline characters lying inside maths / code spans, plus (offset, message) syntax errors."""
    res: set = set()
    errs: List[Tuple[int, str]] = []
    i, n = 0, len(body)
    while i < n:
        c = body[i]
        if c == "\\":
            i += 2
            continue
        if c in "$`":
            j = i
            if c == "$":
                while j < n and body[j] == "$" and j - i < 2:
                    j += 1
            if j < n and body[j] == "`":
                k = j
                while k < n and body[k] == "`":
                    k += 1
                m = find_close(body, k, k - j)
                if m:
                    end = m.end()
                else:
                    eol = body.find("\n", k)  # keep the damage local: an unterminated span is masked to the end of its line
                    end = n if eol < 0 else eol
                    errs.append((i, "unterminated maths / code span (no closing backtick run before the end of the paragraph)"))
                for p in range(i, end):
                    if body[p] == "\n":
                        res.add(p)
                i = end
                continue
        i += 1
    return res, errs


def parse_args_string(rest: str) -> Tuple[List[str], Dict[str, str], List[str]]:
    """Parse the argument part of a directive header: positional strings and `(key := "value")` options."""
    positional: List[str] = []
    options: Dict[str, str] = {}
    problems: List[str] = []
    i, n = 0, len(rest)
    opt_re = re.compile(r'\(\s*([A-Za-z_][\w.]*)\s*:=\s*("(?:[^"\\]|\\.)*"|[^)]*?)\s*\)')
    str_re = re.compile(r'"((?:[^"\\]|\\.)*)"')
    while i < n:
        if rest[i].isspace():
            i += 1
            continue
        m = opt_re.match(rest, i)
        if m:
            val = m.group(2)
            if val.startswith('"') and val.endswith('"') and len(val) >= 2:
                val = val[1:-1]
            else:
                problems.append(f"option {m.group(1)} has a non-string value {val!r}")
            if m.group(1) in options:
                problems.append(f"option {m.group(1)} given twice")
            options[m.group(1)] = val
            i = m.end()
            continue
        m = str_re.match(rest, i)
        if m:
            positional.append(m.group(1))
            i = m.end()
            continue
        m = re.compile(r"\S+").match(rest, i)
        problems.append(f"cannot parse directive argument `{m.group()}`")
        i = m.end()
    return positional, options, problems


def _balanced(s: str) -> bool:
    depth, in_str, i = 0, False, 0
    while i < len(s):
        c = s[i]
        if in_str:
            if c == "\\":
                i += 1
            elif c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        i += 1
    return depth <= 0 and not in_str


def parse_module(path: str, rel: str, text: str) -> Module:
    text = text.replace("\r\n", "\n")
    mod = Module(path=path, rel=rel)
    lines = text.split("\n")
    doc_idx = None
    for idx, l in enumerate(lines):
        m = _IMPORT_RE.match(l)
        if m:
            mod.imports.append(m.group(1))
        m = _DOC_RE.match(l)
        if m:
            mod.title = re.sub(r"\\(.)", r"\1", m.group(1))
            mod.title_info = analyze(mod.title, idx + 1)
            doc_idx = idx
            break
    if doc_idx is None:
        mod.errors.append("no `#doc (..) \"Title\" =>` header found")
        return mod
    body_lines = lines[doc_idx + 1:]
    line0 = doc_idx + 2  # 1-based line number of body_lines[0]
    body = "\n".join(body_lines)
    masked, merrs = masked_newlines(body)
    offs = []
    pos = 0
    for l in body_lines:
        offs.append(pos)
        pos += len(l) + 1
    for off, msg in merrs:
        mod.errors.append(f"{rel}:{line0 + body[:off].count(chr(10))}: {msg}")

    def inside(li: int) -> bool:
        return li > 0 and (offs[li] - 1) in masked

    stack: List[dict] = []
    prose_buf: List[Tuple[int, str]] = []
    in_meta = False

    def flush_prose() -> None:
        nonlocal prose_buf
        if prose_buf and any(t.strip() for _, t in prose_buf):
            first = prose_buf[0][0]
            mod.items.append(("prose", analyze("\n".join(t for _, t in prose_buf), first), first))
        prose_buf = []

    li = 0
    nlines = len(body_lines)
    while li < nlines:
        l = body_lines[li]
        lineno = line0 + li
        if inside(li):
            (stack[-1]["body"] if stack else prose_buf).append((lineno, l))
            li += 1
            continue
        if in_meta:
            if l.strip() == "%%%":
                in_meta = False
            li += 1
            continue
        if not stack and l.strip() == "%%%":
            flush_prose()
            in_meta = True
            li += 1
            continue
        if not stack and l.strip().startswith("%%%") and l.strip().endswith("%%%") and len(l.strip()) > 6:
            li += 1
            continue
        m = _FENCE_CLOSE_RE.match(l)
        if m:
            colons = len(m.group(1))
            if stack and stack[-1]["colons"] == colons:
                top = stack.pop()
                bodytxt = "\n".join(t for _, t in top["body"])
                body_line0 = top["body"][0][0] if top["body"] else top["line"] + 1
                d = Directive(top["name"], top["label"], top["options"], top["line"], lineno - 1, bodytxt,
                              analyze(bodytxt, body_line0), top["problems"])
                if stack:
                    stack[-1]["body"].append((top["line"], f":::{top['name']} ..."))  # nested directive (unexpected)
                    mod.errors.append(f"{rel}:{top['line']}: nested directive `{top['name']}` inside `{stack[-1]['name']}`")
                else:
                    mod.items.append(("directive", d))
            else:
                mod.errors.append(f"{rel}:{lineno}: `{m.group(1)}` closes no open directive of the same colon count")
            li += 1
            continue
        m = _FENCE_OPEN_RE.match(l)
        if m:
            colons, name, rest = len(m.group(1)), m.group(2), m.group(3)
            start = lineno
            while not _balanced(rest) and li + 1 < nlines:
                li += 1
                rest += " " + body_lines[li].strip()
            positional, options, problems = parse_args_string(rest)
            label = positional[0] if positional else None
            if len(positional) > 1:
                problems.append(f"unexpected extra positional arguments {positional[1:]}")
            if not stack:
                flush_prose()
            stack.append({"colons": colons, "name": name, "label": label, "options": options, "line": start,
                          "problems": problems, "body": []})
            li += 1
            continue
        if stack:
            stack[-1]["body"].append((lineno, l))
            li += 1
            continue
        m = _HEADING_RE.match(l)
        if m:
            flush_prose()
            mod.items.append(("heading", len(m.group(1)), m.group(2), lineno, analyze(m.group(2), lineno)))
            li += 1
            continue
        prose_buf.append((lineno, l))
        li += 1
    flush_prose()
    for top in stack:
        mod.errors.append(f"{rel}:{top['line']}: directive `{top['name']}` is never closed")
    return mod


def parse_includes(text: str) -> List[Tuple[int, str, int]]:
    out = []
    for i, l in enumerate(text.replace("\r\n", "\n").split("\n")):
        m = re.match(r"^\s*\{include\s+(\d+)\s+([\w.]+)\s*\}", l)
        if m:
            out.append((int(m.group(1)), m.group(2), i + 1))
    return out


def parse_macros(text: str) -> set:
    names: set = set()
    for chunk in re.findall(r'r#+"(.*?)"#+', text, flags=re.S):
        names |= set(re.findall(r"\\(?:newcommand|renewcommand|providecommand)\*?\s*\{?\s*\\([A-Za-z]+)", chunk))
        names |= set(re.findall(r"\\(?:def|let|gdef|edef)\s*\\([A-Za-z]+)", chunk))
        names |= set(re.findall(r"\\DeclareMathOperator\*?\s*\{\s*\\([A-Za-z]+)", chunk))
    return names


def macros_in(tex: str) -> set:
    return {m.group(1) for m in re.finditer(r"\\\\|\\([A-Za-z]+)", tex) if m.group(1)}


def parse_role_defs(text: str) -> set:
    return set(re.findall(r"@\[role[^\]]*\]\s*(?:private\s+)?def\s+([A-Za-z_][\w']*)", text))


# ----------------------------------------------------------------------------------------------------------------------
# views: what the Verso side (source, manifest, vbp) says about the nodes
# ----------------------------------------------------------------------------------------------------------------------

@dataclass
class NodeV:
    label: str
    kind: str
    parent: Optional[str]
    stmt_uses: List[str]
    proof_uses: List[str]
    has_proof: bool
    number: Optional[str]
    chapter: Optional[str]  # inventory chapter number of the module the node sits in (source view)
    where: str = ""
    path: str = ""
    line: int = 0


@dataclass
class View:
    name: str  # source | manifest | vbp
    nodes: Dict[str, NodeV] = field(default_factory=dict)
    seq: List[str] = field(default_factory=list)       # labels in encounter order (with duplicates)
    dups: Dict[str, List[str]] = field(default_factory=dict)
    has_edges: bool = True
    has_numbers: bool = True
    has_proofs: bool = True
    has_parents: bool = True
    notes: List[str] = field(default_factory=list)

    def add(self, nv: NodeV) -> None:
        self.seq.append(nv.label)
        if nv.label in self.nodes:
            self.dups.setdefault(nv.label, [self.nodes[nv.label].where]).append(nv.where)
        else:
            self.nodes[nv.label] = nv

    @property
    def suffix(self) -> str:
        return "" if self.name == "source" else f"[{self.name}]"


class VersoSource:
    def __init__(self, root: str, chapters_dir: str, macros_file: str = MACROS_FILE, roles_file: str = ROLES_FILE,
                 blueprint_file: str = BLUEPRINT_FILE):
        self.root = root
        self.macros_file, self.roles_file, self.blueprint_file = macros_file, roles_file, blueprint_file
        self.modules: List[Module] = []
        d = os.path.join(root, chapters_dir)
        self.dir_exists = os.path.isdir(d)
        skip = os.path.normpath(os.path.join(root, blueprint_file))
        if self.dir_exists:
            for fn in sorted(os.listdir(d)):
                p = os.path.join(d, fn)
                if fn.endswith(".lean") and os.path.normpath(p) != skip:
                    with open(p, encoding="utf-8") as fh:
                        self.modules.append(parse_module(p, os.path.relpath(p, root), fh.read()))
        self.macros_text = self._read(macros_file)
        self.roles_text = self._read(roles_file)
        self.blueprint_text = self._read(blueprint_file)
        self.macros_defined: Optional[set] = parse_macros(self.macros_text) if self.macros_text is not None else None
        self.roles_defined: Optional[set] = parse_role_defs(self.roles_text) if self.roles_text is not None else None

    def _read(self, rel: str) -> Optional[str]:
        p = os.path.join(self.root, rel)
        if not os.path.isfile(p):
            return None
        with open(p, encoding="utf-8") as fh:
            return fh.read()


def chapter_title_variants(title: str) -> set:
    return {canon_text(title)}


def match_chapter_by_title(inv: Inventory, title: Optional[str]) -> Optional[str]:
    if title is None:
        return None
    t = canon_text(title)
    stripped = re.sub(r"^appendix(?:\s+[A-Za-z0-9]+)?\s*[:.\u2013\u2014-]+\s*", "", t, flags=re.I)
    for c in inv.chapters:
        ct = canon_text(c["title"])
        if t == ct or stripped == ct:
            return c["number"]
    return None


def map_modules(inv: Inventory, modules: List[Module]) -> Tuple[Dict[str, str], List[str]]:
    """module.rel -> chapter number; plus problems."""
    mapping: Dict[str, str] = {}
    problems: List[str] = []
    for m in modules:
        ch = match_chapter_by_title(inv, m.title)
        if ch is None:
            votes: Dict[str, int] = {}
            for d in m.statements():
                n = inv.by_label.get(d.label or "")
                if n:
                    votes[n["chapter"]] = votes.get(n["chapter"], 0) + 1
            if votes:
                ch = max(votes, key=lambda k: votes[k])
                problems.append(f"{m.rel}: title {m.title!r} matches no chapter title; assigned to chapter {ch} by its labels")
            else:
                problems.append(f"{m.rel}: title {m.title!r} matches no chapter title and no known labels")
                continue
        mapping[m.rel] = ch
    by_ch: Dict[str, List[str]] = {}
    for rel, ch in mapping.items():
        by_ch.setdefault(ch, []).append(rel)
    for ch, rels in by_ch.items():
        if len(rels) > 1:
            problems.append(f"chapter {ch} is claimed by several modules: {rels}")
    return mapping, problems


def chapter_include_positions(src: VersoSource) -> Dict[str, int]:
    """module path (relative to root, '/'-separated) -> 1-based chapter position given by the `{include}` order in
    Blueprint.lean: this is the chapter number Verso renders (top-level parts are numbered in include order)."""
    pos: Dict[str, int] = {}
    if src.blueprint_text is None:
        return pos
    have = {m.rel.replace(os.sep, "/") for m in src.modules}
    for _, modname, _ in parse_includes(src.blueprint_text):
        p = modname.replace(".", "/") + ".lean"
        if p in have and p not in pos:
            pos[p] = len(pos) + 1
    return pos


def build_source_view(inv: Inventory, src: VersoSource, mapping: Dict[str, str], offset: int) -> View:
    view = View("source")
    include_pos = chapter_include_positions(src)
    for m in src.modules:
        ch = mapping.get(m.rel)
        ip = include_pos.get(m.rel.replace(os.sep, "/"))
        # rendered chapter number = position in Blueprint.lean's includes; fall back to the expected one if not included
        prefix = str(ip) if ip is not None else (render_chapter(ch, offset) if ch else None)
        counter = 0
        proofs: Dict[str, Directive] = {}
        for d in m.directives("proof"):
            if d.label is not None:
                proofs.setdefault(d.label, d)
        for d in m.statements():
            counter += 1
            label = d.label or f"<unlabelled@{m.rel}:{d.line}>"
            stmt_uses = list(dict.fromkeys(d.uses_option + [r.target for r in d.info.roles_named("uses") if r.target]))
            pr = proofs.get(label)
            proof_uses = []
            if pr is not None:
                proof_uses = list(dict.fromkeys(pr.uses_option + [r.target for r in pr.info.roles_named("uses") if r.target]))
            view.add(NodeV(
                label=label, kind=DIRECTIVE_KIND[d.name], parent=d.options.get("parent"),
                stmt_uses=stmt_uses, proof_uses=proof_uses, has_proof=pr is not None,
                number=f"{prefix}.{counter}" if prefix else None, chapter=ch,
                where=f"{m.rel}:{d.line}", path=m.rel, line=d.line))
    return view


def _first_loc(p: dict) -> Tuple[str, int]:
    loc = (p.get("sourceLocation") or {}).get("location") or {}
    start = (loc.get("range") or {}).get("start") or {}
    return loc.get("path") or "", int(start.get("line", -1)) + 1 if start else 0


def view_from_manifest(manifest: dict) -> View:
    view = View("manifest")
    previews = manifest.get("previews", [])
    proof_entries: Dict[str, dict] = {}
    for p in previews:
        if p.get("facet") == "proof":
            proof_entries[p.get("authoredLabel") or strip_guillemets(p.get("label", ""))] = p
    for p in previews:
        if p.get("facet") != "statement":
            continue
        if p.get("targetKind") not in (None, "block", "externalMarkup"):
            continue
        label = p.get("authoredLabel") or strip_guillemets(p.get("label", ""))
        pr = proof_entries.get(label)
        proof_uses = [strip_guillemets(u["label"]) for u in ((pr or p).get("proofUses") or [])]
        path, line = _first_loc(p)
        view.add(NodeV(
            label=label, kind=str(p.get("kind", "?")).lower(), parent=p.get("parent"),
            stmt_uses=list(dict.fromkeys(strip_guillemets(u["label"]) for u in (p.get("statementUses") or []))),
            proof_uses=list(dict.fromkeys(proof_uses)), has_proof=pr is not None,
            number=p.get("displayLabel"), chapter=None, where=f"manifest:{p.get('key', label)}", path=path, line=line))
    return view


def view_from_node_json(label_rows: List[dict], node_json: Dict[str, dict]) -> View:
    """View from `vbp query labels` (+ optional `vbp query node <label>` documents)."""
    view = View("vbp")
    detailed = bool(node_json)
    view.has_edges = view.has_numbers = view.has_proofs = detailed
    for row in label_rows:
        label = row.get("authoredLabel") or strip_guillemets(row.get("label", ""))
        nj = node_json.get(label)
        if nj is None:
            view.add(NodeV(label, str(row.get("kind", "?")).lower(), row.get("parent"), [], [], False, None, None,
                           where=f"vbp:{label}"))
            continue
        view.add(NodeV(
            label=label, kind=str(nj.get("kind", "?")).lower(), parent=nj.get("parent"),
            stmt_uses=list(dict.fromkeys(strip_guillemets(u["label"]) for u in nj.get("statementUses", []))),
            proof_uses=list(dict.fromkeys(strip_guillemets(u["label"]) for u in nj.get("proofUses", []))),
            has_proof=nj.get("proof") is not None, number=nj.get("displayLabel"), chapter=None, where=f"vbp:{label}"))
    return view


# ----------------------------------------------------------------------------------------------------------------------
# running `lake exe vbp query`
# ----------------------------------------------------------------------------------------------------------------------

def parse_json_stdout(out: str) -> dict:
    """Parse JSON from stdout only; tolerate stray non-JSON lines before the document."""
    out = out.strip()
    try:
        return json.loads(out)
    except ValueError:
        pass
    dec = json.JSONDecoder()
    for m in re.finditer(r"^\{", out, flags=re.M):
        try:
            obj, _ = dec.raw_decode(out[m.start():])
            return obj
        except ValueError:
            continue
    raise ValueError("no JSON object found on stdout")


def vbp_query(cmd: str, root: str, site: Optional[str], args: List[str], timeout: float) -> dict:
    argv = shlex.split(cmd) + ["query"] + (["--site", site] if site else []) + args
    p = subprocess.run(argv, cwd=root, capture_output=True, text=True, timeout=timeout)  # stderr deliberately ignored
    if p.returncode != 0:
        raise RuntimeError(f"`{' '.join(argv)}` exited with {p.returncode}: {trunc(p.stderr.strip(), 300)}")
    return parse_json_stdout(p.stdout)


# ----------------------------------------------------------------------------------------------------------------------
# the checks
# ----------------------------------------------------------------------------------------------------------------------

class Ctx:
    def __init__(self, inv: Inventory, src: Optional[VersoSource], opts: argparse.Namespace):
        self.inv = inv
        self.src = src
        self.opts = opts
        self.partial: bool = opts.partial
        self.offset: int = opts.appendix_offset
        self.results: List[Check] = []
        self.mapping: Dict[str, str] = {}
        self.map_problems: List[str] = []
        self.views: List[View] = []
        self.root: str = opts.root
        self.anchors: Dict[str, str] = ANCHORS if opts.anchors == "legacy" else {}

    # -- result helpers ------------------------------------------------------------------------------------------------
    def add(self, id_: str, ok: Optional[bool], summary: str, details: Optional[List[str]] = None,
            status: Optional[str] = None) -> Check:
        st = status or (PASS if ok else FAIL)
        c = Check(id_, st, summary, details or [])
        self.results.append(c)
        return c

    def info(self, id_: str, summary: str, details: Optional[List[str]] = None) -> Check:
        return self.add(id_, None, summary, details, status=INFO)

    def skip(self, id_: str, why: str) -> Check:
        return self.add(id_, None, why, None, status=SKIP)

    def verdict(self, id_: str, problems: List[str], ok_summary: str, fail_summary: Optional[str] = None) -> Check:
        if problems:
            return self.add(id_, False, fail_summary or f"{len(problems)} problem(s)", problems)
        return self.add(id_, True, ok_summary)

    # -- helpers -------------------------------------------------------------------------------------------------------
    def present(self, view: View, label: str) -> bool:
        return label in view.nodes

    def missing_labels(self, view: View) -> List[str]:
        return [l for l in self.inv.labels if l not in view.nodes]

    def complete_chapters(self, view: View) -> set:
        return {ch for ch, ns in self.inv.nodes_of_chapter.items() if ns and all(n["label_verso"] in view.nodes for n in ns)}

    def number_verifiable(self, view: View, n: dict) -> bool:
        if not self.partial:
            return True
        ch = n["chapter"]
        for m in self.inv.nodes_of_chapter[ch]:
            if m is n:
                break
            if m["label_verso"] not in view.nodes:
                return False
        for c in self.inv.chapter_numbers:
            if c == ch:
                break
            if not any(m["label_verso"] in view.nodes for m in self.inv.nodes_of_chapter[c]):
                return False
        return True

    def cap(self, lines: List[str]) -> List[str]:
        k = self.opts.max_diffs
        if k and len(lines) > k:
            return lines[:k] + [f"... and {len(lines) - k} more (use --max-diffs 0 for all)"]
        return lines


def where_of(ctx: Ctx, view: View, label: str) -> str:
    nv = view.nodes.get(label)
    return nv.where if nv else "?"


# ---- inventory / structure -------------------------------------------------------------------------------------------

def check_inventory(ctx: Ctx) -> None:
    probs = ctx.inv.self_check(ctx.anchors)
    t = ctx.inv.totals()
    ctx.verdict("V2.inventory", ctx.cap(probs),
                f"inventory self-consistent: {t['nodes']} nodes "
                f"({'/'.join(str(t['by_kind'].get(k, 0)) for k in ('definition', 'lemma', 'theorem', 'corollary'))} "
                f"def/lem/thm/cor), {t['proofs']} proofs, {t['statement_edges']} statement + {t['proof_edges']} proof edges, "
                f"{len(ctx.inv.chapters)} chapters",
                "the inventory is not self-consistent (checker input is unreliable)")


def check_syntax(ctx: Ctx) -> None:
    src = ctx.src
    problems: List[str] = []
    for m in src.modules:
        problems.extend(m.errors)
        for it in m.items:
            if it[0] == "heading":
                if it[1] > 2:
                    problems.append(f"{m.rel}:{it[3]}: heading level {it[1]} (`{'#' * it[1]}`) is not in the plan (only `#`, `##`)")
                continue
            if it[0] != "directive":
                continue
            d: Directive = it[1]
            where = f"{m.rel}:{d.line}"
            if d.name in DIRECTIVE_KIND or d.name == "proof":
                if d.label is None:
                    problems.append(f"{where}: `:::{d.name}` without a label argument")
                elif ":" in d.label:
                    problems.append(f"{where}: label {d.label!r} contains `:` (decision D4: `:` -> `_`)")
                for k in d.options:
                    if k not in KNOWN_OPTIONS and k not in ctx.opts.allow_option:
                        problems.append(f"{where}: unexpected option `({k} := ..)` on `:::{d.name}` (the plan uses only parent, uses)")
                if d.name == "proof" and "parent" in d.options:
                    problems.append(f"{where}: `(parent := ..)` on a proof")
                problems.extend(f"{where}: {pb}" for pb in d.problems)
            elif d.name == "group":
                if d.label is None:
                    problems.append(f"{where}: `:::group` without an id")
                problems.extend(f"{where}: {pb}" for pb in d.problems)
            else:
                problems.append(f"{where}: unknown directive `:::{d.name}` (expected definition, lemma_, theorem, corollary, proof or group)")
        chunks = list(m.all_infos()) + ([("#doc title", m.title_info, 1)] if m.title_info is not None else [])
        for where_, info, _ in chunks:
            problems.extend(f"{m.rel}:{pb.line} ({where_}): {pb.msg}" for pb in info.problems if pb.cat == "syntax")
    ctx.verdict("V2.syntax", ctx.cap(problems),
                f"{len(src.modules)} chapter module(s) parse cleanly (directives balanced, known kinds/options, labels present)",
                f"{len(problems)} markup/syntax problem(s)")


def check_modules(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    problems: List[str] = []
    infos: List[str] = []
    if not src.dir_exists:
        (infos if ctx.partial else problems).append(f"chapters directory {CHAPTERS_DIR} does not exist")
    mapping, mp = ctx.mapping, ctx.map_problems
    problems.extend(mp)
    mapped = set(mapping.values())
    for c in inv.chapters:
        if c["number"] not in mapped:
            (infos if ctx.partial else problems).append(
                f"chapter {c['number']} ({c['title']!r}): no chapter module" + (" (not yet ported)" if ctx.partial else ""))
    # includes in the top-level document
    bp = src.blueprint_text
    bpf = src.blueprint_file
    if bp is None:
        (infos if ctx.partial else problems).append(f"{bpf} not found")
    else:
        incs = parse_includes(bp)
        by_path = {m.rel.replace(os.sep, "/"): m for m in src.modules}
        seen: Dict[str, int] = {}
        order: List[Tuple[int, str]] = []
        for level, modname, line in incs:
            p = modname.replace(".", "/") + ".lean"
            if p not in by_path:
                if os.path.isfile(os.path.join(src.root, p)):
                    infos.append(f"{bpf}:{line}: include of module {modname}, which is not a chapter module")
                else:
                    problems.append(f"{bpf}:{line}: included module {modname} has no file {p}")
                continue
            if level != 0:
                infos.append(f"{bpf}:{line}: `{{include {level} {modname}}}` is nested (plan: level 0)")
            if p in seen:
                problems.append(f"{bpf}:{line}: module {modname} included twice (first at line {seen[p]})")
                continue
            seen[p] = line
            ch = mapping.get(by_path[p].rel)
            if ch is not None:
                order.append((inv.chapter_index(ch), modname))
        idxs = [i for i, _ in order]
        if idxs != sorted(idxs):
            exp = [mn for _, mn in sorted(order)]
            problems.append(f"{bpf}: chapter modules are not included in chapter order: "
                            f"got {[mn.rsplit('.', 1)[-1] for _, mn in order]}, expected {[mn.rsplit('.', 1)[-1] for mn in exp]}")
        for m in src.modules:
            p = m.rel.replace(os.sep, "/")
            if p not in seen:
                (infos if ctx.partial else problems).append(f"{m.rel}: not included in {bpf} (no `{{include 0 ..}}`)")
    for m in src.modules:
        ch = mapping.get(m.rel)
        if ch is not None and m.title is not None:
            exp = canon_text(inv.chapter_by_number[ch]["title"])
            t = canon_text(m.title)
            stripped = re.sub(r"^appendix(?:\s+[A-Za-z0-9]+)?\s*[:.\u2013\u2014-]+\s*", "", t, flags=re.I)
            if t != exp and stripped != exp:
                problems.append(f"{m.rel}: chapter title {m.title!r}, expected {inv.chapter_by_number[ch]['title']!r}")
            elif t != exp and not inv.chapter_by_number[ch].get("appendix"):
                problems.append(f"{m.rel}: chapter title {m.title!r} has an unexpected `Appendix` prefix")
    c = ctx.verdict("V2.modules", ctx.cap(problems),
                    f"{len(src.modules)} chapter module(s) map to chapters {sorted(set(mapping.values()), key=inv.chapter_index)}; "
                    f"titles and `{{include}}` order OK",
                    f"{len(problems)} problem(s) with chapter modules")
    if infos and c.status == PASS:
        c.details = ctx.cap(infos)
    elif infos:
        c.details += ctx.cap(infos)


def check_imports(ctx: Ctx) -> None:
    problems = []
    for m in ctx.src.modules:
        for req in REQUIRED_IMPORTS:
            if req not in m.imports:
                problems.append(f"{m.rel}: missing `import {req}`")
    ctx.verdict("V3.imports", problems, f"all {len(ctx.src.modules)} chapter module(s) import {' and '.join(REQUIRED_IMPORTS)}",
                f"{len(problems)} missing import(s)")


def check_coverage(ctx: Ctx, view: View) -> None:
    inv = ctx.inv
    present = [l for l in inv.labels if l in view.nodes]
    lines = []
    for c in inv.chapters:
        ns = inv.nodes_of_chapter[c["number"]]
        k = sum(1 for n in ns if n["label_verso"] in view.nodes)
        lines.append(f"chapter {c['number']:>2} {c['title']}: {k}/{len(ns)} nodes")
    miss = ctx.missing_labels(view)
    if miss:
        lines.append(f"not yet ported: {len(miss)} node(s), first: {', '.join(miss[:6])}{' ...' if len(miss) > 6 else ''}")
    ctx.info("V2.coverage" + view.suffix, f"{len(present)} of {len(inv.labels)} nodes present on the Verso side"
             + (" (--partial: the rest is reported as not yet ported)" if ctx.partial else ""), lines)


# ---- node-level comparisons, run once per view ---------------------------------------------------------------------

def counts_of(view: View) -> dict:
    by_kind: Dict[str, int] = {}
    for nv in view.nodes.values():
        by_kind[nv.kind] = by_kind.get(nv.kind, 0) + 1
    return {
        "nodes": len(view.nodes), "by_kind": by_kind,
        "proofs": sum(1 for nv in view.nodes.values() if nv.has_proof),
        "statement_edges": sum(len(set(nv.stmt_uses)) for nv in view.nodes.values()),
        "proof_edges": sum(len(set(nv.proof_uses)) for nv in view.nodes.values()),
    }


def check_counts(ctx: Ctx, view: View, stats: Optional[dict] = None) -> None:
    inv = ctx.inv.totals()
    act = counts_of(view)
    id_ = "V2.counts" + view.suffix
    keys = ["nodes", "by_kind"] + (["proofs"] if view.has_proofs else []) + (["statement_edges", "proof_edges"] if view.has_edges else [])
    if ctx.partial:
        ctx.info(id_, f"(--partial) {act['nodes']}/{inv['nodes']} nodes, " + ", ".join(
            f"{k}: {act['by_kind'].get(k, 0)}/{inv['by_kind'].get(k, 0)}" for k in ("definition", "lemma", "theorem", "corollary"))
            + (f", {act['proofs']}/{inv['proofs']} proofs" if view.has_proofs else "")
            + (f", {act['statement_edges']}/{inv['statement_edges']} statement edges, {act['proof_edges']}/{inv['proof_edges']} proof edges"
               if view.has_edges else ""))
        return
    problems = []
    for k in keys:
        if k == "by_kind":
            for kind in sorted(set(inv["by_kind"]) | set(act["by_kind"])):
                e, a = inv["by_kind"].get(kind, 0), act["by_kind"].get(kind, 0)
                if e != a:
                    problems.append(f"nodes of kind {kind}: expected {e}, actual {a}")
        elif inv[k] != act[k]:
            problems.append(f"{k}: expected {inv[k]}, actual {act[k]}")
    ctx.verdict(id_, problems,
                f"{act['nodes']} nodes (" + "/".join(str(act['by_kind'].get(k, 0)) for k in ("definition", "lemma", "theorem", "corollary"))
                + " def/lem/thm/cor)"
                + (f", {act['proofs']} proofs" if view.has_proofs else "")
                + (f", {act['statement_edges']} statement + {act['proof_edges']} proof edges" if view.has_edges else "")
                + " as in the inventory",
                "node/proof/edge totals differ from the inventory")


def check_labels(ctx: Ctx, view: View) -> None:
    inv = ctx.inv
    id_ = "V2.labels" + view.suffix
    problems = []
    extra = [l for l in view.nodes if l not in inv.by_label]
    missing = ctx.missing_labels(view)
    universe = set(inv.labels)
    for l in extra:
        hint = ""
        if label_rule(l) in universe and l != label_rule(l):
            hint = f" (hint: `:` not replaced by `_`; expected {label_rule(l)})"
        else:
            low = {u.lower(): u for u in universe}
            if l.lower() in low:
                hint = f" (hint: differs from {low[l.lower()]} only in case)"
        problems.append(f"extra node (not in the inventory): {l} at {where_of(ctx, view, l)}{hint}")
    if not ctx.partial:
        for l in missing:
            n = inv.by_label[l]
            problems.append(f"missing node: {l} (TeX {n['env']} {n['label']}, chapter {n['chapter']}, {n['file']}:{n['line']})")
    for l, wh in view.dups.items():
        problems.append(f"duplicate node label {l}: defined at {', '.join(wh)}")
    # misplaced in the wrong chapter module (source view only)
    if view.name == "source":
        for l, nv in view.nodes.items():
            n = inv.by_label.get(l)
            if n and nv.chapter and nv.chapter != n["chapter"]:
                problems.append(f"misplaced node {l}: in the module of chapter {nv.chapter} ({nv.where}) but TeX has it in chapter {n['chapter']}")
    total = len(inv.labels)
    summary_ok = (f"label bijection holds ({len(view.nodes)} labels = inventory under `:` -> `_`)" if not ctx.partial
                  else f"all {len(view.nodes)} present label(s) exist in the inventory, no duplicates ({len(missing)} not yet ported)")
    ctx.verdict(id_, ctx.cap(problems), summary_ok,
                f"{len(problems)} label problem(s): {len(extra)} extra, {0 if ctx.partial else len(missing)} missing, {len(view.dups)} duplicate")


def check_kinds(ctx: Ctx, view: View) -> None:
    problems = []
    for l, nv in view.nodes.items():
        n = ctx.inv.by_label.get(l)
        if n and nv.kind != n["env"]:
            problems.append(f"{l}: expected kind {n['env']} (`:::{ENV_TO_DIRECTIVE[n['env']]}`), actual {nv.kind} at {nv.where}")
    ctx.verdict("V2.kinds" + view.suffix, ctx.cap(problems), f"node kind == TeX environment kind for all {len(view.nodes)} present node(s)",
                f"{len(problems)} node(s) with the wrong kind")


def check_proofs(ctx: Ctx, view: View) -> None:
    if not view.has_proofs:
        ctx.skip("V2.proofs" + view.suffix, "needs `node` data (use --vbp-nodes) or a manifest")
        return
    problems = []
    for l, nv in view.nodes.items():
        n = ctx.inv.by_label.get(l)
        if not n:
            continue
        if n["has_proof"] and not nv.has_proof:
            problems.append(f"{l}: TeX has a proof but there is no `:::proof \"{l}\"` ({nv.where})")
        if not n["has_proof"] and nv.has_proof:
            problems.append(f"{l}: TeX has no proof but the Verso side has one ({nv.where})")
    if view.name == "source" and ctx.src is not None:
        for m in ctx.src.modules:
            stmt_pos: Dict[str, int] = {}
            order_stmt: List[str] = []
            seen_proofs: Dict[str, int] = {}
            last_stmt: Optional[str] = None
            for it in m.items:
                if it[0] != "directive":
                    continue
                d = it[1]
                if d.name in DIRECTIVE_KIND and d.label:
                    stmt_pos[d.label] = len(order_stmt)
                    order_stmt.append(d.label)
                    last_stmt = d.label
                elif d.name == "proof" and d.label:
                    if d.label in seen_proofs:
                        problems.append(f"{m.rel}:{d.line}: second proof for {d.label} (first at line {seen_proofs[d.label]})")
                    seen_proofs[d.label] = d.line
                    if d.label not in stmt_pos:
                        problems.append(f"{m.rel}:{d.line}: proof for {d.label} without a preceding statement in this module")
                    elif d.label != last_stmt:
                        problems.append(f"{m.rel}:{d.line}: proof for {d.label} does not directly follow its statement (last statement: {last_stmt})")
    total_exp = ctx.inv.totals()["proofs"]
    total_act = sum(1 for nv in view.nodes.values() if nv.has_proof)
    if not ctx.partial and total_exp != total_act:
        problems.append(f"number of proofs: expected {total_exp}, actual {total_act}")
    ctx.verdict("V2.proofs" + view.suffix, ctx.cap(problems),
                f"proofs present exactly for the nodes that have one in TeX ({total_act} proofs), each right after its statement"
                if view.name == "source" else f"proofs present exactly for the nodes that have one in TeX ({total_act} proofs)",
                f"{len(problems)} proof problem(s)")


def check_edges(ctx: Ctx, view: View) -> None:
    id_ = "V2.edges" + view.suffix
    if not view.has_edges:
        ctx.skip(id_, "needs `node` data (use --vbp-nodes) or a manifest")
        return
    problems = []
    nstmt = nproof = 0
    for l, nv in view.nodes.items():
        n = ctx.inv.by_label.get(l)
        if not n:
            continue
        for kind, exp, act in (("statement", n["statement_uses_verso"] if n.get("statement_uses_verso") is not None else [label_rule(u) for u in n["statement_uses"]], nv.stmt_uses),
                               ("proof", n["proof_uses_verso"] if n.get("proof_uses_verso") is not None else [label_rule(u) for u in n["proof_uses"]], nv.proof_uses)):
            if kind == "proof" and not nv.has_proof and not n["has_proof"]:
                continue
            e, a = set(exp), set(act)
            if kind == "statement":
                nstmt += len(a)
            else:
                nproof += len(a)
            if e != a:
                problems.append(f"{l} {kind} uses: missing {sorted(e - a)}, extra {sorted(a - e)}  ({nv.where})")
    if not ctx.partial:
        t = ctx.inv.totals()
        if (t["statement_edges"], t["proof_edges"]) != (nstmt, nproof):
            problems.append(f"edge totals: expected {t['statement_edges']} statement / {t['proof_edges']} proof, actual {nstmt} / {nproof}")
    ctx.verdict(id_, ctx.cap(problems), f"statement and proof `uses` sets equal the inventory's for all {len(view.nodes)} present node(s) "
                f"({nstmt} statement + {nproof} proof edges)", f"{len(problems)} node(s) with differing edges")


def check_targets_source(ctx: Ctx, view: View) -> None:
    src, inv = ctx.src, ctx.inv
    labels = set(view.nodes)
    problems: List[str] = []
    pending: List[str] = []
    n_checked = 0

    def check_target(t: str, where: str, how: str) -> None:
        nonlocal n_checked
        n_checked += 1
        if t in labels:
            return
        if ctx.partial and t in inv.by_label:
            pending.append(f"{where}: {how} -> {t} (not yet ported)")
            return
        hint = ""
        if label_rule(t) in labels and ":" in t:
            hint = f" (hint: `:` not replaced; use {label_rule(t)})"
        problems.append(f"{where}: {how} target {t!r} does not exist{hint}")

    for m in src.modules:
        for it in m.items:
            if it[0] == "directive":
                d = it[1]
                if d.name in DIRECTIVE_KIND or d.name == "proof":
                    for t in d.uses_option:
                        check_target(t, f"{m.rel}:{d.line} `{d.name} {d.label}`", "(uses := ..)")
                if d.name in DIRECTIVE_KIND or d.name == "proof" or d.name == "group":
                    for r in d.info.roles:
                        if r.name in ("uses", "bpref"):
                            if r.target is None:
                                problems.append(f"{m.rel}:{r.line}: {{{r.name}}} without a label argument")
                            else:
                                check_target(r.target, f"{m.rel}:{r.line}", "{" + r.name + " ..}")
            elif it[0] == "prose":
                for r in it[1].roles:
                    if r.name in ("uses", "bpref"):
                        if r.target is None:
                            problems.append(f"{m.rel}:{r.line}: {{{r.name}}} without a label argument")
                        else:
                            check_target(r.target, f"{m.rel}:{r.line} (prose)", "{" + r.name + " ..}")
    c = ctx.verdict("V2.targets", ctx.cap(problems), f"all {n_checked} uses / {{uses ..}} / {{bpref ..}} targets exist",
                    f"{len(problems)} dangling target(s)")
    if pending and c.status == PASS:
        c.details = ctx.cap(pending)
        c.summary += f" ({len(pending)} point to nodes not yet ported)"


def check_groups_source(ctx: Ctx, view: View) -> None:
    src, inv = ctx.src, ctx.inv
    problems: List[str] = []
    group_ids: Dict[str, str] = {}
    nchap = 0
    for m in src.modules:
        ch = ctx.mapping.get(m.rel)
        groups = m.directives("group")
        nchap += 1
        if len(groups) != 1:
            problems.append(f"{m.rel}: {len(groups)} `:::group` directive(s), expected exactly one per chapter")
        gid = groups[0].label if groups else None
        if gid is not None:
            if not gid.startswith("grp_"):
                problems.append(f"{m.rel}: group id {gid!r} does not start with `grp_`")
            if gid in group_ids:
                problems.append(f"{m.rel}: group id {gid!r} also used by {group_ids[gid]}")
            group_ids[gid] = m.rel
            if ch is not None:
                gt = canon_text(groups[0].info.text())
                ct = canon_text(inv.chapter_by_number[ch]["title"])
                gts = re.sub(r"^appendix(?:\s+[A-Za-z0-9]+)?\s*[:.\u2013\u2014-]+\s*", "", gt, flags=re.I)
                if gt != ct and gts != ct:
                    problems.append(f"{m.rel}: group title {groups[0].info.text()!r} != chapter title {inv.chapter_by_number[ch]['title']!r}")
        for d in m.statements():
            par = d.options.get("parent")
            if par is None:
                problems.append(f"{m.rel}:{d.line}: `{d.label}` has no `(parent := \"grp_..\")`")
            elif gid is not None and par != gid:
                problems.append(f"{m.rel}:{d.line}: `{d.label}` has parent {par!r}, but this chapter's group is {gid!r}")
            elif gid is None:
                problems.append(f"{m.rel}:{d.line}: `{d.label}` has parent {par!r} but the module declares no group")
    ctx.verdict("V2.groups", ctx.cap(problems),
                f"every statement has `(parent := \"grp_..\")` of its chapter's single group ({len(group_ids)} group(s), one per chapter module, distinct)",
                f"{len(problems)} grouping problem(s)")


def check_groups_generator(ctx: Ctx, view: View, manifest: Optional[dict]) -> None:
    inv = ctx.inv
    problems: List[str] = []
    for l, nv in view.nodes.items():
        if not nv.parent:
            problems.append(f"{l}: no group (parent) in the generator's view")
    parents = {nv.parent for nv in view.nodes.values() if nv.parent}
    if manifest is not None:
        groups = {g["label"]: g for g in manifest.get("groups", [])}
        for p in sorted(parents):
            if p not in groups:
                problems.append(f"parent group {p} is not declared in the manifest groups")
        by_parent: Dict[str, List[str]] = {}
        for l, nv in view.nodes.items():
            if nv.parent:
                by_parent.setdefault(nv.parent, []).append(l)
        # each group = exactly one chapter
        for p, ls in sorted(by_parent.items()):
            chs = {inv.by_label[l]["chapter"] for l in ls if l in inv.by_label}
            if len(chs) > 1:
                problems.append(f"group {p} mixes chapters {sorted(chs)}")
        chap_groups: Dict[str, set] = {}
        for p, ls in by_parent.items():
            for l in ls:
                if l in inv.by_label:
                    chap_groups.setdefault(inv.by_label[l]["chapter"], set()).add(p)
        for ch, gs in sorted(chap_groups.items()):
            if len(gs) > 1:
                problems.append(f"chapter {ch} is split over several groups {sorted(gs)}")
        if not ctx.partial and len(groups) != len(inv.chapters):
            problems.append(f"manifest declares {len(groups)} groups, expected {len(inv.chapters)} (one per chapter)")
    elif len(parents) > len(inv.chapters):
        problems.append(f"{len(parents)} distinct parents, expected at most {len(inv.chapters)}")
    ctx.verdict("V2.groups" + view.suffix, ctx.cap(problems),
                f"every node has a group; {len(parents)} group(s), each covering one chapter", f"{len(problems)} grouping problem(s)")


def order_diff(expected: Sequence, actual: Sequence, limit: int = 6) -> List[str]:
    """Report for sequences of labels: positions where they differ (same elements) or an opcode diff."""
    expected, actual = list(expected), list(actual)
    if expected == actual:
        return []
    if len(expected) == len(actual) and sorted(expected) == sorted(actual):
        diff = [i for i in range(len(expected)) if expected[i] != actual[i]]
        out = ["same elements, different order:"]
        for i in diff[:limit]:
            out.append(f"position {i + 1}: expected {expected[i]}, actual {actual[i]}")
        if len(diff) > limit:
            out.append(f"... and {len(diff) - limit} more positions")
        return out
    return seq_diff_short(expected, actual)


def math_diff(expected: Sequence[Tuple[str, str]], actual: Sequence[Tuple[str, str]], limit: int = 3) -> List[str]:
    out: List[str] = []
    sm = difflib.SequenceMatcher(None, list(expected), list(actual), autojunk=False)
    ops = [op for op in sm.get_opcodes() if op[0] != "equal"]
    for tag, i1, i2, j1, j2 in ops[:limit]:
        e = expected[i1:i2]
        a = actual[j1:j2]
        for k in range(max(len(e), len(a), 1)):
            ee = f"{e[k][0]} `{trunc(e[k][1], 80)}`" if k < len(e) else "(nothing)"
            aa = f"{a[k][0]} `{trunc(a[k][1], 80)}`" if k < len(a) else "(nothing)"
            out.append(f"span {i1 + k + 1}: expected {ee}")
            out.append(f"{' ' * len(f'span {i1 + k + 1}: ')}actual   {aa}")
            if k >= 2:
                out.append("...")
                break
    if len(ops) > limit:
        out.append(f"... and {len(ops) - limit} more differing blocks")
    return out


def fmt_list(items: Sequence, k: int = 4) -> str:
    items = list(items)
    if len(items) <= k:
        return str(items)
    return "[" + ", ".join(repr(x) for x in items[:k - 1]) + f", ... ({len(items) - k + 1} more)" + "]"


def seq_diff_short(expected: Sequence, actual: Sequence, fmt=str, limit: int = 4) -> List[str]:
    """Like seq_diff but never prints long element lists."""
    out: List[str] = []
    sm = difflib.SequenceMatcher(None, list(expected), list(actual), autojunk=False)
    ops = [op for op in sm.get_opcodes() if op[0] != "equal"]
    if not ops:
        return out
    if sorted(map(repr, expected)) == sorted(map(repr, actual)):
        out.append("same elements, different order:")
    for tag, i1, i2, j1, j2 in ops[:limit]:
        exp = [fmt(x) for x in expected[i1:i2]]
        act = [fmt(x) for x in actual[j1:j2]]
        out.append(f"at position {i1} (expected) / {j1} (actual): expected {fmt_list(exp)} but got {fmt_list(act)}")
    if len(ops) > limit:
        out.append(f"... and {len(ops) - limit} more differing blocks")
    return out


def check_order_and_headings(ctx: Ctx, view: View) -> None:
    inv, src = ctx.inv, ctx.src
    order_p: List[str] = []
    head_p: List[str] = []
    outl_p: List[str] = []
    complete = ctx.complete_chapters(view)
    n_ch = n_outline = n_outline_skipped = 0
    sym = lambda h: f"{'#' * h[0]} {h[1]}"  # noqa: E731
    for m in src.modules:
        ch = ctx.mapping.get(m.rel)
        if ch is None:
            continue
        n_ch += 1
        exp_all = [n["label_verso"] for n in inv.nodes_of_chapter[ch]]
        known = set(exp_all)
        act = [d.label for d in m.statements() if d.label in known]
        exp = [l for l in exp_all if l in set(act)]  # order only: missing/extra nodes are V2.labels' business
        node_ok = act == exp
        if not node_ok:
            order_p.append(f"chapter {ch} ({m.rel}):")
            order_p += ["  " + x for x in order_diff(exp, act)]
        strict = (not ctx.partial) or ch in complete
        exp_h = [(1 if o["type"] == "section" else 2, canon_text(o["title"])) for o in inv.outline_of_chapter(ch) if o["type"] != "node"]
        act_h = [(it[1], canon_text(it[4].text())) for it in m.headings()]
        head_ok = True
        if strict:
            if act_h != exp_h:
                head_ok = False
                head_p.append(f"chapter {ch} ({m.rel}):")
                head_p += ["  " + x for x in seq_diff_short(exp_h, act_h, fmt=sym)]
        else:
            ok, bad = is_subsequence(act_h, exp_h)
            if not ok:
                head_ok = False
                head_p.append(f"chapter {ch} ({m.rel}): heading `{sym(act_h[bad])}` is not an inventory heading in the right order")
        if node_ok and head_ok and strict:
            n_outline += 1
            present = set(act)
            exp_seq = [("S" if o["type"] == "section" else "SS" if o["type"] == "subsection" else "N",
                        canon_text(o["title"]) if o["type"] != "node" else o["label_verso"]) for o in inv.outline_of_chapter(ch)
                       if o["type"] != "node" or o["label_verso"] in present]
            act_seq = []
            for it in m.items:
                if it[0] == "heading":
                    act_seq.append(("S" if it[1] == 1 else "SS", canon_text(it[4].text())))
                elif it[0] == "directive" and it[1].name in DIRECTIVE_KIND and it[1].label in known:
                    act_seq.append(("N", it[1].label))
            if act_seq != exp_seq:
                outl_p.append(f"chapter {ch} ({m.rel}): headings sit at different places relative to the nodes:")
                outl_p += ["  " + x for x in seq_diff_short(exp_seq, act_seq, fmt=lambda t: f"{t[0]}:{t[1]}")]
        else:
            n_outline_skipped += 1
    part = " (present nodes only)" if ctx.partial else ""
    ctx.verdict("V2.order", ctx.cap(order_p), f"document order of the nodes in {n_ch} chapter module(s) equals the inventory's{part}",
                f"node order differs from the inventory in {sum(1 for x in order_p if x.startswith('chapter'))} chapter(s)")
    ctx.verdict("V2.headings", ctx.cap(head_p),
                f"`#`/`##` headings of {n_ch} chapter module(s) match the inventory outline"
                + (" (complete chapters strictly, others as an ordered subset)" if ctx.partial else ""),
                f"headings differ from the inventory outline in {sum(1 for x in head_p if x.startswith('chapter'))} chapter(s)")
    if n_outline == 0 and not outl_p:
        ctx.skip("V2.outline", "no chapter with matching node order and headings to compare" + (" yet" if ctx.partial else ""))
    else:
        ctx.verdict("V2.outline", ctx.cap(outl_p),
                    f"headings and nodes interleave as in the inventory outline ({n_outline} chapter(s) checked"
                    + (f", {n_outline_skipped} skipped: incomplete or order/headings already differ" if n_outline_skipped else "") + ")",
                    f"heading placement differs in {sum(1 for x in outl_p if x.startswith('chapter'))} chapter(s)")


def check_order_generator(ctx: Ctx, view: View) -> None:
    """Nodes sorted by source position within each module file vs inventory order (manifest only)."""
    inv = ctx.inv
    groups: Dict[str, List[NodeV]] = {}
    for nv in view.nodes.values():
        if nv.path and nv.line:
            groups.setdefault(nv.path, []).append(nv)
    if not groups:
        ctx.skip("V2.order" + view.suffix, "no sourceLocation in the generator data")
        return
    problems = []
    for path, nvs in sorted(groups.items()):
        nvs.sort(key=lambda x: x.line)
        votes: Dict[str, int] = {}
        for nv in nvs:
            n = inv.by_label.get(nv.label)
            if n:
                votes[n["chapter"]] = votes.get(n["chapter"], 0) + 1
        if not votes:
            continue
        ch = max(votes, key=lambda k: votes[k])
        act = [nv.label for nv in nvs if nv.label in inv.by_label]
        present = set(act)
        exp = [n["label_verso"] for n in inv.nodes_of_chapter[ch] if n["label_verso"] in present]
        # nodes of other chapters found in this file are a label-level problem; compare the common part
        act_c = [l for l in act if inv.by_label[l]["chapter"] == ch]
        if act_c != exp:
            problems.append(f"{os.path.basename(path)} (chapter {ch}):")
            problems += ["  " + x for x in order_diff(exp, act_c)]
    ctx.verdict("V2.order" + view.suffix, ctx.cap(problems), f"generator source order of nodes equals the inventory's in {len(groups)} module file(s)",
                "generator order differs from the inventory")


def check_numbers(ctx: Ctx, view: View) -> None:
    inv = ctx.inv
    id_ = "V2.numbers" + view.suffix
    if not view.has_numbers:
        ctx.skip(id_, "needs `node` data (use --vbp-nodes) or a manifest")
        return
    problems = []
    n_ok = n_skip = 0
    for n in inv.nodes:
        l = n["label_verso"]
        nv = view.nodes.get(l)
        if nv is None:
            continue
        if not ctx.number_verifiable(view, n):
            n_skip += 1
            continue
        exp = expected_number(n, ctx.offset)
        if nv.number != exp:
            problems.append(f"{l}: expected number {exp} (legacy {n['number']}), actual {nv.number}  ({nv.where})")
        else:
            n_ok += 1
    c = ctx.verdict(id_, ctx.cap(problems),
                    f"rendered number == legacy number for {n_ok} node(s) (appendices A,B -> {render_chapter('A', ctx.offset)},{render_chapter('B', ctx.offset)}"
                    f"{'' if ctx.offset else ' [no shift]'})" + (f"; {n_skip} not verifiable (earlier nodes not yet ported)" if n_skip else ""),
                    f"{len(problems)} node(s) with the wrong number")
    # the six anchors
    ap = []
    shown = 0
    for lab, num in ctx.anchors.items():
        l = label_rule(lab)
        nv = view.nodes.get(l)
        n = inv.by_label.get(l)
        if nv is None:
            if not ctx.partial:
                ap.append(f"{lab} ({l}): node missing, expected {num}")
            continue
        if n is not None and not ctx.number_verifiable(view, n):
            continue
        shown += 1
        if nv.number != num:
            ap.append(f"{lab} ({l}): expected {num}, actual {nv.number}")
    if not ctx.anchors:
        ctx.skip("V2.anchors" + view.suffix, "disabled (--anchors none)")
    elif shown == 0 and not ap:
        ctx.skip("V2.anchors" + view.suffix, f"none of the {len(ctx.anchors)} explicit legacy anchors is ported yet")
    else:
        ctx.verdict("V2.anchors" + view.suffix, ap,
                    (f"all {len(ctx.anchors)} explicit legacy numbers hold (" + ", ".join(f"{k}={v}" for k, v in ctx.anchors.items()) + ")")
                    if shown == len(ctx.anchors) else
                    f"{shown} of {len(ctx.anchors)} explicit legacy numbers present and correct; {len(ctx.anchors) - shown} not verifiable yet (not ported)",
                    f"{len(ap)} explicit legacy number(s) wrong or missing")


# ---- V3 / V4: source view only ---------------------------------------------------------------------------------------

def stmt_proof_directives(m: Module) -> Tuple[Dict[str, Directive], Dict[str, Directive]]:
    stmts: Dict[str, Directive] = {}
    proofs: Dict[str, Directive] = {}
    for d in m.directives():
        if d.name in DIRECTIVE_KIND and d.label:
            stmts.setdefault(d.label, d)
        elif d.name == "proof" and d.label:
            proofs.setdefault(d.label, d)
    return stmts, proofs


def spans_of(d: Optional[Directive]) -> List[Tuple[str, str]]:
    if d is None:
        return []
    return [(s.kind, norm_tex(s.tex)) for s in d.info.spans if not s.in_title]


def check_math(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    problems: List[str] = []
    n_nodes = n_spans = 0
    bad_nodes = 0
    empty_expected_with_none = 0
    expecting = 0
    for m in src.modules:
        stmts, proofs = stmt_proof_directives(m)
        for l, d in stmts.items():
            n = inv.by_label.get(l)
            if n is None:
                continue
            n_nodes += 1
            exp_s = [(s["kind"], norm_tex(s["tex"])) for s in n["math_spans"]]
            exp_p = [(s["kind"], norm_tex(s["tex"])) for s in n["proof_math_spans"]]
            act_s = spans_of(d)
            act_p = spans_of(proofs.get(l))
            n_spans += len(exp_s) + len(exp_p)
            if exp_s or exp_p:
                expecting += 1
                if not act_s and not act_p:
                    empty_expected_with_none += 1
            bad = False
            for what, e, a in (("statement", exp_s, act_s), ("proof", exp_p, act_p)):
                if e != a:
                    bad = True
                    problems.append(f"{l} ({m.rel}:{d.line}) {what} maths: expected {len(e)} span(s), found {len(a)}")
                    problems.extend("    " + x for x in math_diff(e, a))
            bad_nodes += bad
    summary_fail = f"maths spans differ in {bad_nodes} of {n_nodes} node(s)"
    if expecting and empty_expected_with_none == expecting:
        summary_fail += (f" -- NO maths at all was found on the Verso side for the {expecting} node(s) that have spans in TeX "
                         f"(empty / placeholder bodies?)")
    ctx.verdict("V3.math", ctx.cap(problems),
                f"ordered maths spans (inline vs display, statement vs proof) identical for {n_nodes} node(s) ({n_spans} spans)"
                + (" (--partial: present nodes only)" if ctx.partial else ""), summary_fail)


def check_macros(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    used_inv = set()
    for n in inv.nodes:
        for s in n["math_spans"] + n["proof_math_spans"]:
            used_inv |= macros_in(s["tex"])
    used_verso = set()
    for m in src.modules:
        for _, info, _ in m.all_infos():
            for s in info.spans:
                used_verso |= macros_in(s.tex)
    defined = src.macros_defined
    lines = []
    if defined is None:
        ctx.info("V3.macros", f"{src.macros_file} not found; {len(used_verso)} distinct macros used in Verso maths, cannot compare")
        return
    whitelist = {x for x in used_inv if x not in defined}  # standard TeX/KaTeX commands as used by the TeX side itself
    unknown = sorted(used_verso - defined - whitelist)
    if unknown:
        lines.append("used in Verso maths but neither defined in Macros.lean nor used (undefined) by the TeX side: " + ", ".join("\\" + u for u in unknown))
    maybe_missing = sorted(x for x in used_inv if x not in defined and x not in STANDARD_MACROS)
    if maybe_missing:
        lines.append("used by the TeX side, not defined in Macros.lean, not in the built-in standard list (needs a definition?): "
                     + ", ".join("\\" + u for u in maybe_missing))
    ctx.info("V3.macros", f"{len(defined)} macros defined in Macros.lean; {len(used_verso)} distinct macros used in Verso maths; "
             f"{len(unknown)} unknown" + ("" if not maybe_missing else f"; {len(maybe_missing)} TeX-side macro(s) possibly undefined"), lines)


def check_v4_counts(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    problems: List[str] = []
    n_nodes = 0
    for m in src.modules:
        stmts, proofs = stmt_proof_directives(m)
        for l, d in stmts.items():
            n = inv.by_label.get(l)
            if n is None:
                continue
            n_nodes += 1
            infos = [d.info] + ([proofs[l].info] if l in proofs else [])
            got = {
                "term": sum(len(i.roles_named("term")) for i in infos),
                "palka": sum(len(i.roles_named("palka")) for i in infos),
                "ref": sum(len(i.roles_named("bpref")) + len(i.roles_named("uses")) for i in infos),
            }
            exp = {"term": n.get("n_term", 0), "palka": n.get("n_palka", 0), "ref": n.get("n_ref", 0)}
            for k in ("term", "palka", "ref"):
                if got[k] != exp[k]:
                    role = {"term": "{term}", "palka": "{palka}", "ref": "{bpref}/{uses} roles"}[k]
                    problems.append(f"{l}: {role} count expected {exp[k]}, actual {got[k]}  ({m.rel}:{d.line})")
    ctx.verdict("V4.counts", ctx.cap(problems), f"{{term}}, {{palka}} and reference-role counts equal n_term / n_palka / n_ref for {n_nodes} node(s)",
                f"{len(problems)} count mismatch(es)")


def check_titles(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    problems: List[str] = []
    n_nodes = 0
    for m in src.modules:
        for l, d in stmt_proof_directives(m)[0].items():
            n = inv.by_label.get(l)
            if n is None:
                continue
            n_nodes += 1
            exp_title = tex_title_text(n["title_raw"])
            exp_palka = tex_palka_args(n["title_raw"])
            titles = d.info.roles_named("nodetitle")
            palkas = d.info.roles_named("palka")
            where = f"{m.rel}:{d.line}"
            if exp_title:
                if len(titles) != 1:
                    problems.append(f"{l}: expected exactly one {{nodetitle}}[..] (title {exp_title!r}), found {len(titles)}  ({where})")
                else:
                    act = canon_text(titles[0].text)
                    if act != exp_title:
                        problems.append(f"{l}: title expected {exp_title!r}, actual {act!r}  ({where})")
            elif titles:
                problems.append(f"{l}: TeX has no title but there is a {{nodetitle}}[{titles[0].text}]  ({where})")
            if len(palkas) == len(exp_palka):
                for e, r in zip(exp_palka, palkas):
                    if canon_text(r.text) != canon_text(e):
                        problems.append(f"{l}: {{palka}} text expected {e!r}, actual {r.text!r}  ({where})")
    ctx.verdict("V4.titles", ctx.cap(problems), f"every node's {{nodetitle}} and {{palka}} text equals the TeX title ({n_nodes} node(s))",
                f"{len(problems)} title/reference problem(s)")


def check_leftovers(ctx: Ctx) -> None:
    src = ctx.src
    tex_p: List[str] = []
    esc_p: List[str] = []
    n_chunks = 0
    for m in src.modules:
        chunks = list(m.all_infos())
        if m.title_info is not None:
            chunks.append(("#doc title", m.title_info, 1))
        for where, info, line in chunks:
            n_chunks += 1
            for pb in info.problems:
                row = f"{m.rel}:{pb.line} ({where}): {pb.msg}"
                if pb.cat == "tex":
                    tex_p.append(row)
                elif pb.cat == "escape":
                    esc_p.append(row)
    ctx.verdict("V4.tex", ctx.cap(tex_p), f"no leftover TeX commands / ties / dashes / `$..$` in the running text ({n_chunks} text chunk(s) scanned)",
                f"{len(tex_p)} leftover TeX construct(s) in the text")
    ctx.verdict("V4.escapes", ctx.cap(esc_p), "no unescaped Verso specials (`* _ [ ] { } `` ` ``) in the running text",
                f"{len(esc_p)} unescaped special character(s) in the text")
    # unknown roles (informational)
    known = set(BUILTIN_ROLES)
    if src.roles_defined is not None:
        known |= src.roles_defined
    unknown: Dict[str, int] = {}
    metsp = 0
    for m in src.modules:
        for _, info, _ in m.all_infos():
            for r in info.roles:
                if r.name == "metSpCourse":
                    metsp += 1
                if r.name not in known:
                    unknown[r.name] = unknown.get(r.name, 0) + 1
    if unknown:
        ctx.info("V4.roles", f"{len(unknown)} role name(s) neither built in nor defined in Roles.lean: "
                 + ", ".join(f"{{{k}}} x{v}" for k, v in sorted(unknown.items())))


def check_intro(ctx: Ctx) -> None:
    src, inv = ctx.src, ctx.inv
    if src.blueprint_text is None or inv.intro is None:
        ctx.skip("V4.intro", f"{src.blueprint_file} or inventory intro missing")
        return
    text = src.blueprint_text.replace("\r\n", "\n")
    lines = text.split("\n")
    start = 0
    for i, l in enumerate(lines):
        if _DOC_RE.match(l):
            start = i + 1
            break
    # skip metadata block
    j = start
    while j < len(lines) and lines[j].strip() == "":
        j += 1
    if j < len(lines) and lines[j].strip() == "%%%":
        j += 1
        while j < len(lines) and lines[j].strip() != "%%%":
            j += 1
        j += 1
    end = len(lines)
    for i in range(j, len(lines)):
        if re.match(r"^\s*\{(include|blueprint_graph|blueprint_summary)\b", lines[i]):
            end = i
            break
    info = analyze("\n".join(lines[j:end]), j + 1)
    act = canon_text(info.text(math=True))
    expected = re.sub(r"\\(?:emph|textbf|textit)\{([^{}]*)\}", r"\1", inv.intro)
    exp = canon_text(expected)
    probs = [f"{src.blueprint_file}:{p.line}: {p.msg}" for p in info.problems if p.cat in ("tex", "syntax", "escape")]
    if act != exp:
        a_w, e_w = act.split(), exp.split()
        probs.append("intro text differs from the inventory's (content.tex) after removing emphasis markup:")
        probs += ["  " + x for x in seq_diff_short(e_w, a_w, fmt=lambda w: w, limit=4)]
    ctx.verdict("V4.intro", ctx.cap(probs), "intro paragraphs of Blueprint.lean equal content.tex (modulo emphasis markup)", "intro text problem(s)")


def check_v4_global(ctx: Ctx) -> None:
    inv, src = ctx.inv, ctx.src
    t = inv.totals()
    n_term = n_palka = n_sec = n_sub = 0
    for m in src.modules:
        for _, info, _ in m.all_infos():
            n_term += len(info.roles_named("term"))
            n_palka += len(info.roles_named("palka"))
        n_sec += sum(1 for h in m.headings() if h[1] == 1)
        n_sub += sum(1 for h in m.headings() if h[1] == 2)
    got = {"term": n_term, "palka": n_palka, "sections": n_sec, "subsections": n_sub}
    if ctx.partial:
        ctx.info("V4.global", f"(--partial) in the Verso sources: {n_term}/{t['term']} {{term}}, {n_palka}/{t['palka']} {{palka}}, "
                 f"{n_sec}/{t['sections']} sections, {n_sub}/{t['subsections']} subsections")
        return
    problems = [f"total {k}: expected {t[k]}, actual {got[k]}" for k in ("term", "palka", "sections", "subsections") if t[k] != got[k]]
    ctx.verdict("V4.global", problems, f"totals: {n_term} {{term}}, {n_palka} {{palka}}, {n_sec} sections, {n_sub} subsections as in the inventory",
                "global text totals differ from the inventory")


# ---- generator-side orchestration --------------------------------------------------------------------------------------

def find_manifest(site: str) -> Optional[str]:
    for rel in ("html-multi/-verso-data/blueprint-manifest.json", "-verso-data/blueprint-manifest.json"):
        p = os.path.join(site, rel)
        if os.path.isfile(p):
            return p
    return None


def check_manifest_extras(ctx: Ctx, manifest: dict, view: View) -> None:
    probs = []
    for g in manifest.get("graphs", []):
        for node in g.get("nodes", []):
            w = node.get("warnings") or {}
            if w.get("unknownRef"):
                probs.append(f"graph {g.get('key')}: node {node.get('label')} has warnings.unknownRef")
    labels = set(view.nodes)
    for l, nv in view.nodes.items():
        for u in nv.stmt_uses + nv.proof_uses:
            if u not in labels:
                probs.append(f"{l}: manifest edge to unknown node {u}")
    ctx.verdict("V2.targets[manifest]", ctx.cap(probs), "no unknown references in the generator's graph; all edge targets are nodes",
                f"{len(probs)} unknown reference(s)")


def run_vbp(ctx: Ctx, manifest_view: Optional[View]) -> Optional[View]:
    o = ctx.opts
    inv = ctx.inv
    try:
        stats = vbp_query(o.vbp_cmd, ctx.root, o.site, ["stats"], o.vbp_timeout)
        labels = vbp_query(o.vbp_cmd, ctx.root, o.site, ["labels"], o.vbp_timeout)
    except Exception as e:  # noqa: BLE001
        ctx.add("GEN.vbp", False, f"`vbp query` failed: {e}")
        return None
    rows = labels.get("labels", [])
    t = inv.totals()
    probs = []
    if not ctx.partial:
        if stats.get("statements") != t["nodes"]:
            probs.append(f"stats.statements: expected {t['nodes']}, actual {stats.get('statements')}")
        for k in sorted(set(t["by_kind"]) | set(stats.get("byKind", {}))):
            if t["by_kind"].get(k, 0) != stats.get("byKind", {}).get(k, 0):
                probs.append(f"stats.byKind[{k}]: expected {t['by_kind'].get(k, 0)}, actual {stats.get('byKind', {}).get(k, 0)}")
    else:
        for k, v in stats.get("byKind", {}).items():
            if v > t["by_kind"].get(k, 0):
                probs.append(f"stats.byKind[{k}] = {v} exceeds the inventory's {t['by_kind'].get(k, 0)}")
    if len(rows) != stats.get("statements", len(rows)):
        probs.append(f"`labels` returned {len(rows)} rows but stats.statements = {stats.get('statements')}")
    ctx.verdict("V2.counts[vbp-stats]", probs, f"`vbp query stats`: {stats.get('statements')} statements, byKind {stats.get('byKind')}",
                "`vbp query stats` disagrees with the inventory")
    node_json: Dict[str, dict] = {}
    if o.vbp_nodes:
        try:
            for r in rows:
                lab = r.get("authoredLabel") or strip_guillemets(r.get("label", ""))
                node_json[lab] = vbp_query(o.vbp_cmd, ctx.root, o.site, ["node", lab], o.vbp_timeout)
        except Exception as e:  # noqa: BLE001
            ctx.add("GEN.vbp", False, f"`vbp query node` failed: {e}")
            return None
    view = view_from_node_json(rows, node_json)
    if manifest_view is not None:
        probs = []
        if set(manifest_view.nodes) != set(view.nodes):
            probs.append(f"label sets differ: only in manifest {sorted(set(manifest_view.nodes) - set(view.nodes))[:8]}, "
                         f"only in `vbp query labels` {sorted(set(view.nodes) - set(manifest_view.nodes))[:8]}")
        ctx.verdict("GEN.consistency", probs, "`vbp query` and the manifest list the same nodes", "generator outputs disagree")
    return view


def run_generator_checks(ctx: Ctx, view: View, manifest: Optional[dict]) -> None:
    check_coverage(ctx, view)
    check_counts(ctx, view)
    check_labels(ctx, view)
    check_kinds(ctx, view)
    check_proofs(ctx, view)
    check_edges(ctx, view)
    if view.has_parents:
        check_groups_generator(ctx, view, manifest)
    if manifest is not None:
        check_manifest_extras(ctx, manifest, view)
        check_order_generator(ctx, view)
    check_numbers(ctx, view)


def run(opts: argparse.Namespace) -> Tuple[List[Check], Ctx]:
    with open(opts.inventory, encoding="utf-8") as fh:
        inv = Inventory(json.load(fh))
    src = VersoSource(opts.root, opts.chapters_dir, opts.macros_file, opts.roles_file, opts.blueprint_file)
    ctx = Ctx(inv, src, opts)
    check_inventory(ctx)
    ctx.mapping, ctx.map_problems = map_modules(inv, src.modules)
    check_syntax(ctx)
    check_modules(ctx)
    check_imports(ctx)
    view = build_source_view(inv, src, ctx.mapping, ctx.offset)
    ctx.views.append(view)
    check_coverage(ctx, view)
    check_counts(ctx, view)
    check_labels(ctx, view)
    check_kinds(ctx, view)
    check_proofs(ctx, view)
    check_edges(ctx, view)
    check_targets_source(ctx, view)
    check_groups_source(ctx, view)
    check_order_and_headings(ctx, view)
    check_numbers(ctx, view)
    check_math(ctx)
    check_macros(ctx)
    check_v4_counts(ctx)
    check_titles(ctx)
    check_leftovers(ctx)
    check_intro(ctx)
    check_v4_global(ctx)
    # generator side
    manifest = None
    mview = None
    if opts.site:
        site = opts.site if os.path.isabs(opts.site) else os.path.join(opts.root, opts.site)
        path = find_manifest(site)
        if path is None:
            ctx.add("GEN.manifest", False, f"no blueprint-manifest.json under {site} (run `lake exe vbp build` first)")
        else:
            with open(path, encoding="utf-8") as fh:
                manifest = json.load(fh)
            mview = view_from_manifest(manifest)
            ctx.info("GEN.manifest", f"read {os.path.relpath(path, opts.root)}: {len(mview.nodes)} statement entries, "
                     f"schema {manifest.get('vbpInternalSchemaVersion')}")
            run_generator_checks(ctx, mview, manifest)
    if opts.vbp:
        vview = run_vbp(ctx, mview)
        if vview is not None:
            if vview.has_edges:
                run_generator_checks(ctx, vview, manifest)
            else:
                check_counts(ctx, vview)
                check_labels(ctx, vview)
                check_kinds(ctx, vview)
                if vview.has_parents:
                    check_groups_generator(ctx, vview, None)
                ctx.info("GEN.vbp", "only `vbp query labels`/`stats` were used (add --vbp-nodes for edges, proofs and numbers)")
    return ctx.results, ctx


_SYMBOL = {PASS: "PASS", FAIL: "FAIL", INFO: "INFO", SKIP: "SKIP"}


def print_report(results: List[Check], opts: argparse.Namespace, ctx: Ctx, out=None) -> None:
    out = out or sys.stdout
    mode = ["source"]
    if opts.site:
        mode.append("manifest")
    if opts.vbp:
        mode.append("vbp-query")
    print(f"Parity check  inventory: {opts.inventory}  root: {opts.root}", file=out)
    print(f"mode: {'+'.join(mode)}{', partial' if opts.partial else ', full'}; appendix offset {opts.appendix_offset}; "
          f"{len(ctx.src.modules)} chapter module(s), {len(ctx.inv.nodes)} inventory nodes", file=out)
    print("", file=out)
    for c in results:
        print(f"[{_SYMBOL[c.status]}] {c.id}: {c.summary}", file=out)
        if c.status in (FAIL, INFO) or (opts.verbose and c.details):
            for d in c.details:
                print(f"        {d}", file=out)
    n = {k: sum(1 for c in results if c.status == k) for k in (PASS, FAIL, INFO, SKIP)}
    print("", file=out)
    print(f"SUMMARY: {len(results)} checks: {n[PASS]} PASS, {n[FAIL]} FAIL, {n[INFO]} INFO, {n[SKIP]} SKIP", file=out)
    if n[FAIL]:
        print("RESULT: FAIL (" + ", ".join(c.id for c in results if c.status == FAIL) + ")", file=out)
    else:
        print("RESULT: PASS" + (" (partial: nodes not yet ported are not checked)" if opts.partial else ""), file=out)


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description="Independent parity checker for the leanblueprint -> Verso Blueprint migration.")
    ap.add_argument("--inventory", default="scripts/migration/baseline_inventory.json")
    ap.add_argument("--root", default=".", help="repository root (contains ComplexAnalysisCourse/)")
    ap.add_argument("--partial", action="store_true", help="check only nodes present on the Verso side; report the rest as not yet ported")
    ap.add_argument("--appendix-offset", type=int, default=6,
                    help="appendix chapters A,B,.. are rendered as chapters 1+N, 2+N, .. (default 6: A->7, B->8; 0: keep letters)")
    ap.add_argument("--chapters-dir", default=CHAPTERS_DIR, help="directory (relative to --root) with one Lean module per chapter")
    ap.add_argument("--blueprint-file", default=BLUEPRINT_FILE, help="top-level document with the `{include 0 Module}` lines and the intro")
    ap.add_argument("--macros-file", default=MACROS_FILE)
    ap.add_argument("--roles-file", default=ROLES_FILE)
    ap.add_argument("--anchors", choices=["legacy", "none"], default="legacy",
                    help="explicit legacy numbers to verify (default: the six from the plan; `none` for fabricated inventories)")
    ap.add_argument("--site", help="generator output dir (contains html-multi/-verso-data/blueprint-manifest.json); enables manifest checks")
    ap.add_argument("--vbp", action="store_true", help="also run `vbp query stats` and `vbp query labels`")
    ap.add_argument("--vbp-nodes", action="store_true", help="with --vbp: also run `vbp query node <label>` for every label (slow)")
    ap.add_argument("--vbp-cmd", default="lake exe vbp", help='command prefix for the generator CLI (default "lake exe vbp")')
    ap.add_argument("--vbp-timeout", type=float, default=600.0)
    ap.add_argument("--max-diffs", type=int, default=15, help="max detail lines per check (0: unlimited)")
    ap.add_argument("--allow-option", action="append", default=[], help="directive option name to accept besides parent/uses")
    ap.add_argument("--verbose", "-v", action="store_true", help="also print details of passing checks")
    ap.add_argument("--json", help="write the results as JSON to this file")
    return ap


def main(argv: Optional[List[str]] = None) -> int:
    opts = build_parser().parse_args(argv)
    if not os.path.isfile(opts.inventory):
        print(f"error: inventory {opts.inventory} not found", file=sys.stderr)
        return 2
    try:
        results, ctx = run(opts)
    except (OSError, ValueError, KeyError) as e:
        print(f"error: cannot run the checks: {type(e).__name__}: {e}", file=sys.stderr)
        return 2
    print_report(results, opts, ctx)
    if opts.json:
        with open(opts.json, "w", encoding="utf-8") as fh:
            json.dump([c.__dict__ for c in results], fh, indent=1)
    return 1 if any(c.status == FAIL for c in results) else 0


if __name__ == "__main__":
    sys.exit(main())

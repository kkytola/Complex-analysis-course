#!/usr/bin/env python3
"""Bootstrap ``ComplexAnalysisCourse/Macros.lean`` from the legacy ``blueprint/src/macros/common.tex``.

Math macros are copied verbatim (grouped by theme, original order kept inside a theme); text-mode macros
(``\\term``, ``\\Palka``, ...) are not math macros and become Verso roles (``Roles.lean``) instead.
KaTeX built-ins clash with ``\\newcommand``; those are rewritten with ``\\def`` (works in KaTeX and LaTeX).

Usage: python3 -I scripts/migration/extract_macros.py [--src blueprint/src/macros/common.tex] [--usage blueprint/src]
"""
import argparse
import re
import sys
from pathlib import Path

TEXT_MACROS = {"term", "Palka", "MetSpCourse", "thmref", "thmdref", "lemref", "lemdref", "defref", "defdref"}
KATEX_CLASH = {"set"}  # KaTeX builtins: use \def (verified: KaTeX + LaTeX both accept it)

THEMES = [
    ("Number systems, real and imaginary parts, conjugation",
     ["bN", "bZ", "bQ", "bK", "bR", "bC", "re", "im", "ii", "cconj"]),
    ("Sets, balls, discs, annuli, boundaries and closures",
     ["set", "Tri", "Squ", "Rect", "Ball", "CBall", "PBall", "Sphere", "BallRC", "CBallRC", "PBallRC",
      "SphereRC", "Disk", "CDisk", "PDisk", "DiskRC", "CDiskRC", "PDiskRC", "Ann", "AnnRRC", "Domain",
      "bdry", "closOf"]),
    ("Calculus: differentials, partial derivatives, smoothness classes",
     ["ud", "eps", "pder", "pdder", "pmder", "pderof", "pdderof", "pmderof", "Cont", "ContDiff", "Smooth"]),
    ("Paths and winding numbers", ["opp", "concat", "windNsym", "windN"]),
    ("Residues", ["Res", "ResAt", "ResAtOf"]),
    ("Branches of argument and logarithm", ["Arg", "Log", "modtwopi"]),
    ("Uniform convergence on compacts and metric spaces", ["UOC", "genmet", "genspace"]),
]


def strip_comments(t):
    return re.sub(r"(?<!\\)%[^\n]*", "", t)


def parse_macros(text):
    out = []
    for m in re.finditer(r"\\newcommand\{\\([A-Za-z]+)\}(?:\[(\d)\])?\{", text):
        i = m.end()
        depth, j = 1, i
        while depth:
            c = text[j]
            if c == "{" and text[j - 1] != "\\":
                depth += 1
            elif c == "}" and text[j - 1] != "\\":
                depth -= 1
            j += 1
        out.append((m.group(1), int(m.group(2) or 0), text[i:j - 1]))
    return out


def render(name, nargs, body):
    if name in KATEX_CLASH:
        params = "".join(f"#{k + 1}" for k in range(nargs))
        return f"\\def\\{name}{params}{{{body}}}"
    arg = f"[{nargs}]" if nargs else ""
    return f"\\newcommand{{\\{name}}}{arg}{{{body}}}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="blueprint/src/macros/common.tex")
    ap.add_argument("--usage", default="blueprint/src")
    ap.add_argument("-o", "--output", default="ComplexAnalysisCourse/Macros.lean")
    args = ap.parse_args()
    macros = {n: (n, a, b) for n, a, b in parse_macros(strip_comments(Path(args.src).read_text(encoding="utf8")))}
    math = {n: v for n, v in macros.items() if n not in TEXT_MACROS}
    corpus = "".join(strip_comments(p.read_text(encoding="utf8")) for p in Path(args.usage).glob("*.tex"))
    used = lambda n: re.search(r"\\" + n + r"(?![A-Za-z])", corpus) is not None
    chunks, placed = [], set()
    for title, names in THEMES:
        names = [n for n in names if n in math]
        placed.update(names)
        chunks.append((title, [math[n] for n in names]))
    rest = [v for n, v in math.items() if n not in placed]
    chunks.append(("Not used by the current text (left over from an earlier project); kept so that old "
                   "formulae keep working - prune freely", rest))
    lines = [
        "import Verso", "import VersoManual", "import VersoBlueprint", "",
        "open Informal", "",
        "/-!", "# TeX macros for all formulae of the course skeleton", "",
        "This is the one place for LaTeX math macros. Every chapter imports this module.",
        "Each `tex_prelude` chunk is passed to KaTeX (HTML) and to the LaTeX preamble (PDF).", "",
        "* Add or edit macros here and nowhere else; keep one theme per chunk.",
        "* Macros are ordinary LaTeX (`\\newcommand`). KaTeX built-ins such as `\\set` cannot be redefined with",
        "  `\\newcommand`: use `\\def` (works in KaTeX and LaTeX). Unsupported things (e.g. `\\mathbbm`) are",
        "  reported as `KaTeX rejected blueprint math` by `lake build`.",
        "* A chunk is a raw string `r#\"...\"#`; it must not contain the character sequence `\"#`.",
        "* After editing, run `python3 scripts/gen_macro_gallery.py` and `lake build`: the gallery module",
        "  uses every macro once, so a broken macro is reported there.",
        "-/", "",
    ]
    for title, ms in chunks:
        if not ms:
            continue
        body = "\n".join(render(*m) for m in ms)
        assert '"#' not in body
        lines += [f"-- {title}", 'tex_prelude', f'  r#"{body}"#', ""]
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text("\n".join(lines), encoding="utf8")
    print(f"{len(math)} math macros ({len(rest)} unused) -> {args.output}; unused: {[m[0] for m in rest]}")


if __name__ == "__main__":
    sys.exit(main())

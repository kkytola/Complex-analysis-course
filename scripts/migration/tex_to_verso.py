#!/usr/bin/env python3
"""Deterministic TeX -> Verso Blueprint converter for the Complex-analysis-course blueprint.

Reads the legacy leanblueprint sources (``blueprint/src/content.tex`` and the files it ``\\input``s)
and writes one Verso module per chapter plus ``label_map.json`` and ``report.md``.  The translation
rules are those of section 7 of ``plan_migration_to_verso_blueprint.md``; the hand-written golden
sample is ``ComplexAnalysisCourse/Chapters/ComplexNumbers.lean``.

Usage (standard library only):

    python3 -I scripts/migration/tex_to_verso.py --src blueprint/src --out DIR [--only 1,2,A]
                                                  [--appendix-prefix "Appendix: "]

``--only`` restricts which chapter modules are *written* (chapter numbers ``1``..``6``, ``A``, ``B``);
the whole source is always converted and checked, and ``label_map.json`` / ``report.md`` always
describe the whole source.

The converter FAILS CLOSED: any construct it does not know about (unknown command or environment in
text mode, display maths other than ``align*``, a dangling ``\\ref``/``\\uses`` target, ...) makes it
print ``file:line: message`` on stderr and exit with status 1; nothing is silently dropped.  The
output is deterministic (no timestamps, fixed ordering).
"""
from __future__ import annotations

import argparse
import bisect
import json
import re
import sys
import unicodedata
from pathlib import Path

# --------------------------------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------------------------------

#: TeX environment -> Verso directive name (kind = the ENVIRONMENT, never the label prefix).
NODE_ENV_KIND = {"definition": "definition", "lemma": "lemma_", "theorem": "theorem",
                 "corollary": "corollary"}
#: Word that the ``bpref`` role generates (and that legacy TeX writes before ``\ref``).
KIND_WORD = {"definition": "Definition", "lemma": "Lemma", "theorem": "Theorem",
             "corollary": "Corollary"}
LIST_ENVS = ("itemize", "enumerate", "description")
STRUCT_CMDS = {"section": 1, "subsection": 2}

#: chapter number (content.tex order; appendices are lettered), Lean module, group id.
CHAPTER_TABLE = [
    ("1", "ComplexNumbers", "grp_complex_numbers"),
    ("2", "ComplexDerivative", "grp_complex_derivative"),
    ("3", "ContourIntegration", "grp_contour_integration"),
    ("4", "CauchyTheorem", "grp_cauchy_theorem"),
    ("5", "PowerSeries", "grp_power_series"),
    ("6", "Singularities", "grp_singularities"),
    ("A", "TopologyBackground", "grp_topology_background"),
    ("B", "CalculusBackground", "grp_calculus_background"),
]

MODULE_HEADER = """import Verso
import VersoManual
import VersoBlueprint
import ComplexAnalysisCourse.Macros
import ComplexAnalysisCourse.Roles

open Verso.Genre
open Verso.Genre.Manual
open Informal
"""

#: report categories, in the order in which they appear in report.md
CAT_REFFIX = "reffix"
CAT_KIND = "kind"
CAT_LIST = "list"
CAT_OTHER = "other"

NBSP = "\u00a0"
WS = " \t\n\r"

# --------------------------------------------------------------------------------------------------
# Errors and source handling
# --------------------------------------------------------------------------------------------------


class ConvError(Exception):
    """Fail-closed error carrying a ``file:line`` location."""

    def __init__(self, file: str, line: int, msg: str):
        super().__init__(f"{file}:{line}: {msg}")
        self.file, self.line, self.msg = file, line, msg


def find_comment(line: str) -> int:
    """Index of the first unescaped ``%`` in ``line`` (or -1)."""
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        if c == "\\":
            i += 2
            continue
        if c == "%":
            return i
        i += 1
    return -1


def strip_comments(raw: str):
    """Remove TeX comments.  Returns ``(text, linemap)``.

    TeX semantics are followed where they matter for the structure of the text: a line that
    consists only of a comment vanishes completely (it does NOT create a paragraph break), a
    trailing comment preceded by whitespace leaves the line break, and a trailing comment glued to
    non-space text also swallows the line break and the leading blanks of the next line.  ``linemap[k]``
    is the original 1-based line number of the k-th line of the stripped text.
    """
    out: list[str] = []
    linemap: list[int] = []
    glued = False
    for no, line in enumerate(raw.split("\n"), 1):
        k = find_comment(line)
        has = k >= 0
        content = line[:k] if has else line
        if glued:
            if content.strip(" \t") == "" and not has:      # blank line after a glued comment
                out.append("")
                linemap.append(no)
                glued = False
                continue
            out[-1] += content.lstrip(" \t")
            glued = has and out[-1] != "" and out[-1][-1] not in " \t"
            continue
        if has and content.strip(" \t") == "":              # comment-only line: vanishes
            continue
        out.append(content)
        linemap.append(no)
        glued = has and content != "" and content[-1] not in " \t"
    return "\n".join(out), linemap


class Src:
    """A comment-stripped TeX source file with line-number mapping back to the original."""

    def __init__(self, name: str, raw: str):
        self.name = name
        self.raw = raw
        self.text, self.linemap = strip_comments(raw)
        self._nl = [m.start() for m in re.finditer("\n", self.text)]

    def line(self, pos: int) -> int:
        idx = bisect.bisect_left(self._nl, pos)
        return self.linemap[min(idx, len(self.linemap) - 1)] if self.linemap else 1


# --------------------------------------------------------------------------------------------------
# Conversion context (label table, notices, placeholders)
# --------------------------------------------------------------------------------------------------

DISP_RE = re.compile("\x00D(\\d+)\x00")
DISP_SPLIT = re.compile("(\x00D\\d+\x00)")
REF_RE = re.compile("\x00R(\\d+)\x00")
LABEL_RE = re.compile(r"^[A-Za-z0-9_:]+$")
KINDWORD_RE = re.compile(r"(?<![A-Za-z])(Lemma|Theorem|Corollary|Definition)(?:~|[ \t\n]+)\Z")
CMD_RE = re.compile(r"\\([A-Za-z]+|[^A-Za-z])", re.S)
OPENER_RE = re.compile(r"^(?:[*+\-](?: |$)|\d+[.)](?: |$)|: |:{3,}|`{3,}|%%%|>|#)")

ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303",
           "=": "\u0304", ".": "\u0307", "c": "\u0327", "v": "\u030c", "u": "\u0306",
           "H": "\u030b"}
ACCENT_LETTER_CMDS = ("c", "v", "u", "H")


def label_to_verso(label: str) -> str:
    """Decision D4: ``kind:name`` -> ``kind_name`` (every ``:`` becomes ``_``, case kept)."""
    return label.replace(":", "_")


class Ctx:
    """Shared state of one conversion run."""

    def __init__(self, labels=None):
        #: TeX label -> {"env": ..., "file": ..., "line": ..., "verso": ...}
        self.labels: dict = labels if labels is not None else {}
        self.notices: list = []          # (category, file, line, message)
        self.displays: list[str] = []
        self.refs: list[dict] = []

    def notice(self, cat: str, file: str, line: int, msg: str) -> None:
        self.notices.append((cat, file, line, msg))

    # -- label resolution (used for \uses and \ref targets) --------------------------------------
    def resolve_label(self, label: str, file: str, line: int, what: str) -> str:
        """Return the existing TeX label for ``label`` (exact or the unique case-insensitive match)."""
        if label in self.labels:
            return label
        cands = [l for l in self.labels if l.lower() == label.lower()]
        if len(cands) == 1:
            self.notice(CAT_REFFIX, file, line,
                        f"{what}{{{label}}} points to a non-existing label; using the unique "
                        f"case-insensitive match `{cands[0]}` instead (source defect, fixed in the port)")
            return cands[0]
        if len(cands) > 1:
            raise ConvError(file, line, f"{what}{{{label}}}: dangling target, and several labels match "
                            f"case-insensitively ({', '.join(cands)})")
        raise ConvError(file, line, f"{what}{{{label}}}: dangling target (no such label)")

    def resolve_refs(self, text: str) -> str:
        """Replace ``\\ref`` placeholders by ``{bpref "label"}[]`` (and report kind-word mismatches)."""
        def sub(m):
            r = self.refs[int(m.group(1))]
            target = self.resolve_label(r["label"], r["file"], r["line"], "\\ref")
            env = self.labels[target]["env"]
            if KIND_WORD[env] != r["word"]:
                self.notice(CAT_KIND, r["file"], r["line"],
                            f"`{r['form']}{{{r['label']}}}`: the source says \"{r['word']}\" but `{target}` "
                            f"is a {env}; the generated reference text will say \"{KIND_WORD[env]}\"")
            return '{bpref "' + label_to_verso(target) + '"}[]'
        return REF_RE.sub(sub, text)


# (Ctx.resolve_refs is attached below, after KIND_WORD/REF_RE are known.)

# --------------------------------------------------------------------------------------------------
# Small formatting helpers
# --------------------------------------------------------------------------------------------------


def collapse_ws(s: str) -> str:
    """Collapse all TeX whitespace (including newlines) to single spaces and strip."""
    return re.sub(r"[ \t\n\r]+", " ", s).strip(" ")


def fmt_inline_math(body: str) -> str:
    """``$...$`` -> ``$`...```: whitespace collapsed, content otherwise byte-for-byte."""
    m = collapse_ws(body)
    if not m:
        raise ValueError("empty inline math")
    longest = max((len(x) for x in re.findall(r"`+", m)), default=0)
    fence = "`" * (longest + 1)
    if longest and (m.startswith("`") or m.endswith("`")):
        m = " " + m + " "
    return "$" + fence + m + fence


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


# --------------------------------------------------------------------------------------------------
# Parser: TeX text -> blocks (with inline content already rendered to Verso text)
# --------------------------------------------------------------------------------------------------


class Parser:
    """Recursive-descent parser over one comment-stripped TeX source."""

    def __init__(self, src: Src, ctx: Ctx):
        self.src = src
        self.s = src.text
        self.n = len(self.s)
        self.i = 0
        self.ctx = ctx
        self.tilde = NBSP      # what ``~`` becomes in text (a plain space inside ``\Palka``)

    # -- diagnostics -----------------------------------------------------------------------------
    def line(self, pos=None) -> int:
        return self.src.line(self.i if pos is None else pos)

    def fail(self, msg: str, pos=None):
        raise ConvError(self.src.name, self.line(pos), msg)

    def notice(self, cat: str, msg: str, pos=None) -> None:
        self.ctx.notice(cat, self.src.name, self.line(pos), msg)

    # -- low-level scanning ----------------------------------------------------------------------
    def skip_ws(self) -> None:
        while self.i < self.n and self.s[self.i] in WS:
            self.i += 1

    def looking_at_cmd(self, name: str) -> bool:
        j = self.i + 1 + len(name)
        return (self.s.startswith("\\" + name, self.i)
                and not (j < self.n and self.s[j].isalpha()))

    def group_raw(self) -> str:
        """Read a balanced ``{...}`` argument and return its raw text."""
        self.skip_ws()
        if self.i >= self.n or self.s[self.i] != "{":
            self.fail("expected '{' (command argument)")
        j = self.i + 1
        depth = 1
        while j < self.n:
            c = self.s[j]
            if c == "\\":
                j += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        else:
            self.fail("unterminated '{' argument")
        raw = self.s[self.i + 1:j]
        self.i = j + 1
        return raw

    def group_inline(self, tilde=None) -> str:
        """Read a ``{...}`` argument and convert its contents (inline context only)."""
        self.skip_ws()
        if self.i >= self.n or self.s[self.i] != "{":
            self.fail("expected '{' (command argument)")
        start = self.i
        self.i += 1
        saved = self.tilde
        if tilde is not None:
            self.tilde = tilde
        try:
            out, _term = self.inline_until("}", False)
        finally:
            self.tilde = saved
        if self.i >= self.n or self.s[self.i] != "}":
            self.fail("unterminated '{' argument", start)
        self.i += 1
        return "".join(out)

    def read_env_name(self, j: int):
        """Parse ``{name}`` starting at ``j`` (after ``\\begin``/``\\end``); returns (name, new_pos)."""
        while j < self.n and self.s[j] in " \t":
            j += 1
        if j >= self.n or self.s[j] != "{":
            self.fail("expected '{environment}'", j)
        k = self.s.find("}", j)
        if k < 0:
            self.fail("unterminated environment name", j)
        return self.s[j + 1:k].strip(), k + 1

    # -- text rendering --------------------------------------------------------------------------
    def render_text(self, raw: str, pos: int) -> str:
        """Plain TeX text -> Verso text (ligatures, ``~``, escaping of Verso-special characters)."""
        out = []
        i = 0
        n = len(raw)
        while i < n:
            c = raw[i]
            if raw.startswith("---", i):
                out.append("\u2014"); i += 3
            elif raw.startswith("--", i):
                out.append("\u2013"); i += 2
            elif raw.startswith("``", i):
                out.append("\u201c"); i += 2
            elif raw.startswith("''", i):
                out.append("\u201d"); i += 2
            elif c == "~":
                out.append(self.tilde); i += 1
            elif c in "*[]{}$":
                out.append("\\" + c); i += 1
            elif c == "`":
                self.fail("a single backtick in text mode is not supported", pos)
            elif c in "_^#&":
                self.fail(f"unescaped {c!r} in text mode (TeX would reject it)", pos)
            else:
                out.append(c); i += 1
        return "".join(out)

    def make_ref(self, label: str, word: str, form: str, pos: int) -> str:
        idx = len(self.ctx.refs)
        self.ctx.refs.append({"label": label, "word": word, "form": form,
                              "file": self.src.name, "line": self.line(pos)})
        return f"\x00R{idx}\x00"

    def read_math(self) -> str:
        s = self.s
        i = self.i
        if s.startswith("$$", i):
            self.fail("display maths in $$...$$ form is not supported (only align*)")
        j = i + 1
        depth = 0                      # a '$' inside braces (e.g. \\text{if $x$}) is nested maths
        while j < self.n:
            c = s[j]
            if c == "\\":
                j += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            elif c == "$" and depth <= 0:
                break
            j += 1
        else:
            self.fail("unterminated inline math")
        body = s[i + 1:j]
        if re.search(r"\n[ \t]*\n", body):
            self.fail("blank line inside inline math")
        try:
            out = fmt_inline_math(body)
        except ValueError:
            self.fail("empty inline math '$$'")
        if "`" in body:
            self.notice(CAT_OTHER, "inline math contains a backtick; emitted with a longer backtick fence")
        self.i = j + 1
        return out

    def read_display(self, begin_pos: int, j: int) -> str:
        """``\\begin{align*}`` ... ``\\end{align*}`` -> display placeholder (``j`` is after the begin)."""
        s = self.s
        end_tok = "\\end{align*}"
        e = s.find(end_tok, j)
        if e < 0:
            self.fail("missing \\end{align*}", begin_pos)
        end = e + len(end_tok)
        raw = s[begin_pos:end]
        if "`" in raw:
            self.fail("backtick inside display maths", begin_pos)
        ls = s.rfind("\n", 0, begin_pos) + 1
        prefix = s[ls:begin_pos]
        indent = len(prefix) if prefix.strip(" \t") == "" else len(prefix) - len(prefix.lstrip(" \t"))
        out = []
        dropped = 0
        for k, ln in enumerate(raw.split("\n")):
            ln = ln.rstrip(" \t\r")
            if ln.strip(" \t") == "":
                dropped += 1
                continue
            if k > 0:
                lead = len(ln) - len(ln.lstrip(" \t"))
                ln = ln[min(lead, indent):]
            out.append(ln)
        if dropped:
            self.notice(CAT_OTHER, f"{dropped} blank line(s) inside an align* environment dropped "
                        "(not allowed by TeX; blank lines would end the Verso paragraph)", begin_pos)
        self.i = end
        idx = len(self.ctx.displays)
        self.ctx.displays.append("$$`\n" + "\n".join(out) + "\n`")
        return f"\x00D{idx}\x00"

    # -- inline content --------------------------------------------------------------------------
    def inline_until(self, stop: str, allow_block: bool, title: dict | None = None):
        """Parse inline content.

        Stops, without consuming, at the unescaped ``stop`` character, at the end of input, or (when
        ``allow_block``) at a block-level command.  Returns ``(pieces, terminator)`` where the
        terminator is ``None`` (end of input / stop char) or a tuple describing the block-level
        command that was peeked: ``("begin", env, pos)``, ``("end", env, pos)``, ``("item", pos)``,
        ``("struct", name, pos)``.
        """
        s = self.s
        out: list[str] = []
        buf: list[str] = []
        state = {"start": self.i}

        def flush():
            if buf:
                out.append(self.render_text("".join(buf), state["start"]))
                del buf[:]

        while self.i < self.n:
            c = s[self.i]
            if stop and c == stop:
                break
            if c == "}":
                self.fail("unbalanced '}'")
            if c == "{":
                self.fail("bare '{...}' group in text mode is not supported")
            if c == "$":
                flush()
                out.append(self.read_math())
                state["start"] = self.i
                continue
            if c == "\\":
                term = self.command(out, buf, flush, allow_block, title)
                if term is not None:
                    return out, term
                state["start"] = self.i
                continue
            if not buf:
                state["start"] = self.i
            buf.append(c)
            self.i += 1
        flush()
        return out, None

    def command(self, out, buf, flush, allow_block, title):
        """Handle a backslash command at the current position.  Returns a terminator or None."""
        s = self.s
        start = self.i
        m = CMD_RE.match(s, start)
        if not m:
            self.fail("dangling backslash")
        name = m.group(1)
        j = m.end()

        # ---- block-level commands ------------------------------------------------------------
        if name in ("begin", "end"):
            env, j2 = self.read_env_name(j)
            if name == "begin" and env == "align*":
                flush()
                if not allow_block:
                    self.fail("display maths (align*) inside a group/argument is not supported")
                out.append(self.read_display(start, j2))
                return None
            known = set(LIST_ENVS) | set(NODE_ENV_KIND) | {"proof"}
            if name == "begin" and env not in known:
                self.fail(f"unsupported environment \\begin{{{env}}} in text mode")
            if not allow_block:
                self.fail(f"unexpected \\{name}{{{env}}} inside an inline context")
            flush()
            return (name, env, start)
        if name == "item":
            if not allow_block:
                self.fail("\\item outside of a list item context")
            flush()
            return ("item", start)
        if name in STRUCT_CMDS:
            if not allow_block:
                self.fail(f"\\{name} inside an inline context")
            flush()
            return ("struct", name, start)

        # ---- text commands -------------------------------------------------------------------
        if name == "term":
            flush()
            self.i = j
            inner = self.group_inline()
            if not inner.strip(" \t\n"):
                self.fail("empty \\term{}", start)
            out.append("{term}[" + inner + "]")
            return None
        if name in ("emph", "textbf"):
            flush()
            self.i = j
            inner = self.group_inline()
            core = inner.strip(" \t\n")
            if not core:
                self.fail(f"empty \\{name}{{}}", start)
            mark = "_" if name == "emph" else "*"
            lead = inner[:len(inner) - len(inner.lstrip(" \t\n"))]
            trail = inner[len(inner.rstrip(" \t\n")):]
            out.append(lead + mark + core + mark + trail)
            return None
        if name == "Palka":
            flush()
            self.i = j
            inner = collapse_ws(self.group_inline(tilde=" "))
            if not inner:
                self.fail("empty \\Palka{}", start)
            if title is not None:
                if title.get("palka") is not None:
                    self.fail("two \\Palka{} in one title", start)
                title["palka"] = inner
                title["after"] = len(out)
            else:
                out.append("{palka}[" + inner + "]")
            return None
        if name in ("ldots", "MetSpCourse"):
            flush()
            self.i = j
            if s.startswith("{}", self.i):
                self.i += 2
            out.append("\u2026" if name == "ldots" else "{metSpCourse}[]")
            return None
        if name == "ref":
            self.i = j
            label = self.group_raw().strip()
            raw = "".join(buf)
            km = KINDWORD_RE.search(raw)
            if not km:
                self.fail(f"\\ref{{{label}}} is not preceded by a kind word "
                          "(Lemma~, Theorem~, Corollary~, Definition~)", start)
            del buf[:]
            buf.append(raw[:km.start()])
            flush()
            out.append(self.make_ref(label, km.group(1), f"{km.group(1)}~\\ref", start))
            return None
        if name in ("defref", "thmref", "lemref"):
            flush()
            self.i = j
            label = self.group_raw().strip()
            word = {"defref": "Definition", "thmref": "Theorem", "lemref": "Lemma"}[name]
            out.append(self.make_ref(label, word, "\\" + name, start))
            return None
        if name in ("label", "uses"):
            self.fail(f"\\{name} is only supported directly after \\begin{{...}} of a statement/proof")
        if name in "%&#$_{}" and len(name) == 1:
            flush()
            self.i = j
            lit = "%" if name == "%" else name
            out.append("\\" + lit if lit in "*[]{}$_" else lit)
            return None
        if name in ACCENTS and (len(name) == 1 or name in ACCENT_LETTER_CMDS):
            flush()
            self.i = j
            if name.isalpha():
                while self.i < self.n and s[self.i] in " \t":
                    self.i += 1
            if self.i < self.n and s[self.i] == "{":
                arg = self.group_raw().strip()
            elif self.i < self.n:
                arg = s[self.i]
                self.i += 1
            else:
                self.fail("accent command without argument", start)
            arg = {"\\i": "\u0131", "\\j": "\u0237"}.get(arg, arg)
            if len(arg) != 1 or not arg.isalpha():
                self.fail(f"unsupported accent argument {arg!r}", start)
            out.append(unicodedata.normalize("NFC", arg + ACCENTS[name]))
            return None
        shown = name if name.isalpha() else name.replace("\n", "\\n")
        self.fail(f"unsupported command \\{shown} in text mode", start)

    # -- blocks ----------------------------------------------------------------------------------
    def parse_blocks(self, stop_envs=(), item_stop=False, struct_stop=False):
        """Parse prose into blocks.  Returns ``(blocks, terminator)`` (terminator peeked, not consumed)."""
        blocks: list = []
        pieces: list[str] = []
        first = {"pos": self.i}

        def flush():
            text = "".join(pieces)
            del pieces[:]
            if text.strip(" \t\n"):
                p = first["pos"]
                while p < self.n and self.s[p] in WS:
                    p += 1
                blocks.append(("para", text, self.line(p)))

        while True:
            if not pieces:
                first["pos"] = self.i
            out, term = self.inline_until("", True)
            pieces.extend(out)
            if term is None:
                flush()
                return blocks, None
            kind = term[0]
            if kind == "begin" and term[1] in LIST_ENVS:
                flush()
                blocks.append(self.parse_list())
                continue
            if kind == "end" and term[1] in stop_envs:
                flush()
                return blocks, term
            if kind == "item" and item_stop:
                flush()
                return blocks, term
            if kind in ("begin", "struct") and struct_stop:
                flush()
                return blocks, term
            self.fail(self.describe_term(term), term[-1])

    @staticmethod
    def describe_term(term) -> str:
        if term[0] in ("begin", "end"):
            return f"unexpected \\{term[0]}{{{term[1]}}}"
        if term[0] == "struct":
            return f"unexpected \\{term[1]} here"
        return "unexpected \\item here"

    def parse_list(self):
        start = self.i
        env, j = self.read_env_name(self.i + len("\\begin"))
        self.i = j
        items = []
        pre, term = self.parse_blocks(stop_envs=(env,), item_stop=True)
        if pre:
            self.fail(f"text before the first \\item in {env}", start)
        while True:
            if term is None:
                self.fail(f"missing \\end{{{env}}}", start)
            if term[0] == "end":
                _e, self.i = self.read_env_name(self.i + len("\\end"))
                break
            ipos = self.i
            self.i += len("\\item")
            label = None
            k = self.i
            while k < self.n and self.s[k] in " \t\n":
                k += 1
            if k < self.n and self.s[k] == "[":
                self.i = k + 1
                out, _t = self.inline_until("]", False)
                if self.i >= self.n or self.s[self.i] != "]":
                    self.fail("unterminated \\item[...] label", ipos)
                self.i += 1
                label = collapse_ws("".join(out))
                if not label:
                    self.fail("empty \\item[] label", ipos)
            body, term = self.parse_blocks(stop_envs=(env,), item_stop=True)
            items.append((label, body, ipos))
        labels = [lab for lab, _b, _p in items if lab is not None]
        if labels:
            how = ("bold label (`* *LABEL* text`)" if env == "description"
                   else "plain label text (`* LABEL text`)")
            self.notice(CAT_LIST, f"`{env}` with explicit item labels {', '.join(labels)}: emitted as "
                        f"unordered bullets with the label as {how}", start)
        return ("list", env, items, self.line(start))

    # -- statements / proofs ---------------------------------------------------------------------
    def read_title(self):
        """Optional ``[Title \\Palka{..}]``; returns ``(title_text, palka_text)`` or ``(None, None)``."""
        self.skip_ws()
        if self.i >= self.n or self.s[self.i] != "[":
            return None, None
        start = self.i
        self.i += 1
        title = {"palka": None, "after": None}
        out, _t = self.inline_until("]", False, title)
        if self.i >= self.n or self.s[self.i] != "]":
            self.fail("unterminated optional title argument", start)
        self.i += 1
        if title["palka"] is not None:
            tail = "".join(out[title["after"]:])
            if tail.strip(" \t\n"):
                self.fail("text after \\Palka{..} in a title is not supported", start)
            out = out[:title["after"]]
        return collapse_ws("".join(out)), title["palka"]

    def read_header(self, allow_label: bool):
        label = None
        uses = None
        while True:
            self.skip_ws()
            if self.looking_at_cmd("label") and allow_label:
                if label is not None:
                    self.fail("two \\label in one environment")
                self.i += len("\\label")
                label = self.group_raw().strip()
            elif self.looking_at_cmd("uses"):
                if uses is not None:
                    self.fail("two \\uses in one environment")
                self.i += len("\\uses")
                uses = self.group_raw()
            else:
                break
        return label, uses

    def parse_node(self, env: str):
        start = self.i
        _e, self.i = self.read_env_name(self.i + len("\\begin"))
        title, palka = self.read_title()
        label, uses = self.read_header(allow_label=True)
        if label is None:
            self.fail(f"\\begin{{{env}}} without a \\label", start)
        if not LABEL_RE.match(label):
            self.fail(f"label {label!r} contains characters outside [A-Za-z0-9_:]", start)
        body, term = self.parse_blocks(stop_envs=(env,))
        if term is None:
            self.fail(f"missing \\end{{{env}}}", start)
        _e, self.i = self.read_env_name(self.i + len("\\end"))
        return {"type": "node", "env": env, "label": label, "title": title, "palka": palka,
                "uses": self.split_uses(uses), "body": body, "file": self.src.name,
                "line": self.line(start)}

    def parse_proof(self):
        start = self.i
        _e, self.i = self.read_env_name(self.i + len("\\begin"))
        self.skip_ws()
        if self.i < self.n and self.s[self.i] == "[":
            self.fail("\\begin{proof}[...] with an optional argument is not supported")
        label, uses = self.read_header(allow_label=False)
        body, term = self.parse_blocks(stop_envs=("proof",))
        if term is None:
            self.fail("missing \\end{proof}", start)
        _e, self.i = self.read_env_name(self.i + len("\\end"))
        return {"type": "proof", "uses": self.split_uses(uses), "body": body,
                "file": self.src.name, "line": self.line(start)}

    @staticmethod
    def split_uses(raw):
        if raw is None:
            return []
        return [x.strip() for x in raw.split(",") if x.strip()]

    def parse_file(self):
        """Top-level structure of a chapter file: headings, prose, statements and proofs."""
        items: list = []
        last_stmt = None
        while True:
            blocks, term = self.parse_blocks(struct_stop=True)
            if blocks:
                items.append({"type": "prose", "blocks": blocks})
                last_stmt = None
            if term is None:
                break
            if term[0] == "struct":
                self.i += len("\\" + term[1])
                self.skip_ws()
                if self.i < self.n and self.s[self.i] in "*[":
                    self.fail(f"\\{term[1]}* / \\{term[1]}[..] is not supported")
                pos = self.i
                text = collapse_ws(self.group_inline())
                if not text:
                    self.fail(f"empty \\{term[1]} title", pos)
                items.append({"type": "heading", "level": STRUCT_CMDS[term[1]], "text": text,
                              "file": self.src.name, "line": self.line(term[2])})
                last_stmt = None
            elif term[0] == "begin" and term[1] in NODE_ENV_KIND:
                node = self.parse_node(term[1])
                items.append(node)
                last_stmt = node
            elif term[0] == "begin" and term[1] == "proof":
                if last_stmt is None:
                    self.fail("\\begin{proof} does not immediately follow a statement environment")
                if last_stmt.get("has_proof"):
                    self.fail("second proof for the same statement")
                proof = self.parse_proof()
                proof["label"] = last_stmt["label"]
                last_stmt["has_proof"] = True
                if last_stmt["env"] == "definition":
                    self.ctx.notice(CAT_OTHER, proof["file"], proof["line"],
                                    f"proof attached to a definition ({last_stmt['label']})")
                items.append(proof)
            else:  # pragma: no cover - parse_blocks only returns the cases above
                self.fail(self.describe_term(term), term[-1])
        return items


# --------------------------------------------------------------------------------------------------
# Rendering: blocks -> lines
# --------------------------------------------------------------------------------------------------


class Renderer:
    def __init__(self, ctx: Ctx):
        self.ctx = ctx

    # -- paragraphs ------------------------------------------------------------------------------
    @staticmethod
    def isolate_displays(text: str) -> str:
        """Make every display placeholder occupy a line of its own."""
        res = ""
        for k, part in enumerate(DISP_SPLIT.split(text)):
            if k % 2 == 1:
                res = res.rstrip(" \t")
                if res and not res.endswith("\n"):
                    res += "\n"
                res += part
            else:
                if k > 0:
                    part = part.lstrip(" \t")
                    if part and not part.startswith("\n"):
                        part = "\n" + part
                res += part
        return res

    def para_lines(self, text: str, file: str = "?", line: int = 0):
        """One block of prose -> list of paragraphs, each a list of output lines."""
        text = self.isolate_displays(text)
        result = []
        for ptxt in re.split(r"\n[ \t]*\n(?:[ \t]*\n)*", text):
            lines: list[str] = []
            for raw in ptxt.split("\n"):
                ln = re.sub(r"[ \t]+", " ", raw).strip(" \t")
                if not ln:
                    continue
                is_disp = DISP_RE.fullmatch(ln) is not None
                if (not is_disp and OPENER_RE.match(ln)):
                    prev_is_text = bool(lines) and DISP_RE.fullmatch(lines[-1]) is None
                    if prev_is_text:
                        lines[-1] += " " + ln
                        self.ctx.notice(CAT_OTHER, file, line,
                                        f"line starting with a Verso block opener joined to the previous "
                                        f"line: `{ln[:40]}`")
                        continue
                    self.ctx.notice(CAT_OTHER, file, line,
                                    f"paragraph starting with a Verso block opener escaped: `{ln[:40]}`")
                    ln = "\\" + ln
                lines.append(ln)
            if not lines:
                continue
            expanded: list[str] = []
            for ln in lines:
                m = DISP_RE.fullmatch(ln)
                if m:
                    expanded.extend(self.ctx.displays[int(m.group(1))].split("\n"))
                else:
                    expanded.append(ln)
            result.append(expanded)
        return result

    # -- blocks ----------------------------------------------------------------------------------
    def render_blocks(self, blocks, file: str = "?", line: int = 0):
        lines: list[str] = []
        for b in blocks:
            if b[0] == "para":
                for p in self.para_lines(b[1], file, b[2]):
                    if lines:
                        lines.append("")
                    lines.extend(p)
            else:
                if lines:
                    lines.append("")
                lines.extend(self.render_list(b, file))
        return lines

    def render_list(self, lst, file: str):
        _tag, env, items, _line = lst
        labelled = any(lab is not None for lab, _b, _p in items)
        out: list[str] = []
        for lab, body, ipos in items:
            if labelled or env != "enumerate":
                bullet = "* "
            else:
                bullet = "1. "
            body_lines = self.render_blocks(body, file)
            if lab is not None:
                lab_text = f"*{lab}*" if env == "description" else lab
                if body_lines:
                    body_lines[0] = lab_text + " " + body_lines[0]
                else:
                    body_lines = [lab_text]
            if not body_lines:
                body_lines = [""]
            out.append(bullet + body_lines[0])
            for ln in body_lines[1:]:
                out.append(("  " + ln) if ln else "")
        return out


# --------------------------------------------------------------------------------------------------
# Whole-run conversion
# --------------------------------------------------------------------------------------------------


class Chapter:
    def __init__(self, number, module, group, title_raw, files):
        self.number = number
        self.module = module
        self.group = group
        self.title_raw = title_raw
        self.files = files            # list of file names (in \input order)
        self.items: list = []         # filled by parsing
        self.title = ""               # converted (Verso-escaped) title


def parse_content(src_dir: Path):
    """Chapters (in order) of ``content.tex``: ``[(title_raw, [files], is_appendix)]``."""
    path = src_dir / "content.tex"
    src = Src("content.tex", path.read_text(encoding="utf8"))
    p = Parser(src, Ctx())
    s = src.text
    chapters = []
    appendix = False
    seen_chapter = False
    while p.i < p.n:
        k = s.find("\\", p.i)
        if k < 0:
            rest = s[p.i:]
            if seen_chapter and rest.strip():
                p.fail("text after the last \\input in content.tex")
            break
        before = s[p.i:k]
        if seen_chapter and before.strip():
            p.fail("text between chapters in content.tex is not supported", p.i)
        p.i = k
        m = re.compile(r"\\([A-Za-z]+)").match(s, k)
        if not m:
            p.fail("unexpected backslash sequence in content.tex")
        name = m.group(1)
        p.i = m.end()
        if name == "chapter":
            title_raw = p.group_raw()
            chapters.append([title_raw, [], appendix])
            seen_chapter = True
        elif name == "appendix":
            appendix = True
        elif name == "input":
            if not seen_chapter:
                p.fail("\\input before the first \\chapter")
            f = p.group_raw().strip()
            chapters[-1][1].append(f if f.endswith(".tex") else f + ".tex")
        elif not seen_chapter:
            # the introductory text before the first \chapter (\emph etc.) is not converted here
            continue
        else:
            p.fail(f"unsupported command \\{name} in content.tex")
    return chapters


def scan_commented_environments(src: Src):
    """Commented-out statement environments (whole blocks starting with ``%\\begin{lemma}`` etc.)."""
    found = []
    lines = src.raw.split("\n")
    pat = re.compile(r"^\s*%+\s*\\begin\{(definition|lemma|theorem|corollary)\}(.*)$")
    i = 0
    while i < len(lines):
        m = pat.match(lines[i])
        if not m:
            i += 1
            continue
        env = m.group(1)
        end_pat = re.compile(r"^\s*%+\s*\\end\{" + env + r"\}")
        j = i
        while j < len(lines) and not end_pat.match(lines[j]):
            j += 1
        last = min(j, len(lines) - 1)
        block = lines[i:last + 1]
        label = None
        for ln in block:
            lm = re.search(r"\\label\{([^}]*)\}", ln)
            if lm:
                label = lm.group(1)
                break
        title = None
        tm = re.search(r"\[(.*)\]", m.group(2))
        if tm:
            title = tm.group(1)
        has_proof = False
        k = last + 1
        if k < len(lines) and re.match(r"^\s*%+\s*\\begin\{proof\}", lines[k]):
            pend = re.compile(r"^\s*%+\s*\\end\{proof\}")
            while k < len(lines) and not pend.match(lines[k]):
                k += 1
            last = min(k, len(lines) - 1)
            has_proof = True
        found.append({"file": src.name, "line": i + 1, "last": last + 1, "env": env, "label": label,
                      "title": title, "has_proof": has_proof})
        i = last + 1
    return found


class Converter:
    """Converts the whole blueprint source tree."""

    def __init__(self, src_dir: Path, appendix_prefix: str = "Appendix: "):
        self.src_dir = Path(src_dir)
        self.appendix_prefix = appendix_prefix
        self.ctx = Ctx()
        self.chapters: list[Chapter] = []
        self.sources: dict[str, Src] = {}
        self.commented: list = []

    # -- phase 1: parse everything -----------------------------------------------------------------
    def load(self):
        spec = parse_content(self.src_dir)
        if len(spec) != len(CHAPTER_TABLE):
            raise ConvError("content.tex", 1, f"expected {len(CHAPTER_TABLE)} chapters, found {len(spec)}")
        for (title_raw, files, is_app), (num, module, group) in zip(spec, CHAPTER_TABLE):
            if is_app != num.isalpha():
                raise ConvError("content.tex", 1, f"chapter {num}: appendix flag does not match the table")
            if not files:
                raise ConvError("content.tex", 1, f"chapter {num} has no \\input")
            ch = Chapter(num, module, group, title_raw, files)
            ptitle = Parser(Src("content.tex", title_raw), self.ctx)
            out, _t = ptitle.inline_until("", False)
            ch.title = collapse_ws("".join(out))
            self.chapters.append(ch)
        for ch in self.chapters:
            for f in ch.files:
                path = self.src_dir / f
                if not path.is_file():
                    raise ConvError("content.tex", 1, f"\\input file {f} does not exist")
                src = Src(f, path.read_text(encoding="utf8"))
                self.sources[f] = src
                self.commented.extend(scan_commented_environments(src))
                parser = Parser(src, self.ctx)
                ch.items.extend(parser.parse_file())
        self.register_labels()

    def register_labels(self):
        verso_seen: dict[str, str] = {}
        for ch in self.chapters:
            for it in ch.items:
                if it["type"] != "node":
                    continue
                lab = it["label"]
                if lab in self.ctx.labels:
                    raise ConvError(it["file"], it["line"], f"duplicate label {lab!r}")
                v = label_to_verso(lab)
                if v in verso_seen:
                    raise ConvError(it["file"], it["line"],
                                    f"labels {verso_seen[v]!r} and {lab!r} collide after ':' -> '_'")
                verso_seen[v] = lab
                self.ctx.labels[lab] = {"env": it["env"], "file": it["file"], "line": it["line"],
                                        "verso": v, "chapter": ch.number}

    # -- phase 2: render ---------------------------------------------------------------------------
    def resolve_uses(self, node) -> list[str]:
        out = []
        for l in node["uses"]:
            t = self.ctx.resolve_label(l, node["file"], node["line"], "\\uses")
            out.append(label_to_verso(t))
        return out

    def render_item(self, rend: Renderer, ch: Chapter, it) -> list[str]:
        typ = it["type"]
        if typ == "heading":
            return ["#" * it["level"] + " " + it["text"]]
        if typ == "prose":
            return rend.render_blocks(it["blocks"])
        if typ == "node":
            return self.render_node(rend, ch, it)
        if typ == "proof":
            return self.render_proof(rend, it)
        raise AssertionError(typ)

    def render_node(self, rend: Renderer, ch: Chapter, node) -> list[str]:
        kind = NODE_ENV_KIND[node["env"]]
        head = f':::{kind} "{label_to_verso(node["label"])}" (parent := "{ch.group}")'
        uses = self.resolve_uses(node)
        if uses:
            head += f' (uses := "{", ".join(uses)}")'
        lines = [head]
        title, palka = node["title"], node["palka"]
        lead = []
        if title:
            lead.append("{nodetitle}[" + title + "]")
        if palka:
            lead.append("{palka}[" + palka + "]")
        if title is None and palka is None:
            self.ctx.notice(CAT_OTHER, node["file"], node["line"],
                            f"`{node['label']}` has no optional [Title] argument (no lead-in paragraph emitted)")
        elif not lead:
            self.ctx.notice(CAT_OTHER, node["file"], node["line"],
                            f"`{node['label']}` has an empty [] title (no lead-in paragraph emitted)")
        body = rend.render_blocks(node["body"], node["file"], node["line"])
        if lead:
            lines.append(" ".join(lead))
            if body:
                lines.append("")
        lines.extend(body)
        lines.append(":::")
        return lines

    def render_proof(self, rend: Renderer, proof) -> list[str]:
        head = f':::proof "{label_to_verso(proof["label"])}"'
        uses = self.resolve_uses(proof)
        if uses:
            head += f' (uses := "{", ".join(uses)}")'
        body = rend.render_blocks(proof["body"], proof["file"], proof["line"])
        if not body:
            raise ConvError(proof["file"], proof["line"], f"proof of {proof['label']} has an empty body")
        return [head] + body + [":::"]

    def render_chapter(self, ch: Chapter) -> str:
        rend = Renderer(self.ctx)
        doc_title = (self.appendix_prefix if ch.number.isalpha() else "") + ch.title
        chunks: list[list[str]] = [[
            ":::group " + lean_string(ch.group), ch.title, ":::"]]
        for it in ch.items:
            chunks.append(self.render_item(rend, ch, it))
        body = "\n\n".join("\n".join(c) for c in chunks if c)
        body = self.ctx.resolve_refs(body)
        if "\x00" in body:  # pragma: no cover - internal consistency check
            raise ConvError(ch.files[0], 1, "internal error: unresolved placeholder in the output")
        return (MODULE_HEADER + "\n#doc (Manual) " + lean_string(doc_title) + " =>\n\n" + body + "\n")

    # -- report ------------------------------------------------------------------------------------
    def label_map(self) -> dict:
        return {l: info["verso"] for l, info in self.ctx.labels.items()}

    def counts(self) -> dict:
        by_kind = {k: 0 for k in NODE_ENV_KIND}
        proofs = sections = subsections = palka = 0
        stmt_edges = proof_edges = 0
        for ch in self.chapters:
            for it in ch.items:
                if it["type"] == "node":
                    by_kind[it["env"]] += 1
                    stmt_edges += len(it["uses"])
                    if it["palka"]:
                        palka += 1
                elif it["type"] == "proof":
                    proofs += 1
                    proof_edges += len(it["uses"])
                elif it["type"] == "heading":
                    if it["level"] == 1:
                        sections += 1
                    else:
                        subsections += 1
        return {"nodes": sum(by_kind.values()), "by_kind": by_kind, "proofs": proofs,
                "statement_edges": stmt_edges, "proof_edges": proof_edges,
                "sections": sections, "subsections": subsections, "palka": palka}

    def report(self, written: list[str], only, rendered: dict | None = None) -> str:
        c = self.counts()
        n = self.ctx.notices
        rendered = rendered or {}
        out: list[str] = ["# TeX to Verso conversion report", ""]
        out.append("Generated by `scripts/migration/tex_to_verso.py` (deterministic; no timestamps).")
        out.append("")
        out.append("## Summary")
        out.append("")
        out.append(f"* Chapters converted: {len(self.chapters)}; modules written: {', '.join(written) or 'none'}"
                   + (f" (`--only {','.join(only)}`)" if only else ""))
        bk = c["by_kind"]
        out.append(f"* Nodes: {c['nodes']} (definitions {bk['definition']}, lemmas {bk['lemma']}, "
                   f"theorems {bk['theorem']}, corollaries {bk['corollary']}); proofs: {c['proofs']}")
        out.append(f"* `\\uses` edges: {c['statement_edges']} on statements, {c['proof_edges']} on proofs")
        out.append(f"* Sections: {c['sections']}, subsections: {c['subsections']}; titles with `\\Palka`: {c['palka']}")
        out.append(f"* `\\ref`/`\\defref` converted to `{{bpref}}`: {len(self.ctx.refs)}")
        out.append(f"* Commented-out statement environments dropped: {len(self.commented)}")
        if rendered:
            allout = "\n".join(rendered.values())
            roles = [("nodetitle", "{nodetitle}["), ("palka", "{palka}["), ("term", "{term}["),
                     ("metSpCourse", "{metSpCourse}[]"), ("bpref", "{bpref \"")]
            out.append("* Role uses in the generated modules: "
                       + ", ".join(f"`{{{name}}}` {allout.count(pat)}" for name, pat in roles))
        out.append("* Not converted here: the introductory paragraphs of `content.tex` (they live in "
                   "`ComplexAnalysisCourse/Blueprint.lean`); `course_overview.tex` is not `\\input` anywhere.")
        out.append("")
        out.append("## Chapter to module mapping")
        out.append("")
        out.append("| Ch. | Title | Module | TeX files | Nodes | Proofs |")
        out.append("|---|---|---|---|---|---|")
        for ch in self.chapters:
            nn = sum(1 for it in ch.items if it["type"] == "node")
            pp = sum(1 for it in ch.items if it["type"] == "proof")
            out.append(f"| {ch.number} | {ch.title} | `{ch.module}` | {', '.join(ch.files)} | {nn} | {pp} |")
        out.append("")

        def section(title, cat, empty):
            out.append("## " + title)
            out.append("")
            rows = [x for x in n if x[0] == cat]
            if not rows:
                out.append(empty)
            for _c, f, l, msg in rows:
                out.append(f"* `{f}:{l}`: {msg}")
            out.append("")

        section("Reference fixes (source defects repaired) -- PLEASE REVIEW", CAT_REFFIX,
                "None.")
        section("`\\ref` kind-word mismatches (dropped word differs from the target's environment kind)",
                CAT_KIND, "None.")
        out.append("## Commented-out statement environments (dropped, not ported)")
        out.append("")
        if not self.commented:
            out.append("None.")
        for x in self.commented:
            lab = f"label `{x['label']}`" if x["label"] else "no label"
            live = ""
            if x["label"] in self.ctx.labels:
                lv = self.ctx.labels[x["label"]]
                live = f"; the same label is live at `{lv['file']}:{lv['line']}` ({lv['env']})"
            pr = " (with a commented proof)" if x["has_proof"] else ""
            ttl = f", title `{x['title']}`" if x["title"] else ""
            out.append(f"* `{x['file']}:{x['line']}-{x['last']}`: commented-out `{x['env']}`{pr}, {lab}{ttl}{live}")
        out.append("")
        section("Lists with explicit item labels (`\\item[..]`), including description lists", CAT_LIST,
                "None.")
        out.append("## Labels whose prefix does not match the environment kind (kind taken from the environment)")
        out.append("")
        prefix_kind = {"def": "definition", "lem": "lemma", "thm": "theorem", "cor": "corollary"}
        mism = [(l, i) for l, i in self.ctx.labels.items()
                if ":" in l and prefix_kind.get(l.split(":")[0], i["env"]) != i["env"]]
        if not mism:
            out.append("None.")
        for l, i in mism:
            out.append(f"* `{i['file']}:{i['line']}`: `{l}` labels a `{i['env']}` "
                       f"(emitted as `:::{NODE_ENV_KIND[i['env']]}`)")
        out.append("")
        out.append("## Other notices and judgement calls")
        out.append("")
        out.append("* Node kinds come from the TeX environment, never from the label prefix; labels are "
                   "`kind:name` -> `kind_name` (see `label_map.json`).")
        out.append("* Group ids/titles: one group per chapter (`grp_*`); the group body is the TeX chapter "
                   "title WITHOUT the appendix prefix; document titles of the appendices carry "
                   f"the prefix {self.appendix_prefix!r}.")
        out.append("* `\\ldots`, `~`, quotes, dashes are converted as in plan section 7; `\\ref`s are "
                   "converted to `{bpref \"label\"}[]` with the preceding kind word and `~` dropped.")
        rows = [x for x in n if x[0] == CAT_OTHER]
        for _c, f, l, msg in rows:
            out.append(f"* `{f}:{l}`: {msg}")
        out.append("")
        return "\n".join(out)


# --------------------------------------------------------------------------------------------------
# Convenience API (used by the unit tests) and CLI
# --------------------------------------------------------------------------------------------------


def convert_fragment(tex: str, labels: dict | None = None, name: str = "<fragment>") -> str:
    """Convert a TeX body fragment (prose, lists, display maths) to Verso text.  Test helper.

    ``labels`` maps known TeX labels to their environment kind (for ``\\ref`` resolution).
    """
    ctx = Ctx({l: {"env": e, "file": name, "line": 1, "verso": label_to_verso(l)}
               for l, e in (labels or {}).items()})
    parser = Parser(Src(name, tex), ctx)
    blocks, term = parser.parse_blocks()
    assert term is None
    lines = Renderer(ctx).render_blocks(blocks, name)
    return ctx.resolve_refs("\n".join(lines))


def run(src_dir: Path, out_dir: Path, only=None, appendix_prefix: str = "Appendix: "):
    conv = Converter(src_dir, appendix_prefix)
    conv.load()
    only = [o.upper() for o in only] if only else None
    if only:
        unknown = [o for o in only if o not in {c.number for c in conv.chapters}]
        if unknown:
            raise ValueError(f"unknown chapter selector(s) in --only: {', '.join(unknown)}")
    selected = [ch for ch in conv.chapters if not only or ch.number in only]
    # render every chapter (in order) so that all notices/errors are produced regardless of --only
    rendered = {ch.module: conv.render_chapter(ch) for ch in conv.chapters}
    modules = {ch.module: rendered[ch.module] for ch in selected}
    out_dir = Path(out_dir)
    (out_dir / "Chapters").mkdir(parents=True, exist_ok=True)
    for mod, text in modules.items():
        (out_dir / "Chapters" / f"{mod}.lean").write_text(text, encoding="utf8")
    (out_dir / "label_map.json").write_text(
        json.dumps(conv.label_map(), indent=2, ensure_ascii=False) + "\n", encoding="utf8")
    (out_dir / "report.md").write_text(conv.report(list(modules), only, rendered), encoding="utf8")
    return conv


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--src", required=True, help="directory with content.tex and the chapter files")
    ap.add_argument("--out", required=True, help="output directory (Chapters/, label_map.json, report.md)")
    ap.add_argument("--only", default="", help="comma-separated chapter numbers to write, e.g. 1,2,A")
    ap.add_argument("--appendix-prefix", default="Appendix: ",
                    help="prefix of the document titles of the appendices (default: 'Appendix: ')")
    args = ap.parse_args(argv)
    only = [x.strip() for x in args.only.split(",") if x.strip()] or None
    try:
        run(Path(args.src), Path(args.out), only, args.appendix_prefix)
    except ConvError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    except ValueError as e:
        ap.error(str(e))
    return 0


if __name__ == "__main__":
    sys.exit(main())

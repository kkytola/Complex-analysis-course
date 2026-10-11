#!/usr/bin/env python3
"""TeX-side inventory of the legacy leanblueprint sources (standard library only).

Reads ``blueprint/src/content.tex`` and the files it ``\\input``s (comments stripped) and writes a JSON
inventory: chapters, an ordered outline (sections / nodes), every theorem-like node with its label,
kind, title, ``\\uses`` edges (statement and proof), proof presence, ordered maths spans and legacy
number.  It is the TeX-side ground truth of ``check_parity.py``.

Usage:  python3 -I scripts/migration/tex_inventory.py [--src blueprint/src] [-o baseline_inventory.json]
"""
import argparse
import json
import re
import sys
from pathlib import Path

NODE_ENVS = ("definition", "lemma", "theorem", "corollary")
COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
MATH_RE = re.compile(
    r"\\begin\{align\*\}.*?\\end\{align\*\}|(?<![\\$])\$(?!\$)(.+?)(?<!\\)\$", re.S)


def strip_comments(text: str) -> str:
    """Remove ``%`` comments (keeps newlines so that line numbers stay valid)."""
    return COMMENT_RE.sub("", text)


def norm(text: str) -> str:
    """Whitespace-normalise a piece of TeX."""
    return re.sub(r"\s+", " ", text).strip()


def label_to_verso(label: str) -> str:
    """Decision D4: ``kind:name`` becomes ``kind_name``."""
    return label.replace(":", "_")


def balanced(text: str, start: int, open_c: str, close_c: str) -> int:
    """Index just after the group opened at ``text[start]``; braces nest, brackets inside braces ignored."""
    depth = 0
    i = start
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "{" and open_c != "{":
            # skip a braced group while scanning for ']'
            i = balanced(text, i, "{", "}")
            continue
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced group")


def split_labels(arg: str):
    return [x.strip() for x in arg.split(",") if x.strip()]


def math_spans(text: str):
    spans = []
    for m in MATH_RE.finditer(text):
        if m.group(0).startswith("\\begin"):
            spans.append({"kind": "display", "tex": norm(m.group(0))})
        else:
            spans.append({"kind": "inline", "tex": norm(m.group(1))})
    return spans


def parse_content(src: Path):
    """Chapters in order, with their ``\\input`` files; also the intro text."""
    text = strip_comments((src / "content.tex").read_text(encoding="utf8"))
    chapters = []
    appendix = False
    intro = []
    for line in text.splitlines():
        s = line.strip()
        m = re.match(r"\\chapter\{(.*)\}$", s)
        if m:
            chapters.append({"title": m.group(1), "files": [], "appendix": appendix})
        elif s == "\\appendix":
            appendix = True
        else:
            m = re.match(r"\\input\{([^}]*)\}$", s)
            if m:
                name = m.group(1)
                chapters[-1]["files"].append(name if name.endswith(".tex") else name + ".tex")
            elif not chapters:
                intro.append(line)
    letters = iter("ABCDEFGH")
    nums = iter(range(1, 20))
    for ch in chapters:
        ch["number"] = next(letters) if ch["appendix"] else str(next(nums))
    return chapters, "\n".join(intro).strip()


def parse_file(path: Path, chapter: dict, counter: list, nodes: list, outline: list):
    raw = path.read_text(encoding="utf8")
    text = strip_comments(raw)
    pos = 0
    token_re = re.compile(
        r"\\(?P<sec>section|subsection)\{(?P<title>[^}]*)\}"
        r"|\\begin\{(?P<env>definition|lemma|theorem|corollary)\}")
    while True:
        m = token_re.search(text, pos)
        if not m:
            break
        line = text.count("\n", 0, m.start()) + 1
        if m.group("sec"):
            outline.append({"type": m.group("sec"), "title": m.group("title"),
                            "chapter": chapter["number"], "file": path.name, "line": line})
            pos = m.end()
            continue
        env = m.group("env")
        end_m = re.compile(r"\\end\{%s\}" % env).search(text, m.end())
        body = text[m.end():end_m.start()]
        title = None
        stripped = body.lstrip()
        if stripped.startswith("["):
            off = len(body) - len(stripped)
            stop = balanced(body, off, "[", "]")
            title = body[off + 1:stop - 1]
            body = body[stop:]
        label = re.search(r"\\label\{([^}]*)\}", body).group(1)
        statement_uses = [x for u in re.findall(r"\\uses\{([^}]*)\}", body) for x in split_labels(u)]
        pos = end_m.end()
        proof = None
        pm = re.compile(r"\s*\\begin\{proof\}").match(text, pos)
        if pm:
            pe = re.compile(r"\\end\{proof\}").search(text, pm.end())
            proof = text[pm.end():pe.start()]
            pos = pe.end()
        counter[0] += 1
        palka = re.findall(r"\\Palka\{([^}]*)\}", title or "") + re.findall(r"\\Palka\{([^}]*)\}", body)
        node = {
            "order": len(nodes) + 1,
            "chapter": chapter["number"],
            "number": f"{chapter['number']}.{counter[0]}",
            "file": path.name,
            "line": line,
            "env": env,
            "label": label,
            "label_verso": label_to_verso(label),
            "title_raw": title,
            "statement_uses": statement_uses,
            "statement_uses_verso": [label_to_verso(x) for x in statement_uses],
            "has_proof": proof is not None,
            "proof_uses": [x for u in re.findall(r"\\uses\{([^}]*)\}", proof or "") for x in split_labels(u)],
            "math_spans": math_spans(body),
            "proof_math_spans": math_spans(proof or ""),
            "n_term": len(re.findall(r"\\term\{", body)) + len(re.findall(r"\\term\{", proof or "")),
            "n_palka": len(palka) + len(re.findall(r"\\Palka\{", proof or "")),
            "n_ref": len(re.findall(r"\\(?:ref|defref|thmref|lemref)\{", body + (proof or ""))),
        }
        node["proof_uses_verso"] = [label_to_verso(x) for x in node["proof_uses"]]
        nodes.append(node)
        outline.append({"type": "node", "label": label, "label_verso": label_to_verso(label),
                        "env": env, "chapter": chapter["number"], "file": path.name, "line": line})


def build(src: Path):
    chapters, intro = parse_content(src)
    nodes, outline = [], []
    for ch in chapters:
        counter = [0]
        outline.append({"type": "chapter", "title": ch["title"], "number": ch["number"]})
        for f in ch["files"]:
            parse_file(src / f, ch, counter, nodes, outline)
    labels = [n["label"] for n in nodes]
    assert len(labels) == len(set(labels)), "duplicate labels"
    known = set(labels)
    dangling = sorted({u for n in nodes for u in n["statement_uses"] + n["proof_uses"] if u not in known})
    counts = {
        "nodes": len(nodes),
        "by_kind": {k: sum(1 for n in nodes if n["env"] == k) for k in NODE_ENVS},
        "proofs": sum(1 for n in nodes if n["has_proof"]),
        "statement_edges": sum(len(n["statement_uses"]) for n in nodes),
        "proof_edges": sum(len(n["proof_uses"]) for n in nodes),
        "sections": sum(1 for o in outline if o["type"] == "section"),
        "subsections": sum(1 for o in outline if o["type"] == "subsection"),
        "palka": sum(n["n_palka"] for n in nodes),
        "term": sum(n["n_term"] for n in nodes),
    }
    return {"chapters": chapters, "intro": intro, "counts": counts, "dangling_uses": dangling,
            "outline": outline, "nodes": nodes}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", default="blueprint/src")
    ap.add_argument("-o", "--output")
    ap.add_argument("--summary", action="store_true")
    args = ap.parse_args(argv)
    inv = build(Path(args.src))
    if args.output:
        Path(args.output).write_text(json.dumps(inv, indent=1, ensure_ascii=False) + "\n", encoding="utf8")
    if args.summary or not args.output:
        print(json.dumps(inv["counts"], indent=1))
        print("dangling uses:", inv["dangling_uses"])
        for ch in inv["chapters"]:
            print(ch["number"], ch["title"], ch["files"])
    return 0


if __name__ == "__main__":
    sys.exit(main())

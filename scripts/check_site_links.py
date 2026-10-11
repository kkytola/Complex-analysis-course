#!/usr/bin/env python3
"""Check the internal links of an assembled static site (stdlib only).

    python3 scripts/check_site_links.py home_page/_site
    python3 scripts/check_site_links.py SITE_DIR --prefix /Complex-analysis-course/

The site directory is treated as if it were served under the URL path prefix (default
`/Complex-analysis-course/`, as on GitHub Pages project sites).  Every page is parsed and every
internal reference is resolved *as a browser would resolve it* against the URL of the page, then
mapped back to a file below SITE_DIR.  This proves, without a web server, that

  * no link, stylesheet or script is a root-absolute path that escapes the prefix (`/blueprint/`
    instead of `/Complex-analysis-course/blueprint/`),
  * every referenced file exists (directory URLs resolve to their `index.html`),
  * every `#fragment` that points into a page of the site names an existing `id`/`name`,
  * `url(...)` references inside the stylesheets exist,
  * the legacy URL `blueprint/dep_graph_document.html` is a working redirect to the graph page,
  * the key files of the site are present (and blueprint.pdf really is a PDF).

Checked: href/src/srcset/action/poster/data attributes of HTML pages, `<meta http-equiv=refresh>`,
`<base href>`, `url()`/`@import` in .css files and in `<style>` blocks.  Not checked (cannot be done
statically): URLs assembled by JavaScript at run time (the graph page fetches its data that way, so
load it in a browser too, e.g. with `chromium --headless --dump-dom`), and external `http(s)` links
(they are only counted).

Absolute URLs whose host and path prefix are those of the site (e.g. the `{{ site.url }}/blueprint/`
links of the Jekyll home page) count as internal and are checked against the local files.

Exit status: 0 = all fine, 1 = broken links or missing files, 2 = bad usage.
"""

from __future__ import annotations

import argparse
import os
import posixpath
import re
import sys
from collections import defaultdict
from html.parser import HTMLParser
from urllib.parse import parse_qs, unquote, urljoin, urlsplit

FAKE_SCHEME = "https"
DEFAULT_HOST = "kkytola.github.io"
DEFAULT_PREFIX = "/Complex-analysis-course/"

# (tag, attribute) pairs whose value is a single URL.
URL_ATTRS = {
    ("a", "href"), ("area", "href"), ("link", "href"), ("base", "href"),
    ("script", "src"), ("img", "src"), ("iframe", "src"), ("frame", "src"), ("source", "src"),
    ("audio", "src"), ("video", "src"), ("video", "poster"), ("track", "src"), ("embed", "src"),
    ("input", "src"), ("form", "action"), ("object", "data"),
}
SRCSET_ATTRS = {("img", "srcset"), ("source", "srcset"), ("link", "imagesrcset")}
CSS_URL_RE = re.compile(r"""url\(\s*(?:"([^"]*)"|'([^']*)'|([^)\s"'][^)]*?))\s*\)""", re.I)
CSS_IMPORT_RE = re.compile(r"""@import\s+(?:"([^"]+)"|'([^']+)')""", re.I)
META_REFRESH_RE = re.compile(r"^\s*(\d+(?:\.\d+)?)\s*(?:[;,]\s*(?:url\s*=\s*)?(.*?))?\s*$", re.I | re.S)


class PageParser(HTMLParser):
    """Collects references, ids and the base URL of one HTML document."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.refs: list[tuple[int, str, str]] = []   # (line, "<tag attr>", value)
        self.ids: set[str] = set()
        # Verso gives the root section of a page no DOM id, but its table-of-contents links use the
        # section tag as fragment ("Chapter/#Doc--Chapter").  The tag is advertised by the permalink
        # `find/?domain=Verso.Genre.Manual.section&name=<tag>`; such fragments just mean "page top".
        self.section_tags: set[str] = set()
        self.base: str | None = None
        self.refresh: list[tuple[int, str, str]] = []  # (line, delay, target)
        self.css_blocks: list[tuple[int, str]] = []
        self._style_line: int | None = None
        self._style_text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        a = {k.lower(): (v if v is not None else "") for k, v in attrs}
        line = self.getpos()[0]
        if "id" in a:
            self.ids.add(a["id"])
        if tag == "a" and "name" in a:
            self.ids.add(a["name"])
        for (t, attr) in URL_ATTRS:
            if t == tag and attr in a:
                if tag == "base":
                    self.base = a[attr]
                else:
                    self.refs.append((line, f"<{tag} {attr}>", a[attr]))
                    if tag == "a" and "domain=Verso.Genre.Manual.section" in a[attr]:
                        for name in parse_qs(urlsplit(a[attr]).query).get("name", []):
                            self.section_tags.add(name)
        for (t, attr) in SRCSET_ATTRS:
            if t == tag and attr in a:
                for candidate in a[attr].split(","):
                    parts = candidate.strip().split()
                    if parts:
                        self.refs.append((line, f"<{tag} {attr}>", parts[0]))
        if tag == "meta" and a.get("http-equiv", "").lower() == "refresh":
            m = META_REFRESH_RE.match(a.get("content", ""))
            if m and m.group(2):
                target = m.group(2).strip().strip("'\"")
                self.refresh.append((line, m.group(1), target))
                self.refs.append((line, "<meta refresh>", target))
        if "style" in a:
            self.css_blocks.append((line, a["style"]))
        if tag == "style":
            self._style_line = line
            self._style_text = []

    def handle_data(self, data: str) -> None:
        if self._style_line is not None:
            self._style_text.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag == "style" and self._style_line is not None:
            self.css_blocks.append((self._style_line, "".join(self._style_text)))
            self._style_line = None


def css_references(text: str) -> list[str]:
    out = []
    for m in CSS_URL_RE.finditer(text):
        out.append((m.group(1) or m.group(2) or m.group(3) or "").strip())
    for m in CSS_IMPORT_RE.finditer(text):
        out.append((m.group(1) or m.group(2) or "").strip())
    return [u for u in out if u]


class Checker:
    def __init__(self, root: str, prefix: str, host: str, fragments: str) -> None:
        self.root = os.path.abspath(root)
        self.prefix = prefix
        self.host = host
        self.fragments = fragments  # "error" | "warn" | "off"
        self.errors: dict[str, list[str]] = defaultdict(list)   # page (site-relative) -> messages
        self.warnings: list[str] = []
        self.notes: list[str] = []
        self.parsed: dict[str, PageParser] = {}
        self.n_internal = 0
        self.n_external = 0
        self.n_fragments = 0
        self.n_section_tag_fragments = 0

    # -- URL <-> file mapping -------------------------------------------------------------

    def page_url(self, rel: str) -> str:
        """The URL under which the file `rel` (site-relative, '/'-separated) is served."""
        if rel == "index.html" or rel.endswith("/index.html"):
            rel = rel[: -len("index.html")]
        return f"{FAKE_SCHEME}://{self.host}{self.prefix}{rel}"

    def resolve_path(self, url_path: str) -> tuple[str | None, str]:
        """Map a URL path (already inside the prefix) to (site-relative file or None, note)."""
        rel = unquote(url_path[len(self.prefix):])
        if rel == "" or rel.endswith("/"):
            cand = rel + "index.html"
            return (cand, "") if os.path.isfile(os.path.join(self.root, cand)) else (None, f"no {cand}")
        full = os.path.join(self.root, rel)
        if os.path.isfile(full):
            return rel, ""
        if os.path.isdir(full):
            if os.path.isfile(os.path.join(full, "index.html")):
                # GitHub Pages answers a directory URL without the slash with a redirect.
                return rel + "/index.html", "directory URL without trailing slash (served through a redirect)"
            return None, "directory without index.html"
        return None, "file not found"

    def parse_page(self, rel: str) -> PageParser:
        if rel not in self.parsed:
            p = PageParser()
            with open(os.path.join(self.root, rel), encoding="utf-8", errors="replace") as fh:
                p.feed(fh.read())
                p.close()
            self.parsed[rel] = p
        return self.parsed[rel]

    # -- checking one reference -------------------------------------------------------------

    def check_ref(self, source: str, line: int, kind: str, value: str, base_url: str) -> str | None:
        """Check one reference found in `source`; returns the site-relative target file if internal."""
        shown = f"{source}:{line}: {kind} {value!r}"
        raw = value.strip()
        if raw in ("", "#"):
            return None
        parts = urlsplit(raw)
        if parts.scheme and parts.scheme not in ("http", "https"):
            return None  # mailto:, tel:, javascript:, data:, ...
        url = urljoin(base_url, raw)
        u = urlsplit(url)
        if u.netloc and u.netloc.lower() != self.host.lower():
            self.n_external += 1
            return None
        if not u.path.startswith(self.prefix) and u.path != self.prefix.rstrip("/"):
            if u.netloc and parts.netloc:
                # an absolute URL of the same host but outside our project: somebody else's site
                self.n_external += 1
                return None
            self.errors[source].append(
                f"{shown} -> resolves to {u.path!r}, outside the site prefix {self.prefix!r} "
                f"(a root-absolute path breaks the site on a sub-path)")
            return None
        path = u.path if u.path.startswith(self.prefix) else self.prefix
        self.n_internal += 1
        target, note = self.resolve_path(path)
        if target is None:
            self.errors[source].append(f"{shown} -> {note}: {path}")
            return None
        if note:
            self.notes.append(f"{shown} -> {note}")
        frag = unquote(u.fragment)
        if frag and self.fragments != "off" and target.endswith(".html"):
            self.n_fragments += 1
            tgt = self.parse_page(target)
            if frag in tgt.section_tags and frag not in tgt.ids:
                self.n_section_tag_fragments += 1
            elif frag not in tgt.ids and u.fragment not in tgt.ids and frag != "top":
                msg = f"{shown} -> fragment #{frag} not found in {target}"
                if self.fragments == "error":
                    self.errors[source].append(msg)
                else:
                    self.warnings.append(msg)
        return target

    def check_css(self, source: str, line: int, text: str, base_url: str) -> None:
        for ref in css_references(text):
            if ref.startswith("data:"):
                continue
            self.check_ref(source, line, "css url()", ref, base_url)

    # -- driver -------------------------------------------------------------------------------

    def html_files(self) -> list[str]:
        out = []
        for dirpath, dirnames, filenames in os.walk(self.root):
            # Jekyll sources (_layouts, _include, ...) are not part of a built site.
            dirnames[:] = sorted(d for d in dirnames if not d.startswith("_"))
            for fn in sorted(filenames):
                if fn.endswith((".html", ".htm")):
                    out.append(os.path.relpath(os.path.join(dirpath, fn), self.root).replace(os.sep, "/"))
        return out

    def check_page(self, rel: str) -> list[str]:
        page = self.parse_page(rel)
        url = self.page_url(rel)
        base = urljoin(url, page.base) if page.base else url
        targets = []
        for line, kind, value in page.refs:
            t = self.check_ref(rel, line, kind, value, base)
            if t:
                targets.append(t)
        for line, css in page.css_blocks:
            self.check_css(rel, line, css, base)
        return targets

    def check_stylesheet(self, rel: str) -> None:
        with open(os.path.join(self.root, rel), encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        self.check_css(rel, 0, text, self.page_url(rel))

    def run(self, entries: list[str]) -> set[str]:
        """Crawl from `entries`, then check every remaining page and every stylesheet reached."""
        reached: set[str] = set()
        queue = [e for e in entries if os.path.isfile(os.path.join(self.root, e))]
        stylesheets: set[str] = set()
        while queue:
            rel = queue.pop()
            if rel in reached:
                continue
            reached.add(rel)
            for t in self.check_page(rel):
                if t.endswith((".html", ".htm")) and t not in reached:
                    queue.append(t)
        for rel in self.html_files():
            if rel not in reached:
                self.check_page(rel)
        for dirpath, dirnames, filenames in os.walk(self.root):
            dirnames[:] = sorted(d for d in dirnames if not d.startswith("_"))
            for fn in filenames:
                if fn.endswith(".css"):
                    stylesheets.add(os.path.relpath(os.path.join(dirpath, fn), self.root).replace(os.sep, "/"))
        for rel in sorted(stylesheets):
            self.check_stylesheet(rel)
        return reached

    # -- structural expectations ---------------------------------------------------------------

    def require_file(self, rel: str) -> None:
        full = os.path.join(self.root, rel)
        if not os.path.isfile(full):
            self.errors["(required files)"].append(f"missing required file {rel}")
            return
        if rel.endswith(".pdf"):
            with open(full, "rb") as fh:
                if fh.read(5) != b"%PDF-":
                    self.errors["(required files)"].append(f"{rel} is not a PDF (no %PDF- header)")

    def expect_redirect(self, src: str, dst: str) -> None:
        full = os.path.join(self.root, src)
        if not os.path.isfile(full):
            self.errors["(redirects)"].append(f"redirect page {src} is missing")
            return
        page = self.parse_page(src)
        base = self.page_url(src)
        want = self.page_url(dst + "index.html" if dst.endswith("/") else dst)
        if not page.refresh:
            self.errors[src].append("no <meta http-equiv=\"refresh\" content=\"0; url=...\"> found")
            return
        for line, delay, target in page.refresh:
            got = urljoin(base, target)
            if got != want:
                self.errors[src].append(f"{src}:{line}: meta refresh goes to {got}, expected {want}")
            if float(delay) > 1:
                self.errors[src].append(f"{src}:{line}: meta refresh delay is {delay}s (should be 0)")
        links = [urljoin(base, v) for (_l, k, v) in page.refs if k == "<a href>"]
        if want not in links:
            self.errors[src].append(f"no visible <a href> to {dst} (a link is needed for browsers that ignore refresh)")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Check the internal links of an assembled static site mounted under a URL prefix.")
    ap.add_argument("site_dir", help="the assembled site, e.g. home_page/_site")
    ap.add_argument("--prefix", default=DEFAULT_PREFIX,
                    help=f"URL path prefix under which the site is served (default {DEFAULT_PREFIX})")
    ap.add_argument("--host", default=DEFAULT_HOST,
                    help=f"host name of the public site; absolute URLs to it count as internal (default {DEFAULT_HOST})")
    ap.add_argument("--fragments", choices=("error", "warn", "off"), default="error",
                    help="how to treat #fragments that name no id in a page of the site (default: error)")
    ap.add_argument("--entry", action="append", default=None, metavar="PATH",
                    help="extra crawl entry point, site-relative (repeatable); all pages are checked anyway")
    ap.add_argument("--require", action="append", default=[], metavar="PATH",
                    help="additionally require this file to exist (repeatable)")
    ap.add_argument("--no-home", action="store_true",
                    help="the site was assembled without Jekyll: do not require the home page index.html")
    ap.add_argument("--no-pdf", action="store_true",
                    help="the site was assembled without the PDF: do not require blueprint.pdf")
    ap.add_argument("--expect-redirect", action="append", metavar="SRC=DST", default=None,
                    help="check that page SRC redirects to DST (site-relative; repeatable; default "
                         "blueprint/dep_graph_document.html=blueprint/Dependency-Graph/)")
    ap.add_argument("-q", "--quiet", action="store_true", help="only print errors")
    args = ap.parse_args(argv)

    if not os.path.isdir(args.site_dir):
        print(f"check_site_links: {args.site_dir} is not a directory", file=sys.stderr)
        return 2
    prefix = args.prefix
    if not prefix.startswith("/"):
        prefix = "/" + prefix
    if not prefix.endswith("/"):
        prefix += "/"

    ck = Checker(args.site_dir, prefix, args.host, args.fragments)

    required = ["blueprint/index.html", "blueprint/Dependency-Graph/index.html",
                "blueprint/dep_graph_document.html"]
    if not args.no_home:
        required.append("index.html")
    if not args.no_pdf:
        required.append("blueprint.pdf")
    for rel in required + args.require:
        ck.require_file(rel)

    entries = ["index.html", "blueprint/index.html", "blueprint/dep_graph_document.html"] + (args.entry or [])
    reached = ck.run(entries)
    all_pages = ck.html_files()

    redirects = args.expect_redirect if args.expect_redirect is not None \
        else ["blueprint/dep_graph_document.html=blueprint/Dependency-Graph/"]
    for spec in redirects:
        if "=" not in spec:
            print(f"check_site_links: bad --expect-redirect {spec!r} (want SRC=DST)", file=sys.stderr)
            return 2
        src, dst = spec.split("=", 1)
        ck.expect_redirect(src, dst)

    n_err = sum(len(v) for v in ck.errors.values())
    if not args.quiet:
        print(f"site {ck.root} served under {prefix} (host {args.host})")
        print(f"  {len(all_pages)} HTML pages checked ({len(reached)} reached by crawling from the entry points), "
              f"{ck.n_internal} internal references, {ck.n_fragments} fragments "
              f"({ck.n_section_tag_fragments} of them Verso section tags, which resolve to the page top), "
              f"{ck.n_external} external links skipped")
        for n in sorted(set(ck.notes)):
            print(f"  note: {n}")
        for w in ck.warnings:
            print(f"  warning: {w}")
    if n_err:
        print(f"\nFAILED: {n_err} problem(s)", file=sys.stderr)
        for page in sorted(ck.errors):
            for msg in ck.errors[page]:
                print(f"  {msg}" if msg.startswith(page) else f"  {page}: {msg}", file=sys.stderr)
        return 1
    if not args.quiet:
        print("OK: no broken links.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

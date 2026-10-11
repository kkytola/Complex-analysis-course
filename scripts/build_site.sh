#!/usr/bin/env bash
# Build and assemble the complete course web site.  This is the single entry point used by the
# GitHub Actions workflow (.github/workflows/blueprint.yml) and by humans on their own machine.
#
#   scripts/build_site.sh            full build (Lean + PDF + Jekyll + assembly)
#   SKIP_JEKYLL=1 scripts/build_site.sh     no Ruby/Jekyll: the home page is copied unprocessed
#   SKIP_PDF=1 scripts/build_site.sh        no lualatex: the site is assembled without blueprint.pdf
#   SITE_DIR=/some/dir scripts/build_site.sh   put the assembled site elsewhere
#
# Steps
#   1. lake build                    elaborates the Verso Blueprint sources and lints all maths with
#                                    KaTeX.  Fails on any Lean error and on any "KaTeX rejected".
#   2. lake exe vbp build --pdf      writes _out/site/html-multi (the site) and _out/site/pdf/main.pdf.
#                                    Also fails if a `uses`/`bpref` label is undefined (Verso Blueprint
#                                    only draws a red placeholder node for it) or LaTeX reports errors.
#   3. Jekyll build of home_page/    JEKYLL_ENV=production bundle exec jekyll build  (skippable)
#   4. assemble, AFTER Jekyll so that Jekyll never touches Verso's output:
#        <site>/                       the Jekyll home page
#        <site>/blueprint/             = _out/site/html-multi/
#        <site>/blueprint/Dependency-Graph/   the dependency graph (part of the Verso output)
#        <site>/blueprint/dep_graph_document.html   redirect page: the URL of the legacy graph page
#        <site>/blueprint.pdf          = _out/site/pdf/main.pdf
#
# Environment
#   SITE_DIR      directory that receives the assembled site (default: home_page/_site; a relative
#                 path is relative to the repository root).  It is emptied first, so the script is
#                 idempotent; a directory that is not empty and holds no earlier build is refused.
#   SKIP_JEKYLL   non-empty and not "0": skip step 3; <site> becomes a plain copy of home_page/
#                 (so the Verso part can be tested on machines without Ruby gems).
#   SKIP_PDF      non-empty and not "0": do not build the PDF (no lualatex needed).
#
# Requirements: elan (lake on PATH, or in ~/.elan/bin), node (the maths lint silently does nothing
# without it, so this script refuses to run without it), python3, lualatex unless SKIP_PDF,
# ruby + bundler (with the gems of home_page/Gemfile) unless SKIP_JEKYLL.
#
# Afterwards, check the result with  python3 scripts/check_site_links.py <site>
# (add --no-home after SKIP_JEKYLL=1 and --no-pdf after SKIP_PDF=1).

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$ROOT"

SITE_DIR="${SITE_DIR:-home_page/_site}"
SKIP_JEKYLL="${SKIP_JEKYLL:-0}"
SKIP_PDF="${SKIP_PDF:-0}"

case "${1:-}" in
  -h|--help) sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
  "") ;;
  *) echo "build_site.sh: unexpected argument '$1' (configuration is through environment variables, see --help)" >&2
     exit 2 ;;
esac

enabled() { [[ -n "${1:-}" && "$1" != "0" ]]; }

START=$SECONDS
step() { printf '\n==> [%s] %s  (elapsed %ds)\n' "$1" "$2" "$((SECONDS - START))"; }
info() { printf '    %s\n' "$*"; }
die()  { printf '\nbuild_site.sh: ERROR: %s\n' "$*" >&2; exit 1; }

LOG_DIR="$(mktemp -d)"
trap 'rm -rf "$LOG_DIR"' EXIT

# ---------------------------------------------------------------------------------------------
# 0. Preflight: fail early and loudly when something the build silently depends on is missing.
# ---------------------------------------------------------------------------------------------
step 0 "Preflight"

if ! command -v lake >/dev/null 2>&1 && [[ -x "$HOME/.elan/bin/lake" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
command -v lake >/dev/null 2>&1 || die "'lake' not found; install elan (https://github.com/leanprover/elan)."
command -v node >/dev/null 2>&1 \
  || die "'node' not found. Verso Blueprint lints all maths with KaTeX through node and silently skips the lint when node is missing; refusing to build without it."
info "node $(node --version)"
command -v python3 >/dev/null 2>&1 || die "'python3' not found (used to inspect the generated blueprint manifest)."
if enabled "$SKIP_PDF"; then
  info "SKIP_PDF is set: no PDF will be built"
else
  command -v lualatex >/dev/null 2>&1 \
    || die "'lualatex' not found (needed for the PDF). Install TeX Live, or set SKIP_PDF=1."
fi
if enabled "$SKIP_JEKYLL"; then
  info "SKIP_JEKYLL is set: the home page will be copied without Jekyll processing"
else
  command -v bundle >/dev/null 2>&1 \
    || die "'bundle' not found (needed for Jekyll). Install Ruby and bundler, or set SKIP_JEKYLL=1."
fi

# Every chapter module names its page with `file := "slug"` (metadata block after the #doc line). Two modules
# with the same slug would silently overwrite each other's page (the build still succeeds), and a missing slug
# gives a mangled, capitalised URL, so check both here.
for module in ComplexAnalysisCourse/Chapters/*.lean; do
  grep -q '^file := "[a-z0-9-]*"$' "$module" \
    || die "$module has no \`file := \"some-slug\"\` line in the %%% metadata block after its #doc line (see AUTHORING.md): the chapter page would get a mangled URL."
done
duplicate_slugs="$(sed -n -E 's/^file := "([a-z0-9-]*)"$/\1/p' ComplexAnalysisCourse/Chapters/*.lean | sort | uniq -d)"
[[ -z "$duplicate_slugs" ]] || die "several chapter modules use the same page slug (file := \"...\"): $(echo $duplicate_slugs); one page would overwrite the other."
info "chapter page slugs: unique"

# Resolve SITE_DIR and refuse values that would make the "empty the directory" step dangerous.
SITE_ABS="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$SITE_DIR")"
case "$SITE_ABS" in
  "/"|"$HOME"|"$ROOT"|"$ROOT/home_page"|"$ROOT/_out"|"$ROOT/_out/site")
    die "SITE_DIR=$SITE_DIR resolves to $SITE_ABS, which must not be emptied" ;;
esac
case "$ROOT/" in
  "$SITE_ABS"/*) die "SITE_DIR=$SITE_DIR resolves to an ancestor of the repository" ;;
esac
# A non-default SITE_DIR is only emptied if it is empty already or holds an earlier build of this script.
if [[ "$SITE_ABS" != "$ROOT/home_page/_site" && -n "$(ls -A -- "$SITE_ABS" 2>/dev/null)" \
      && ! -f "$SITE_ABS/blueprint/dep_graph_document.html" ]]; then
  die "SITE_DIR=$SITE_DIR exists, is not empty and does not look like an earlier build; refusing to empty it"
fi
info "site directory: $SITE_ABS"

# Print the offending lines of a build log and return non-zero if the log shows a problem that does
# not (reliably) make the command itself exit non-zero.  Lake replays the messages of cached modules,
# so a lint failure keeps showing up on every run until it is fixed.
check_log() {
  local log="$1" what="$2" bad=0 hits
  # A bad macro is reported once per formula that uses it, so show only the first few lines.
  if hits="$(grep -a -n 'KaTeX rejected' "$log")"; then
    printf '%s\n' "$hits" | head -n 10
    [[ $(printf '%s\n' "$hits" | wc -l) -le 10 ]] || echo "    ... and $(( $(printf '%s\n' "$hits" | wc -l) - 10 )) more (full log above)"
    printf 'build_site.sh: ERROR: %s: the maths lint reported "KaTeX rejected" (see above). Fix the macro or formula.\n' "$what" >&2
    bad=1
  fi
  if hits="$(grep -a -n -E '^(error|✖)' "$log")"; then
    printf '%s\n' "$hits" | head -n 20
    printf 'build_site.sh: ERROR: %s: the build log contains errors (see above).\n' "$what" >&2
    bad=1
  fi
  return $bad
}

# Run a command, copy its output to the console and to a log, then inspect the log.
run_checked() {
  local what="$1"; shift
  local log="$LOG_DIR/${what//[^A-Za-z0-9]/_}.log" status=0
  "$@" 2>&1 | tee "$log" || status="${PIPESTATUS[0]}"
  if [[ $status -ne 0 ]]; then
    check_log "$log" "$what" || true
    die "$what failed (exit status $status)"
  fi
  check_log "$log" "$what" || exit 1
  info "$what: $(grep -a -c '^warning:' "$log" || true) warning line(s) in the log (not an error)"
}

# ---------------------------------------------------------------------------------------------
# 1. Lean build (elaborates everything, runs the KaTeX lint on every maths span)
# ---------------------------------------------------------------------------------------------
step 1 "lake build"
run_checked "lake build" lake build

# ---------------------------------------------------------------------------------------------
# 2. Verso Blueprint site (+ PDF)
# ---------------------------------------------------------------------------------------------
step 2 "lake exe vbp build$(enabled "$SKIP_PDF" || echo ' --pdf')"
# Remove stale output from earlier runs, but keep _out/site/tex-cache (lualatex's font cache).
rm -rf _out/site/html-multi _out/site/pdf _out/site/tex
if enabled "$SKIP_PDF"; then
  run_checked "vbp build" lake exe vbp build
else
  run_checked "vbp build" lake exe vbp build --pdf
fi
[[ -f _out/site/html-multi/index.html ]] || die "_out/site/html-multi/index.html was not produced"
[[ -f _out/site/html-multi/Dependency-Graph/index.html ]] \
  || die "_out/site/html-multi/Dependency-Graph/index.html was not produced (is {blueprint_graph} still in Blueprint.lean?)"
# `uses := "..."` with an unknown label is not a build error in Verso Blueprint: the graph just gets
# a red placeholder node.  Treat that (and any other node warning flag) as a failure here.
MANIFEST=_out/site/html-multi/-verso-data/blueprint-manifest.json
[[ -f "$MANIFEST" ]] || die "$MANIFEST was not produced"
python3 -I - "$MANIFEST" <<'PY' || die "the blueprint manifest reports warnings (unknown labels?), see above"
import json, sys
manifest = json.load(open(sys.argv[1], encoding="utf-8"))
nodes = [n for g in manifest.get("graphs", []) for n in g.get("nodes", [])]
bad = [(n.get("label"), sorted(k for k, v in (n.get("warnings") or {}).items() if v)) for n in nodes]
bad = [(label, flags) for label, flags in bad if flags]
print(f"    blueprint manifest: {len(nodes)} graph nodes, {len(bad)} with warnings")
for label, flags in bad:
    print(f"    node {label!r}: {', '.join(flags)}  (unknownRef = a label used in `uses`/`bpref` that is never defined)", file=sys.stderr)
sys.exit(1 if bad else 0)
PY
if ! enabled "$SKIP_PDF"; then
  [[ -f _out/site/pdf/main.pdf ]] || die "_out/site/pdf/main.pdf was not produced"
  # lualatex runs in nonstopmode: a LaTeX error still leaves a (broken) PDF behind.
  if grep -a -n '^! ' _out/site/pdf/main.log; then
    die "LaTeX reported errors while building the PDF (lines above; full log: _out/site/pdf/main.log)"
  fi
fi

# ---------------------------------------------------------------------------------------------
# 3. Home page (Jekyll)
# ---------------------------------------------------------------------------------------------
step 3 "Home page$(enabled "$SKIP_JEKYLL" && echo ' (plain copy, Jekyll skipped)' || echo ' (Jekyll)')"
rm -rf -- "$SITE_ABS"
mkdir -p -- "$SITE_ABS"
if enabled "$SKIP_JEKYLL"; then
  (
    cd home_page
    # Same exclusions as Jekyll's defaults for a source tree; the unprocessed files are only
    # good enough for testing the rest of the assembly.
    for entry in * .[!.]*; do
      case "$entry" in
        "*"|_site|vendor|.bundle|.jekyll-cache|.sass-cache|Gemfile|Gemfile.lock) continue ;;
      esac
      if [[ -e "$entry" ]]; then cp -R -- "$entry" "$SITE_ABS/"; fi
    done
  )
else
  (
    cd home_page
    JEKYLL_ENV=production bundle exec jekyll build --destination "$SITE_ABS"
  )
  [[ -f "$SITE_ABS/index.html" ]] || die "Jekyll did not produce $SITE_ABS/index.html"
fi

# ---------------------------------------------------------------------------------------------
# 4. Assembly (after Jekyll, so that Jekyll never touches Verso's output)
# ---------------------------------------------------------------------------------------------
step 4 "Assemble $SITE_ABS"
rm -rf -- "$SITE_ABS/blueprint" "$SITE_ABS/blueprint.pdf"
mkdir -p -- "$SITE_ABS/blueprint"
cp -R -- _out/site/html-multi/. "$SITE_ABS/blueprint/"
info "blueprint/            <- _out/site/html-multi/"
if enabled "$SKIP_PDF"; then
  info "blueprint.pdf         (skipped)"
else
  cp -- _out/site/pdf/main.pdf "$SITE_ABS/blueprint.pdf"
  info "blueprint.pdf         <- _out/site/pdf/main.pdf"
fi

# The legacy leanblueprint graph page lived at blueprint/dep_graph_document.html.  Old links keep
# working through this redirect to the graph page of Verso Blueprint.
cat > "$SITE_ABS/blueprint/dep_graph_document.html" <<'EOF'
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta http-equiv="refresh" content="0; url=Dependency-Graph/">
  <title>Dependency graph</title>
</head>
<body>
  <p>The dependency graph has moved to <a href="Dependency-Graph/">Dependency-Graph/</a>.</p>
</body>
</html>
EOF
info "blueprint/dep_graph_document.html  (redirect to Dependency-Graph/)"

# Legacy deep links: the old site had one page per chapter, blueprint/sect0001.html ... sect0008.html (chapters
# 1-6, then the two appendices), with anchors named after the TeX labels (sect0005.html#lem:abel).  Each stub
# below redirects to the matching chapter page, and to the statement itself when the URL has a known label
# (`kind:name`; the new labels are `kind_name`).  The chapter order is the order of the {include} lines.
python3 -I - "$SITE_ABS/blueprint" <<'PY'
import json, re, sys
from pathlib import Path
site = Path(sys.argv[1])
blueprint = Path("ComplexAnalysisCourse/Blueprint.lean").read_text(encoding="utf-8")
modules = re.findall(r"^\{include 0 ComplexAnalysisCourse\.Chapters\.(\w+)\}", blueprint, re.M)
slugs = []
for m in modules:
    text = Path(f"ComplexAnalysisCourse/Chapters/{m}.lean").read_text(encoding="utf-8")
    slugs.append(re.search(r'^file := "([^"]+)"$', text, re.M).group(1))
manifest = json.loads((site / "-verso-data/blueprint-manifest.json").read_text(encoding="utf-8"))
targets = {e["authoredLabel"]: e["href"] for e in manifest["previews"] if e.get("facet") == "statement"}
(site / "legacy-links.js").write_text(
    "// Redirects the URLs of the legacy site (sectNNNN.html#kind:name); generated by scripts/build_site.sh\n"
    "(function () {\n"
    "  var statements = " + json.dumps(targets, sort_keys=True) + ";\n"
    "  var hash = decodeURIComponent(location.hash.slice(1)).replace(/:/g, '_');\n"
    "  location.replace(statements[hash] || document.documentElement.getAttribute('data-chapter'));\n"
    "})();\n", encoding="utf-8")
for n, slug in enumerate(slugs, 1):
    (site / f"sect{n:04d}.html").write_text(
        '<!DOCTYPE html>\n<html lang="en" data-chapter="%s/">\n<head>\n  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width, initial-scale=1">\n'
        '  <title>Moved</title>\n  <script src="legacy-links.js"></script>\n'
        '  <noscript><meta http-equiv="refresh" content="0; url=%s/"></noscript>\n</head>\n<body>\n'
        '  <p>This page has moved to <a href="%s/">%s/</a>.</p>\n</body>\n</html>\n' % (slug, slug, slug, slug),
        encoding="utf-8")
print(f"    blueprint/sect0001.html ... sect{len(slugs):04d}.html  (legacy chapter URLs; {len(targets)} statements)")
PY

# Sanity checks on the result.
[[ -f "$SITE_ABS/blueprint/index.html" ]] || die "assembly failed: $SITE_ABS/blueprint/index.html is missing"
[[ -f "$SITE_ABS/blueprint/Dependency-Graph/index.html" ]] || die "assembly failed: the graph page is missing"
# actions/upload-pages-artifact does not accept symbolic links.
if links="$(find "$SITE_ABS" -type l -print)" && [[ -n "$links" ]]; then
  printf '%s\n' "$links" >&2
  die "the assembled site contains symbolic links (listed above)"
fi

# actions/upload-artifact (used for the pull-request preview) rejects file names containing any of
# " : < > | * ? and they would not make good URLs anyway (# and % are listed for that reason).
if names="$(cd "$SITE_ABS" && find . -print | LC_ALL=C grep -n -E '["*:<>?|\\#%]')"; then
  printf '%s\n' "$names" >&2
  die "the assembled site contains file names with characters that break artifact upload or URLs (listed above)"
fi

printf '\n==> Done in %ds. Site: %s  (%s files, %s)\n' \
  "$((SECONDS - START))" "$SITE_ABS" "$(find "$SITE_ABS" -type f | wc -l)" "$(du -sh "$SITE_ABS" | cut -f1)"
info "check its links:  python3 scripts/check_site_links.py $SITE_DIR$(enabled "$SKIP_JEKYLL" && echo ' --no-home')$(enabled "$SKIP_PDF" && echo ' --no-pdf')"

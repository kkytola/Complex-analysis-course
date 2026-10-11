# Authoring the theory skeleton

The *theory skeleton* of the course MS-C1300 Complex Analysis (statements, proofs sketches and their
logical dependencies) is a [Verso Blueprint](https://github.com/leanprover/verso-blueprint) document: a
Lean project whose sources are Verso markup (Markdown-like text with LaTeX maths). It is built into a web
site (chapters, interactive dependency graph) and a PDF, and deployed to GitHub Pages by
`.github/workflows/blueprint.yml`.

There is **no Lean formalization** attached: Lean is only the host language of the document. The Lean
version simply follows the release line of VersoBlueprint (`lean-toolchain`, `lake-manifest.json`).

## Layout

| Path | Content |
|---|---|
| `ComplexAnalysisCourse/Chapters/*.lean` | one module per chapter (6 chapters, 2 appendices) |
| `ComplexAnalysisCourse/Blueprint.lean` | the top-level document: title, intro text, chapter list, dependency graph |
| `ComplexAnalysisCourse/Macros.lean` | **all LaTeX math macros** (see below) |
| `ComplexAnalysisCourse/Roles.lean` | text-level macros: `{term}`, `{palka}`, `{nodetitle}`, `{metSpCourse}` |
| `ComplexAnalysisCourse/MacroGallery.lean` | generated; uses every macro once so that `lake build` lints them |
| `ComplexAnalysisCourse/SiteConfig.lean`, `assets/` | site configuration, graph styling (CSS/JS) |
| `ComplexAnalysisCourse/TeXFixes.lean` | workaround for a PDF paragraph-break bug of VersoBlueprint |
| `BlueprintMain.lean` | generator entry point (`lake exe vbp build` runs it) |
| `home_page/` | the Jekyll home page of the course (links to the blueprint) |
| `scripts/` | `build_site.sh` (CI/local), `check_site_links.py`, `gen_macro_gallery.py` |

## Building and previewing

Prerequisites: [elan](https://github.com/leanprover/elan) (installs the right Lean automatically; the first
`lake build` compiles Verso and takes several minutes, later builds take seconds), Node.js (maths is
checked with KaTeX while building), optionally `lualatex` (PDF). In VS Code use the *Lean 4* extension.

```bash
lake build                       # elaborate everything; reports Verso/KaTeX problems
lake exe vbp build --serve       # build the site and serve it locally (prints the URL)
lake exe vbp build --pdf         # also writes _out/site/pdf/main.pdf
lake exe vbp query stats         # counts of nodes by kind (also: labels, node <l>, uses <l>, used-by <l>)
./scripts/build_site.sh          # what CI does: build + assemble home page and blueprint
```

The generated site is `_out/site/html-multi/` (not committed).

## Writing a chapter

Each chapter is a Lean module `#doc (Manual) "Title" =>`; `# Section`, `## Subsection`; text is Verso
markup. A new chapter: copy the header of an existing module (VS Code snippet `chapter`), `import` it in
`Blueprint.lean` and add `{include 0 ComplexAnalysisCourse.Chapters.MyChapter}` in the right place.

### Statements and proofs

````lean
:::lemma_ "lem_goursat" (parent := "grp_cauchy_theorem") (uses := "def_triangle, def_complex_derivative")
{nodetitle}[Goursat's lemma] {palka}[Lem V.1.1]

Let $`U \subset \bC` be an open set ... and
$$`
\begin{align*}
  \oint_{\partial \Tri} f(z) \, \ud z = 0 .
\end{align*}
`
See {bpref "thm_cauchy_theorem"}[]; a defined term looks like {term}[star-shaped].
:::

:::proof "lem_goursat" (uses := "def_complex_derivative")
…
:::
````

* **Kinds:** `:::definition`, `:::lemma_` (with the underscore), `:::theorem`, `:::corollary`,
  `:::proposition`; the proof of a statement is `:::proof` with the *same label*, written after it. Choose
  the kind by what the statement *is*, not by its label.
* **Labels** are `kind_name` in snake case (`def_`, `lem_`, `thm_`, `cor_`, e.g. `lem_abel`). Labels are
  permanent identifiers (they drive links, graph nodes and URL anchors): do not rename them casually.
* **Dependencies.** `(uses := "a, b")` on the statement declares the statements it depends on; the same
  option on `:::proof` declares what only the proof needs. In running text, `{uses "a"}[]` does the same
  and links; `{bpref "a"}[]` links *without* a dependency edge. An empty `[]` generates the visible text
  ("Lemma 2.3"), so do not write the word "Lemma" before it. Forward references are fine.
* **Titles and references.** Verso node headers have no title slot, so the first line of the body holds
  `{nodetitle}[Title]` and, for the textbook, `{palka}[Thm V.1.5]` (shows `[Palka1991, Thm V.1.5]`).
* **Groups.** Each chapter declares `:::group "grp_chapter"` + title at its top and all of its statements
  carry `(parent := "grp_chapter")`; the dependency graph draws one cluster per chapter and offers
  per-chapter views.
* **Numbering** is per chapter with one shared counter (`Lemma 2.2`, `Theorem 2.4`). The appendices are
  chapters 7 and 8 (Verso cannot letter them).

### Verso markup pitfalls

* Maths: inline `` $`x^2` ``, display `` $$`...` `` (may span lines; `align*`, `cases`, `array` work).
  Inline `$...$` of LaTeX is *not* valid.
* In running text an unmatched `*`, `_`, `` ` ``, `[`, `]`, `{`, `}` is a syntax error: write `\*`, `\_`,
  `\[`, ... A line of text must not begin with `* `, `1. `, `#`, `:::` or `>` unless it is meant as markup.
* Emphasis `_text_`, bold `*text*`, lists `* item` / `1. item` (continuation lines indented by two spaces,
  blank line before the list).

## Macros

* **LaTeX math macros live in `ComplexAnalysisCourse/Macros.lean`** — and only there. They are ordinary
  `\newcommand`s inside `tex_prelude r#"..."#` chunks (one chunk per theme, comment above it). The same
  macros are used by KaTeX in the web pages and by LaTeX in the PDF. Every chapter imports the module.
* KaTeX built-ins (e.g. `\set`) cannot be redefined by `\newcommand`: use `\def` (works in KaTeX and
  LaTeX). Packages are not available (`\mathbbm` etc.); `lake build` prints `KaTeX rejected blueprint
  math` for anything KaTeX cannot handle — fix all of them.
* After adding or changing a macro: `python3 scripts/gen_macro_gallery.py` (regenerates
  `MacroGallery.lean`, which uses every macro once), then `lake build`; look at the result with
  `lake exe vbp build --serve`.
* Text-level helpers (`\term`, `\Palka`, ...) are Verso *roles* in `Roles.lean` (a role must live in an
  imported module). Add new ones there following the existing pattern.

## Deployment

`.github/workflows/blueprint.yml` builds the project (`scripts/build_site.sh`), assembles the Jekyll home
page together with the blueprint (`/blueprint/`, graph at `/blueprint/Dependency-Graph/`, PDF at
`/blueprint.pdf`) and deploys to GitHub Pages on pushes to `main`. Pull requests only build and upload
the assembled site as a workflow artifact. A build fails if the log contains `KaTeX rejected`.

## Upgrading Verso Blueprint

VersoBlueprint states that it keeps no compatibility layers and follows Lean release lines: the branch
named in `lakefile.lean` (`@ "v4.35.0"`) determines the Lean version. To upgrade, change the branch to the
newest `vX.Y.Z`, copy its `lean-toolchain`, run `lake update`, rebuild, and re-check the pieces that hook
into upstream internals: `assets/` (CSS/JS use upstream class names, listed at the top of each file),
`TeXFixes.lean` (may become unnecessary once upstream fixes the paragraph breaks) and `SiteConfig.lean`.

## Backlog

* Colour the dependency graph by **course progress** (so that students see which parts have been covered
  so far). Needs per-node metadata (e.g. a lecture tag) and a small script; currently all nodes have one
  neutral colour because Verso Blueprint's built-in colours mean *formalization status*, which does not
  apply here.
* Verso numbers the appendices 7 and 8 (legacy: A and B).
* Graph nodes show the label rather than number/title.

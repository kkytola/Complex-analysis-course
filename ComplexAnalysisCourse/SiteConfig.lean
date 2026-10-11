import VersoManual

/-!
# Site configuration (look and feel of the generated HTML)

`BlueprintMain.lean` passes `siteConfig` to the generator:
`(config := ComplexAnalysisCourse.SiteConfig.siteConfig)`.
VersoBlueprint *adds* its own assets to this configuration (`withBlueprintAssets`); it does not replace them.

## Assets

`assets/neutral-graph.css` and `assets/neutral-graph.js` give the dependency graph one neutral colour and remove
all "formalization status" wording (this project has no Lean formalization). See the header comments of those
files for what they do and which upstream class names they depend on.

The generator copies the directory `assets/` to `<site>/assets/` (`extraFilesHtml`) and every page links
`assets/neutral-graph.css` and `assets/neutral-graph.js` (`extraHead`). Such relative URLs are resolved against
the `<base>` element that Verso puts in every page, so this works at any depth and under any URL prefix
(`/Complex-analysis-course/blueprint/...`). Two consequences:

* The generator must run with the repository root as working directory (`lake exe vbp build`, as in
  `scripts/build_site.sh`); the build fails if `assets/` cannot be found.
* Editing the asset files needs no Lean rebuild; `lake exe vbp build` picks them up.
-/

open Verso.Genre.Manual
open Verso.Output.Html

namespace ComplexAnalysisCourse.SiteConfig

/-- Extra elements for the `<head>` of every page: the stylesheet and the script of `assets/`.
The script is a plain (blocking) one on purpose: it must register its start-up code before the
Verso Blueprint page runtime, which is loaded as a module and therefore starts later. -/
def siteHead : Array Verso.Output.Html := #[
  {{ <link rel="stylesheet" href="assets/neutral-graph.css"/> }},
  {{ <script src="assets/neutral-graph.js"></script> }}
]

/-- The configuration passed to the Verso Blueprint generator. -/
def siteConfig : RenderConfig where
  -- "Source Code" link in the table of contents.
  sourceLink := some "https://github.com/kkytola/Complex-analysis-course"
  -- One HTML page per chapter (as in the legacy site) instead of Verso's default of one page per section (2).
  htmlDepth := 1
  -- The first page lists the chapters together with their sections.
  rootTocDepth := some 2
  -- Copy `assets/` (relative to the working directory) to `<site>/assets/` and link it from every page.
  extraFilesHtml := [(System.FilePath.mk "assets", "assets")]
  extraHead := siteHead

end ComplexAnalysisCourse.SiteConfig

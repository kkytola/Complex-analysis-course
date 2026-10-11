import VersoManual
import VersoBlueprint.Informal.Block
import VersoBlueprint.Informal.Code
import VersoBlueprint.Math
import VersoBlueprint.Commands.Graph

/-!
# Workarounds for the PDF (TeX) output of Verso Blueprint

`withPdfFixes` is the entry point used by `BlueprintMain.lean`. It composes two independent pieces,
both implemented by rewriting entries of the `ExtensionImpls` table (no fork of the dependency).

## 1. Paragraph structure: `withParagraphBreaks`

Verso's `Part.toTeX` separates the top-level blocks of a section with a TeX paragraph break
(`Block.para` itself emits only its inlines). The TeX renderer of the Blueprint statement blocks
(`:::definition`, `:::theorem`, `:::lemma`, `:::proof`, ...), `Block.informal.toTeX`, instead does
`blocks.mapM goB` and wraps the result in a `quote` environment, *without* any separator between
the body blocks. In the generated `main.tex` all paragraphs of a node run together
(`... $x,y \in \bR$.The operations of addition ...`), the title lead-in line merges with the first
paragraph, and `\begin{itemize}` is glued to the preceding sentence.

`withParagraphBreaks` replaces the `toTeX` of the affected extensions by a wrapper that calls the
original implementation, with a block renderer `goB` that appends `Verso.Output.TeX.paragraphBreak`
after every body block. The HTML renderers, traversal, and all other descriptor fields are left
untouched. (It also adds some vertical spacing around nodes and removes a spurious blank line
before display equations; see `separateBodyBlocks` and `tightenDisplayMath`.)

The workaround becomes redundant (and harmless apart from a few extra blank lines) once upstream
`Block.informal.toTeX` separates its body blocks itself; it can then simply be dropped.

Node headings: a bold node heading directly after a sectioning command would otherwise be
separated from the section heading by the `\Needspace` (a legal page break), stranding the section
heading at the bottom of a page. `nodePrefix` therefore emits nothing in that situation (LaTeX's
`\if@nobreak`), and `keepHeadingWithBody` (memoir's `\noprelistbreak`) keeps the node heading
together with the first lines of its body.

Known limitations (Verso core, not repairable from here):
* Blocks nested *inside* a list item or a block quote are rendered by Verso's own `Block.toTeX`,
  which concatenates them without separators, so a list item consisting of two paragraphs prints
  them run together.
* The paragraphs before the first chapter of the root document are "front matter" for
  `emitTeX`, which joins them with single newlines and places them behind the table of contents
  (with the running head "CONTENTS"). The course works around this with the directive
  `:::frontIntro` of `Roles.lean`, which does not belong to this module.

## 2. Page layout and links: `withPdfLayout`

Verso's fixed TeX preamble produces Letter paper, hyperref link *boxes* (red in the table of
contents, cyan around footnote URLs) and no PDF metadata. The legacy LaTeX print version was A4 with
coloured links (`colorlinks=true, linkcolor=blue, urlcolor=magenta, citecolor=blue`).
`withPdfLayout` restores that by contributing one free-form TeX *preamble item* (the mechanism
Verso offers to extensions through `BlockDescr.preamble`/`InlineDescr.preamble`):

* `\setstocksize`/`\settrimmedsize`/`\settypeblocksize`/... (memoir): A4 paper and a type block
  of `PdfLayout.typeblockWidth` x `PdfLayout.typeblockHeight`, centred on the page;
* `\hypersetup{colorlinks=true, ...}` for the link colours;
* `\emergencystretch=3em`: a last-resort amount of extra interword stretch, which removes the
  overfull lines caused by long inline formulas (15 overfull boxes of up to 68pt in the course
  document drop to the single one that is inside a display equation) without touching the
  mathematics;
* PDF `Title`/`Author` metadata, taken at `\begin{document}` from the document's own `\title` and
  `\author` (so nothing about this course is hard-coded), unless `PdfLayout.title`/`author` are set.

Verso places the preamble items after the memoir document class, hyperref and its own `\chapterstyle`
settings and before `\title`/`\begin{document}`. Items are collected into a `HashSet`, so their
relative order is undefined: everything is therefore a single string. Items are only collected from
extensions whose blocks occur in the document, so the item is attached to several extensions
(statement blocks, Blueprint math, the dependency graph); identical strings are deduplicated.

Usage (see `BlueprintMain.lean`):
```
(extensionImpls := ComplexAnalysisCourse.TeXFixes.withPdfFixes (by exact extension_impls%))
```
-/

open Verso Doc
open Verso.Genre Manual

namespace ComplexAnalysisCourse.TeXFixes

/-- What separates two body blocks of a node: a TeX paragraph break, plus (if `spacing`) a small
vertical gap. Inside the `quote` environment that Blueprint wraps around the body, `\parindent` and
`\parskip` are both zero, so a bare paragraph break would be visible only through the short last
line of the preceding paragraph. `\addvspace` merges with the skips that list and display-math
environments add themselves, so it never stacks on top of them.

After the *first* body block (typically the one-line title lead-in `Title [Palka1991, ...]`) a page
break is discouraged (`\penalty3000`, a soft keep-with-next: TeX may still break there if nothing
better exists), so that the node heading and its lead-in are not left alone at the bottom of a
page. -/
private def blockSeparator (spacing first : Bool) : Output.TeX :=
  if spacing then
    .seq #[.paragraphBreak, .raw (if first then "\\penalty3000\n" else ""),
      .raw "\\addvspace{\\smallskipamount}\n"]
  else
    .paragraphBreak

/-- Run `render` and terminate the rendered block with a block separator; `first` tells whether
the block is the first one rendered through this renderer. -/
private def withSeparator {m : Type → Type} [Monad m] [MonadLiftT BaseIO m] (spacing : Bool)
    (isFirst : IO.Ref Bool) (render : Doc.Block Manual → m Output.TeX) (b : Doc.Block Manual) :
    m Output.TeX := do
  let out ← render b
  let first ← (isFirst.modifyGet fun f => (f, false) : BaseIO Bool)
  pure <| .seq #[out, blockSeparator spacing first]

/-- The TeX that goes before a node: a little vertical space above the bold heading and a
`\Needspace` (memoir) so that the heading is not stranded at the bottom of a page.

Directly after a sectioning command (`\section`, `\chapter`, ...) LaTeX's `\if@nobreak` is true
until the first paragraph starts: the heading is then kept together with what follows. A
`\Needspace` there would be a legal page break *between the section heading and the node* and
strand the section heading at the bottom of the page. In that case emit nothing (see
`keepHeadingWithBody` for the heading of the node itself). -/
private def nodePrefix : Output.TeX :=
  .raw ("\\makeatletter\\if@nobreak\\else\\par\\addvspace{\\medskipamount}" ++
    "\\Needspace{4\\baselineskip}\\fi\\makeatother\n")

/-- Keep the bold node heading (`Informal.TeX.boldHeading`: `\par\noindent\textbf{..}\par`
followed by the body environment) on the same page as the first lines of the body: memoir's
`\noprelistbreak` suppresses the page break that LaTeX would otherwise allow before the `quote`
list. Output of any other shape is returned unchanged. -/
private def keepHeadingWithBody (out : Output.TeX) : Output.TeX :=
  match out with
  | .seq #[pre@(.raw "\\par\\noindent"), head, post@(.raw "\\par\n"), body] =>
    .seq #[pre, head, post, .raw "\\noprelistbreak\n", body]
  | _ => out

/-- Make the `toTeX` of the block extension `name` separate its body blocks by paragraph breaks.
Does nothing if the extension (or its TeX renderer) is not registered.

With `spacing := true`, additionally put a little vertical space above the bold node heading
(`Definition 1.1`) and keep it together with the first lines of the body (`nodePrefix`,
`keepHeadingWithBody`). The Blueprint renderer does neither: a node otherwise sits flush against the
preceding paragraph and its heading can be stranded at the bottom of a page. -/
def separateBodyBlocks (name : Lean.Name) (spacing : Bool := true) (impls : ExtensionImpls) :
    ExtensionImpls :=
  match impls.getBlock? name with
  | none => impls
  | some descr =>
    match descr.toTeX with
    | none => impls
    | some original =>
      impls.insertBlock name
        { descr with
          toTeX := some fun goI goB id data blocks => do
            let isFirst ← IO.mkRef true
            let out ← original goI (withSeparator spacing isFirst goB) id data blocks
            if spacing then
              pure <| .seq #[nodePrefix, keepHeadingWithBody out]
            else
              pure out }

/-- `Inline.bpMath` emits a display-style source (`align*`, `\[ ... \]`, ...) as `"\n" ++ source ++
"\n"`. After the soft line break that usually precedes a display equation in the Verso source
(`... the formulas` newline `$$`...``) this makes a blank line, i.e. a spurious paragraph break
before the display, which TeX turns into an empty line plus the display skip. Drop the leading
newline so that the display stays inside its paragraph. -/
def tightenDisplayMath (impls : ExtensionImpls) : ExtensionImpls :=
  match impls.getInline? ``Informal.Math.Inline.bpMath with
  | none => impls
  | some descr =>
    match descr.toTeX with
    | none => impls
    | some original =>
      impls.insertInline ``Informal.Math.Inline.bpMath
        { descr with
          toTeX := some fun goI id data contents => do
            match ← original goI id data contents with
            | .raw s => pure <| .raw (if s.startsWith "\n" then (s.drop 1).toString else s)
            | out => pure out }

/-- Repair the paragraph structure of the TeX/PDF output:

* statement and proof blocks (`Block.informal`) and Lean-code blocks (`Block.informalCode`) get
  paragraph breaks between their body blocks (and, with `spacing := true`, some vertical space
  around them, see `separateBodyBlocks`);
* display equations no longer introduce a spurious blank line (see `tightenDisplayMath`).

`spacing := false` restricts the first fix to the bare paragraph breaks. -/
def withParagraphBreaks (impls : ExtensionImpls) (spacing : Bool := true) : ExtensionImpls :=
  impls
    |> separateBodyBlocks ``Informal.Block.informal spacing
    |> separateBodyBlocks ``Informal.Block.informalCode spacing
    |> tightenDisplayMath

/-- Parameters of `withPdfLayout`. The defaults reproduce the look of the legacy print version:
A4 paper, blue internal links, magenta URLs. Lengths are TeX lengths. -/
structure PdfLayout where
  /-- Paper (stock) height. -/
  stockHeight : String := "297mm"
  /-- Paper (stock) width. -/
  stockWidth : String := "210mm"
  /-- Height of the type block (the area holding running text, without header/footer). -/
  typeblockHeight : String := "225mm"
  /-- Width of the type block. The block is centred horizontally. -/
  typeblockWidth : String := "140mm"
  /-- Ratio of the upper to the lower margin (memoir's `\setulmargins`). -/
  upperLowerRatio : String := "0.8"
  /-- Colour of internal links (table of contents, cross-references). -/
  linkColor : String := "blue"
  /-- Colour of URLs. -/
  urlColor : String := "magenta"
  /-- Colour of citations. -/
  citeColor : String := "blue"
  /-- PDF metadata title, as TeX. `none`: use the document's `\title`. -/
  title : Option String := none
  /-- PDF metadata author, as TeX. `none`: use the document's `\author`. -/
  author : Option String := none

/-- The preamble item that implements `PdfLayout`; one string, because the order of different
preamble items is not defined (see the module documentation). -/
def PdfLayout.preambleItem (l : PdfLayout) : String :=
  let title := l.title.getD "\\@title"
  let author := l.author.getD "\\@author"
  String.intercalate "\n" [
    "% PDF page layout and link colours (ComplexAnalysisCourse.TeXFixes.withPdfLayout)",
    s!"\\setstocksize\{{l.stockHeight}}\{{l.stockWidth}}",
    "\\settrimmedsize{\\stockheight}{\\stockwidth}{*}",
    s!"\\settypeblocksize\{{l.typeblockHeight}}\{{l.typeblockWidth}}\{*}",
    "\\setlrmargins{*}{*}{1}",
    s!"\\setulmargins\{*}\{*}\{{l.upperLowerRatio}}",
    "\\checkandfixthelayout",
    -- Allow looser spacing as a last resort before a line (typically one with a long inline
    -- formula) sticks out into the margin.
    "\\setlength{\\emergencystretch}{3em}",
    s!"\\hypersetup\{colorlinks=true,linkcolor={l.linkColor},urlcolor={l.urlColor},citecolor={l.citeColor}}",
    "\\makeatletter",
    s!"\\AtBeginDocument\{\\hypersetup\{pdftitle=\{{title}},pdfauthor=\{{author}}}}",
    "\\makeatother"]

/-- Add the preamble item `item` to `name` (a block extension) if it is registered. -/
private def addBlockPreamble (item : String) (name : Lean.Name) (impls : ExtensionImpls) :
    ExtensionImpls :=
  match impls.getBlock? name with
  | none => impls
  | some descr => impls.insertBlock name { descr with preamble := descr.preamble ++ [item] }

/-- Add the preamble item `item` to `name` (an inline extension) if it is registered. -/
private def addInlinePreamble (item : String) (name : Lean.Name) (impls : ExtensionImpls) :
    ExtensionImpls :=
  match impls.getInline? name with
  | none => impls
  | some descr => impls.insertInline name { descr with preamble := descr.preamble ++ [item] }

/-- Switch the PDF to A4 with a sensible memoir type block, coloured links instead of link boxes,
and PDF title/author metadata; see the module documentation. -/
def withPdfLayout (impls : ExtensionImpls) (layout : PdfLayout := {}) : ExtensionImpls :=
  let item := layout.preambleItem
  impls
    |> addBlockPreamble item ``Informal.Block.informal
    |> addBlockPreamble item ``Informal.Commands.Block.graph
    |> addInlinePreamble item ``Informal.Math.Inline.bpMath

/-- All PDF workarounds: `withParagraphBreaks` and `withPdfLayout`. -/
def withPdfFixes (impls : ExtensionImpls) (layout : PdfLayout := {}) : ExtensionImpls :=
  withPdfLayout (withParagraphBreaks impls) layout

end ComplexAnalysisCourse.TeXFixes

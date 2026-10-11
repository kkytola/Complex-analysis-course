import VersoManual

/-!
# Text-level macros (Verso roles)

LaTeX text macros cannot be used in Verso text. The few that the course text uses are roles instead,
so that their appearance is defined in one place. (Math macros live in `Macros.lean`.)

Usage in a chapter:  `{term}[linear map]`,  `{palka}[Thm V.1.5]`,  `{nodetitle}[Goursat's lemma]`,
`{metSpCourse}[]`.  Roles must live in a module that is *imported* by the chapters.
The directive `:::frontIntro` (end of this file) wraps the introduction of the root document.
-/

open Verso Doc Elab
open Verso.Genre Manual

/-- A defined term; replaces `\term{..}`. -/
@[role]
def term : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.bold #[$content,*])

/-- A reference to the textbook; replaces `\Palka{Thm~V.1.5}`: `{palka}[Thm V.1.5]` shows
`[Palka1991, Thm V.1.5]`. -/
@[role]
def palka : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.concat #[Inline.text "[Palka1991, ", $content,*, Inline.text "]"])

/-- The title of a theorem-like node (the optional `[Title]` argument of the old LaTeX environments).
Verso node headers have no title slot, so the title is the first line of the node body. -/
@[role]
def nodetitle : RoleExpanderOf Unit
  | (), content => do
    let content ← content.mapM elabInline
    ``(Inline.emph #[$content,*])

/-- The name of the metric spaces course; replaces `\MetSpCourse`: `{metSpCourse}[]`. -/
@[role]
def metSpCourse : RoleExpanderOf Unit
  | (), _ => ``(Inline.bold #[Inline.text "MS-C1541 Metric Spaces"])

/-!
## The introduction of the root document: `:::frontIntro`

The paragraphs before the first chapter of the root document are *front matter* for Verso's TeX
backend (`emitTeX`), which writes them behind the table of contents, with only a single newline
between two blocks. In the PDF the introduction therefore ran together into ONE paragraph, on a
page that carries the running head "CONTENTS". The directive `:::frontIntro` wraps the
introduction in one block whose

* HTML rendering is just its content (the root page looks exactly as without the wrapper),
* TeX rendering separates the paragraphs, suppresses the running head (`\thispagestyle{plain}`) and
  moves the table of contents *behind* the introduction (title page, introduction, table of
  contents, chapters; as in the legacy print version the introduction follows the title page).

Moving the table of contents: Verso's fixed preamble contains `\tableofcontents`. The block's
preamble item (collected only if the block occurs in the document) saves the command as
`\introTableOfContents` and turns `\tableofcontents` into a no-op; the TeX of the block calls
`\introTableOfContents` (on a new page) after the introduction. Use the directive at most once,
directly in the root part (the only place where Verso emits front matter).

Side effects on the HTML output (inherent to adding a block): the dependency graph's internal id
number is one higher; the search-index text of the root page has no newline between the
introduction's paragraphs (a few words at paragraph boundaries are indexed as one token).
-/

block_extension Block.frontIntro where
  traverse := fun _ _ _ => pure none
  preamble := [String.intercalate "\n" [
    "% The introduction precedes the table of contents (Block.frontIntro in Roles.lean)",
    "\\let\\introTableOfContents\\tableofcontents",
    "\\renewcommand{\\tableofcontents}{}"]]
  toHtml := some fun _ goB _ _ content => content.mapM goB
  toTeX := some fun _ goB _ _ content => do
    let body ← content.mapM fun b => do
      pure <| Verso.Output.TeX.seq #[← goB b, .paragraphBreak]
    pure <| .seq <| #[.raw "\\thispagestyle{plain}\n"] ++ body ++ #[.raw "\\clearpage\n\\introTableOfContents\n"]

/-- The introduction of the root document; see the section comment above. -/
@[directive]
def frontIntro : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Block.other Block.frontIntro #[$(← contents.mapM elabBlock),*])

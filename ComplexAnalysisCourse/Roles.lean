import VersoManual

/-!
# Text-level macros (Verso roles)

LaTeX text macros cannot be used in Verso text. The few that the course text uses are roles instead,
so that their appearance is defined in one place. (Math macros live in `Macros.lean`.)

Usage in a chapter:  `{term}[linear map]`,  `{palka}[Thm V.1.5]`,  `{nodetitle}[Goursat's lemma]`,
`{metSpCourse}[]`.  Roles must live in a module that is *imported* by the chapters.
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

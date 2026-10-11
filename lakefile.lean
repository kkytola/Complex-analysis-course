import Lake
open Lake DSL

-- The theory skeleton is a pure Verso Blueprint document: there is no Lean formalization attached,
-- so the toolchain simply follows the release line of VersoBlueprint (see lean-toolchain).
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.35.0"

package ComplexAnalysisCourse where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    -- Statement numbering per chapter with one shared counter, as in the legacy blueprint ("Lemma 2.2").
    ⟨`weak.verso.blueprint.subNumberingPrefix, "first"⟩,
    -- Proofs are collapsed by default (the old "show more" behaviour).
    ⟨`weak.verso.blueprint.foldProofBlocks, true⟩
  ]

-- All modules below `ComplexAnalysisCourse` are built (including `MacroGallery`, which lints every macro).
@[default_target]
lean_lib ComplexAnalysisCourse where
  globs := #[.andSubmodules `ComplexAnalysisCourse]

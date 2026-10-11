import VersoManual
import VersoBlueprint.PreviewManifest
import ComplexAnalysisCourse.Blueprint
import ComplexAnalysisCourse.TeXFixes
import ComplexAnalysisCourse.SiteConfig

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ComplexAnalysisCourse.Blueprint)
    args
    (extensionImpls := ComplexAnalysisCourse.TeXFixes.withPdfFixes (by exact extension_impls%))
    (config := ComplexAnalysisCourse.SiteConfig.siteConfig)

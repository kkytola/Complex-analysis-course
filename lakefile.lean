import Lake
open Lake DSL

package «ComplexAnalysisCourse» where
  -- add package configuration options here

lean_lib «ComplexAnalysisCourse» where
  -- add library configuration options here

@[default_target]
lean_exe «complexanalysiscourse» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
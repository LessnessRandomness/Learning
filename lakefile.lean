import Lake
open Lake DSL

package «Learning» where
  -- add package configuration options here

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib «Learning» where
  -- add library configuration options here

@[default_target]
lean_exe «learning» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

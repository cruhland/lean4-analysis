
import Lake
open System Lake DSL

package «lean4-analysis» {
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    -- This linter rule can make proof readability harder in some cases.
    ⟨`linter.tacticAnalysis.introMerge, false⟩,
  ]
}

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"

require «lean4-axiomatic» from
  /- If you need to pick up local changes to this library, uncomment the line
   - below (and comment out the `git` line). Be sure to edit the path prefix to
   - match your local setup. Then run `lake update` to reload the build config.
   -/
  -- ".."/"lean4-axiomatic"
  git axiomatic_url @ "main"

lean_lib Lean4Analysis {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-analysis» {
  root := `Main
}

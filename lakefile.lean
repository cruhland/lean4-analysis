import Lake
open System Lake DSL

package «lean4-analysis» {
  moreLeanArgs := #["-D warningAsError=true"]
}

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"
def axiomatic_rev := "386b8c43ae6a4a54c2f2ea052c02887907796984"

require «lean4-axiomatic» from
  /- If you need to pick up local changes to this library, uncomment the line
   - below (and comment out the `git` line). Be sure to edit the path prefix to
   - match your local setup. Then run `lake update` to reload the build config.
   -/
  -- ".."/"lean4-axiomatic"
  git axiomatic_url @ axiomatic_rev

lean_lib Lean4Analysis {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-analysis» {
  root := `Main
}

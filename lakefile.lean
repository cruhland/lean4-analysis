
import Lake
open System Lake DSL

package «lean4-analysis» {
  moreLeanArgs := #["-D warningAsError=true"]
}

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"
def axiomatic_rev := "4d77cebdd63255cb8e60c60285bf35e40920321d"

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

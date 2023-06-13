import Lake
open System Lake DSL

package «lean4-analysis» {
  moreLeanArgs := #["-D warningAsError=true"]
}

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"
def axiomatic_rev := "c7f07478dfad8b321cbfb05298c5ecfe184bcd35"

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

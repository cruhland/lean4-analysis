import Lake
open System Lake DSL

package «lean4-analysis»
-- add package configuration options here

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"
def axiomatic_rev := "5605c3a5008480fd0a386e22f0d56cb6cfcd5f03"

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

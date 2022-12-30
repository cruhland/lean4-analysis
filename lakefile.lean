import Lake
open System Lake DSL

package «lean4-analysis»
-- add package configuration options here

def axiomatic_url := "https://github.com/cruhland/lean4-axiomatic.git"
def axiomatic_rev := "3fa8f23df2f82dd4f7f7d9136403c5072fa908f1"

require «lean4-axiomatic» from
  -- If you need to pick up local changes to this library, use this alternative
  -- source instead, after editing the path prefix to match your personal setup
  -- ".."/"lean4-axiomatic"
  git axiomatic_url @ axiomatic_rev

lean_lib Lean4Analysis {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-analysis» {
  root := `Main
}

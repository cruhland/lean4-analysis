import Lake
open Lake DSL

package «lean4-analysis» {
  dependencies := #[
    {
      name := `«lean4-axiomatic»
      src := Source.git "https://github.com/cruhland/lean4-axiomatic.git" "main"
    }
  ]
}

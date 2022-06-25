import Lake
open Lake DSL
open System

package «lean4-analysis» {
  dependencies := #[
    {
      name := `«lean4-axiomatic»
      -- If you need to pick up local changes to this library, use this
      -- alternative `src` setting instead, after changing the path prefix to
      -- match your personal setup
      -- src := Source.path (FilePath.mk ".." / "lean4-axiomatic")
      src := Source.git
        "https://github.com/cruhland/lean4-axiomatic.git"
        "efbc3c53a9e9a11888719fc29b5cf40be5ad0c91"
    }
  ]
}

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
        "3ac3afd19a5c224072c321843bc9e4feb1abb0fa"
    }
  ]
}

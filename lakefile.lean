import Lake
open Lake DSL

package «sia» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «SIA» where
  srcDir := "."

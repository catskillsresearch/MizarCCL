import Lake
open Lake DSL

package «MizarCCL» where
  version := v!"0.1.0"

/-!
1–1 translation of the used-module closure of YELLOW* / WAYBEL*.
One Lean module per Mizar article, imported from `MizarCCL.lean`.
No Mathlib: Mizar set theory is untyped Tarski–Grothendieck.
`Challenge` / `Solution` are the Palomar surface for `TARSKI`.
-/

@[default_target]
lean_lib MizarCCL where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, true⟩
  ]

@[default_target]
lean_lib Challenge

@[default_target]
lean_lib Solution

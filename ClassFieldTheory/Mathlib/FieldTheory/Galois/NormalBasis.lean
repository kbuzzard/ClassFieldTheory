import Mathlib.FieldTheory.Galois.Basic

-- Sorry-free version is in https://github.com/leanprover-community/mathlib4/pull/27390
namespace IsGalois
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

variable (K L) in
/-- Given a finite Galois extension `L/K`, `normalBasis K L` is a basis of `L` over `K`
that is an orbit under the Galois group action. -/
noncomputable def normalBasis : Basis (L ≃ₐ[K] L) K L := sorry

theorem normalBasis_apply (e : L ≃ₐ[K] L) : normalBasis K L e = e (normalBasis K L 1) := sorry

end IsGalois

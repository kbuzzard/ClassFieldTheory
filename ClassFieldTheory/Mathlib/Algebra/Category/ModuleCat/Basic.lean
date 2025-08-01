import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory Limits

namespace ModuleCat
variable {R : Type*} [Ring R]

lemma isZero_iff_subsingleton {M : ModuleCat R} : IsZero M ↔ Subsingleton M where
  mp := subsingleton_of_isZero
  mpr _ := isZero_of_subsingleton M

@[simp]
lemma isZero_of_iff_subsingleton {M : Type*} [AddCommGroup M] [Module R M] :
    IsZero (of R M) ↔ Subsingleton M := isZero_iff_subsingleton

end ModuleCat

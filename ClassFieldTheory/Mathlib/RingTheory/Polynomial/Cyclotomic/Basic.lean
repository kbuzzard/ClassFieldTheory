import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} {ζ : R}

-- with much more effort are the following generalisable to CommRing

theorem X_pow_sub_one_factors (hζ : IsPrimitiveRoot ζ n) :
    (X ^ n - 1 : R[X]).Factors := by
  obtain _ | n := n
  · simp
  rw [X_pow_sub_one_eq_prod n.succ_pos hζ]
  aesop

theorem X_pow_sub_X_factors (hζ : IsPrimitiveRoot ζ (n - 1)) :
    (X ^ n - X : R[X]).Factors := by
  obtain _ | n := n
  · rw [← neg_sub, pow_zero]
    exact .neg <| .X_sub_C 1
  rw [pow_succ, ← sub_one_mul]
  exact .mul (X_pow_sub_one_factors hζ) .X

end Polynomial

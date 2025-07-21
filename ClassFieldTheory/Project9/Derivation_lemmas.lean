/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic



open Polynomial Finset Derivation Algebra BigOperators

variable {R A M : Type*}

/-
  TODO : If `Polynomial.derivation_ext` is added (a version of
  `mv_polynomial.derivation_ext` for one variable) then there would be a simpler proof
  of the following result:
  Show that both sides of the equation are derivations
  on the polynomial ring (when regarded as functions of `f`).
  Then by `ext`, they are equal iff they agree in the case `f = X`.
  This case is follows from `eval₂_X` and `eval₂_one`.
-/

/--
  If `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation
  then for all `a : A` we have

    `d(f(a)) = f.derivative (a) * d a`.
-/
theorem Derivation.polynomial_eval₂ [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (d : Derivation R A M) (f : R[X]) (a : A) :
  d (f.eval₂ (algebraMap R A) a) = f.derivative.eval₂ (algebraMap R A) a • d a :=
by
  rw [eval₂_eq_sum_range, map_sum, sum_range_succ', leibniz,
    leibniz_pow, map_algebraMap, zero_nsmul, smul_zero, smul_zero,
    zero_add, add_zero]
  by_cases h : f.natDegree = 0
  · rw [h, sum_range_zero, derivative_of_natDegree_zero h, eval₂_zero, zero_smul]
  · have : f.derivative.natDegree < f.natDegree := natDegree_derivative_lt h
    rw [eval₂_eq_sum_range' (hn := this), sum_smul]
    apply sum_congr rfl
    intro x hx
    rw [leibniz, leibniz_pow, map_algebraMap, smul_zero, add_zero,
      add_tsub_cancel_right, coeff_derivative, map_mul, IsScalarTower.algebraMap_smul,
      algebraMap_eq_smul_one, algebraMap_eq_smul_one, smul_mul_assoc,
      mul_smul_comm, one_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
      smul_assoc, smul_assoc, ←Nat.cast_succ, Nat.cast_smul_eq_nsmul]

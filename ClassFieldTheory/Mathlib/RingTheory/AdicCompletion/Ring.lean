/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Duplication of API for IsAdicComplete

Specialised to the situation `IsAdicComplete I R`.

-/

open Ideal Quotient

variable {R : Type*} [CommRing R] {I : Ideal R}

theorem Submodule.factorPow_eq_factorPow {m n : ℕ} (h : m ≤ n) :
    ⇑(factorPow I R h) = Ideal.quotEquivOfEq (by simp) ∘
      Ideal.Quotient.factorPow I h ∘ Ideal.quotEquivOfEq (by simp) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem Ideal.quotEquivOfEq_trans {I₁ I₂ I₃ : Ideal R} (h12 : I₁ = I₂) (h23 : I₂ = I₃) :
    (quotEquivOfEq h12).trans (quotEquivOfEq h23) = quotEquivOfEq (h12.trans h23) :=
  RingEquiv.toRingHom_injective <| ringHom_ext rfl

theorem Ideal.quotEquivOfEq_rfl :
    quotEquivOfEq (rfl : I = I) = .refl _ :=
  RingEquiv.toRingHom_injective <| ringHom_ext rfl

theorem Ideal.Quotient.factorPow_comp_factorPow {m n p : ℕ} (h1 : m ≤ n) (h2 : n ≤ p) :
    (factorPow I h1).comp (factorPow I h2) = factorPow I (h1.trans h2) :=
  ringHom_ext rfl

def AdicCompletion.mkRing (f : ∀ n, R ⧸ I ^ n) (hf : ∀ n, factorPowSucc I n (f (n + 1)) = f n) :
    AdicCompletion I R := by
  refine ⟨fun n ↦ quotEquivOfEq (by simp) (f n), fun {m n} h ↦ ?_⟩
  simp_rw [transitionMap, Submodule.factorPow_eq_factorPow, Function.comp_apply,
    EmbeddingLike.apply_eq_iff_eq, ← RingEquiv.trans_apply, quotEquivOfEq_trans,
    quotEquivOfEq_rfl, RingEquiv.refl_apply]
  induction h with
  | refl => simp
  | step h ih =>
    rw [← ih, eq_comm, ← hf, ← RingHom.comp_apply, factorPow_comp_factorPow]

theorem AdicCompletion.mk_ofLinearEquiv_symm_mkRing
    [IsAdicComplete I R] {f : ∀ n, R ⧸ I ^ n} {hf} {n : ℕ} :
    Ideal.Quotient.mk (I ^ n) ((ofLinearEquiv I R).symm (.mkRing f hf)) = f n := by
  generalize hx : (ofLinearEquiv I R).symm _ = x
  rw [LinearEquiv.symm_apply_eq] at hx
  have h : I ^ n • ⊤ = I ^ n := by simp
  convert congr(quotEquivOfEq h ($(hx.symm).val n))
  simp_rw [mkRing, ← RingEquiv.trans_apply, quotEquivOfEq_trans, quotEquivOfEq_rfl]
  rfl

theorem IsHausdorff.eq_iff_eq [IsHausdorff I R] {x y : R} :
    x = y ↔ ∀ n, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y := by
  simp_rw [IsHausdorff.eq_iff_smodEq (I := I), SModEq, mk_eq_mk]
  refine forall_congr' fun n ↦ ?_
  rw [← (quotEquivOfEq <| show I ^ n • ⊤ = I ^ n by simp).injective.eq_iff]
  rfl

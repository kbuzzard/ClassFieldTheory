/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Cohomology.IsFilterComplete.Basic
import Mathlib.LinearAlgebra.Pi

/-! # Complete filtrations by submodules

This file constructs more complete filtrations by:
1. Pi, i.e. if `M_` is complete then `fun i ↦ (M_ i)^α` is complete.
2. passing to a submodule `s` satisfying the magic condition `(⨅ i, (M_ i ⊔ s)) = s`.
3. kernel of a map that respects the filtration
4. isomorphism that respects the filtration
-/

-- TODO: more API (e.g. SModEq)

open Submodule LinearMap

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [LE ι] {M_ : ι → Submodule R M} {N_ : ι → Submodule R N}

namespace Submodule
variable {α : Type*} {s : Set α}

theorem pi_sup {w₁ w₂ : α → Submodule R M} :
    pi s (fun i ↦ w₁ i ⊔ w₂ i) = pi s w₁ ⊔ .pi s w₂ := by
  refine le_antisymm ?_ (sup_le (pi_mono fun _ _ ↦ le_sup_left) (pi_mono fun _ _ ↦ le_sup_right))
  intro x
  simp only [mem_pi, mem_sup]
  intro hx
  choose y hy z hz hyz using hx
  classical
  refine ⟨fun i ↦ if H : i ∈ s then y i H else x i, ?_,
    fun i ↦ if H : i ∈ s then z i H else 0, ?_, ?_⟩
  · simpa +contextual
  · simpa +contextual
  · ext i
    simp only [Pi.add_apply]
    split_ifs <;> simp [*]

theorem pi_iInf {ι : Sort*} {w : α → ι → Submodule R M} :
    (pi s fun a ↦ ⨅ i, w a i) = ⨅ i, pi s fun a ↦ w a i := by
  ext; simpa using by tauto

theorem submoduleOf_iInf {ι : Sort*} {w₁ : ι → Submodule R M} {w₂ : Submodule R M} :
    (⨅ i, w₁ i).submoduleOf w₂ = ⨅ i, (w₁ i).submoduleOf w₂ := by simp [submoduleOf]

@[simp] theorem submoduleOf_bot {w : Submodule R M} :
    (⊥ : Submodule R M).submoduleOf w = ⊥ := by simp [submoduleOf]

theorem submoduleOf_sup_le {w₁ w₂ w : Submodule R M} :
    w₁.submoduleOf w ⊔ w₂.submoduleOf w ≤ (w₁ ⊔ w₂).submoduleOf w :=
  sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)

end Submodule

def FilterCauchySeq.mkSubmodule (x : ι → M) (hx : ∀ ⦃i j : ι⦄, i ≤ j → x i - x j ∈ M_ i ⊔ M_ j) :
    FilterCauchySeq M_ :=
  ⟨x, by simpa [set, AddSubgroup.mem_sup, mem_sup] using hx⟩

namespace Filtration

@[simp] theorem iInf_eq_bot_submodule [IsFilterHausdorff M_] : (⨅ i, M_ i) = ⊥ :=
  eq_bot_iff.mpr fun _ hx ↦ eq_zero M_ <| (mem_iInf _).mp hx

end Filtration

namespace IsFilterComplete

-- restatement in terms of submodules
theorem mk_submodule (haus : ⨅ i, M_ i = ⊥)
    (prec : ∀ (x : ι → M), (∀ ⦃i j : ι⦄, i ≤ j → x i - x j ∈ M_ i ⊔ M_ j) →
      ∃ L, ∀ i, x i - L ∈ M_ i) :
    IsFilterComplete M_ where
  haus' x hx := (mem_bot R).mp <| haus ▸ (mem_iInf _).mpr hx
  prec' := by simpa [AddSubgroup.mem_sup, Submodule.mem_sup] using prec

variable (M_) [IsFilterComplete M_]

instance piLeft (α : Type*) :
    IsFilterComplete fun i ↦ Submodule.pi .univ fun _ : α ↦ (M_ i) := mk_submodule
  (by simp [← Submodule.pi_iInf]) fun x hx ↦
  ⟨fun a ↦ limit M_ <| .mk _ <| .mkSubmodule (x · a) fun i j hij ↦ by
      simp only [← pi_sup] at hx; exact hx hij _ trivial,
    fun i _ _ ↦ sub_mem_symm <| limit_sub_mem ..⟩

variable {M_}

theorem submoduleOf {s : Submodule R M} (hs : (⨅ i, (M_ i ⊔ s)) ≤ s) :
    IsFilterComplete fun i ↦ (M_ i).submoduleOf s := .mk_submodule
  (by simp [← submoduleOf_iInf]) fun x hx ↦
  let f : FilterCauchySeq M_ := .mkSubmodule (x ·) fun _ _ h ↦ submoduleOf_sup_le <| hx h
  ⟨⟨limit M_ <| .mk _ <| f, hs <| (mem_iInf _).mpr fun i ↦ mem_sup.mpr
    ⟨_, limit_sub_mem M_ f, _, (x i).2, sub_add_cancel _ _⟩⟩, fun i ↦ sub_limit_mem M_ f⟩

theorem ker [IsFilterHausdorff N_] (f : M →ₗ[R] N) (hf : ∀ ⦃x i⦄, x ∈ M_ i → f x ∈ N_ i) :
    IsFilterComplete fun i ↦ (M_ i).submoduleOf (ker f) :=
  submoduleOf fun x hx ↦ Filtration.eq_zero N_ fun i ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp <| (mem_iInf _).mp hx i
    rw [map_add, hz, add_zero]
    exact hf hy

theorem of_iso (e : M ≃ₗ[R] N) (he : ∀ ⦃x⦄ i, x ∈ M_ i ↔ e x ∈ N_ i) :
    IsFilterComplete N_ := by
  have he' := e.symm.surjective.forall.mp he
  simp_rw [e.apply_symm_apply] at he'
  have hn (i) : M_ i = (N_ i).comap e.toLinearMap := by ext; exact he _
  have hn' (i) : N_ i = (M_ i).map e.toLinearMap :=
    hn i ▸ (map_comap_eq_of_surjective e.surjective _).symm
  refine mk_submodule (comap_injective_of_surjective e.surjective ?_) ?_
  · simp_rw [comap_iInf, ← hn, Filtration.iInf_eq_bot_submodule, comap_bot]
    exact e.ker.symm
  · intro x hx
    let f : FilterCauchySeq M_ := .mkSubmodule (e.symm ∘ x) fun i j h ↦ by
      specialize hx h
      simp_rw [hn', ← Submodule.map_sup] at hx
      conv_lhs at hx => exact map_equiv_eq_comap_symm ..
      simp_rw [Function.comp_apply, ← map_sub]
      exact hx
    refine ⟨e <| limit M_ <| .mk _ <| f, fun i ↦ ?_⟩
    rw [← e.apply_symm_apply (x i), ← map_sub, ← he]
    exact sub_mem_symm <| limit_sub_mem ..

end IsFilterComplete

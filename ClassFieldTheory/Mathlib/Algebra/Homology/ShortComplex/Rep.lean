/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Rep

universe u

variable {k G : Type u} [CommRing k] [Monoid G] {A : Rep k G}

open CategoryTheory ShortComplex ShortExact Limits

instance : HasForget₂ (Rep k G) Ab where
  forget₂ := forget₂ (Rep k G) (ModuleCat k) ⋙ (forget₂ _ _)

instance : (forget₂ (Rep k G) Ab).Additive := ⟨rfl⟩

instance : PreservesLimits (forget₂ (Rep k G) Ab) :=
  comp_preservesLimits _ _

instance : PreservesColimits (forget₂ (Rep k G) Ab) :=
  comp_preservesColimits _ _

theorem CategoryTheory.ShortComplex.rep_exact_iff
    {k G : Type u} [CommRing k] [Monoid G] {S : ShortComplex (Rep k G)} :
    S.Exact ↔ ∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂ :=
  CategoryTheory.ShortComplex.exact_iff_of_hasForget S

-- move
theorem CategoryTheory.ShortComplex.ShortExact.rep_exact_iff_function_exact
    {k G : Type u} [CommRing k] [Monoid G] {S : ShortComplex (Rep k G)} :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [← exact_map_iff_of_faithful (F := forget₂ _ (ModuleCat k)),
    moduleCat_exact_iff_function_exact]
  rfl

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Cohomology.Subrep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short exact sequences associated to subreps -/

universe u

variable {k G : Type u} [CommRing k] [Monoid G] {A : Rep k G} (w w₁ w₂ : Subrep A)

open CategoryTheory ShortComplex ShortExact

-- move
theorem CategoryTheory.ShortComplex.rep_exact_iff
    {k G : Type u} [CommRing k] [Monoid G] {S : ShortComplex (Rep k G)} :
    S.Exact ↔ ∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂ := by
  rw [← exact_map_iff_of_faithful (F := forget₂ _ (ModuleCat k)), moduleCat_exact_iff]; rfl

-- move
theorem CategoryTheory.ShortComplex.ShortExact.rep_exact_iff_function_exact
    {k G : Type u} [CommRing k] [Monoid G] {S : ShortComplex (Rep k G)} :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [← exact_map_iff_of_faithful (F := forget₂ _ (ModuleCat k)),
    moduleCat_exact_iff_function_exact]
  rfl

namespace Subrep

/-- `0 ⟶ w ⟶ A ⟶ A⧸w ⟶ 0` -/
noncomputable def shortComplex : ShortComplex (Rep k G) where
  f := w.subtype
  g := w.mkQ
  zero := by ext; exact (LinearMap.exact_subtype_mkQ _).apply_apply_eq_zero _

theorem shortExact : w.shortComplex.ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr <| Submodule.subtype_injective _
  epi_g := (Rep.epi_iff_surjective _).mpr <| Submodule.mkQ_surjective _
  exact := rep_exact_iff_function_exact.mpr <| LinearMap.exact_subtype_mkQ _

variable {w₁ w₂} (h : w₂ ≤ w₁)

-- should we have a delab to always show `w₁` and `w₂`?
/-- `0 ⟶ w₂ ⟶ w₁ ⟶ w₁ ⧸ w₂ ⟶ 0` -/
noncomputable def shortComplexOfLE : ShortComplex (Rep k G) where
  f := w₂.inclusion h
  g := (w₂.subrepOf w₁).mkQ
  zero := by ext x; exact Submodule.Quotient.mk_eq_zero _ |>.mpr x.2

noncomputable def shortComplexOfLEIso :
    (w₁.shortComplexOfLE h) ≅ (w₂.subrepOf w₁).shortComplex :=
  isoMk (w₂.subrepOfIsoOfLE h).symm (Iso.refl _) (Iso.refl _)

theorem shortExact_of_le : (shortComplexOfLE h).ShortExact :=
  shortExact_of_iso (shortComplexOfLEIso h).symm <| shortExact _

end Subrep

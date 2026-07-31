/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import ClassFieldTheory.Cohomology.Subrep.Basic
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.Rep
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Short exact sequences associated to subreps -/

@[expose] public section

universe w w' u v

variable {k : Type u} {G : Type v} {V : Type w'} [CommRing k] [Monoid G] [AddCommGroup V]
    [Module k V] {ρ : Representation k G V} (w w₁ w₂ : Subrepresentation ρ)

open CategoryTheory ShortComplex ShortExact Limits

namespace Subrepresentation

/-- `0 ⟶ w ⟶ A ⟶ A⧸w ⟶ 0` -/
@[simps, implicit_reducible]
def shortComplex : ShortComplex (Rep.{w'} k G) where
  f := w.toRepSubtype
  g := w.toRepMkQ
  zero := by ext; exact (LinearMap.exact_subtype_mkQ _).apply_apply_eq_zero _

theorem shortExact : w.shortComplex.ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr <| Submodule.subtype_injective _
  epi_g := (Rep.epi_iff_surjective _).mpr <| Submodule.mkQ_surjective _
  exact := rep_exact_iff_function_exact.mpr <| LinearMap.exact_subtype_mkQ _

variable {w₁ w₂} (h : w₂ ≤ w₁)

-- should we have a delab to always show `w₁` and `w₂`?
/-- `0 ⟶ w₂ ⟶ w₁ ⟶ w₁ ⧸ w₂ ⟶ 0` -/
noncomputable def shortComplexOfLE : ShortComplex (Rep k G) where
  f := w₂.toRepInclusion h
  g := (w₂.subrepresentationOf w₁).toRepMkQ
  zero := by ext x; exact Submodule.Quotient.mk_eq_zero _ |>.mpr x.2

noncomputable def shortComplexOfLEIso :
    (w₁.shortComplexOfLE h) ≅ (w₂.subrepresentationOf w₁).shortComplex :=
  isoMk (w₂.subrepOfIsoOfLE h).symm (Iso.refl _) (Iso.refl _)

theorem shortExact_of_le : (shortComplexOfLE h).ShortExact :=
  shortExact_of_iso (shortComplexOfLEIso h).symm <| shortExact _

end Subrepresentation

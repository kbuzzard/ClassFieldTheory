module

public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
Transport of `Mono`/`Epi` of the outer maps of a short complex along an isomorphism of
short complexes.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] {S₁ S₂ : ShortComplex C}

/-- An isomorphism of short complexes transports `Mono` of the first map. -/
lemma mono_f_of_iso (e : S₁ ≅ S₂) (h : Mono S₁.f) : Mono S₂.f := by
  obtain ⟨h₁, h₂, -⟩ := (isIso_iff e.hom).1 inferInstance
  have := h
  have : Mono (inv e.hom.τ₁) := IsIso.mono_of_iso _
  have : Mono e.hom.τ₂ := IsIso.mono_of_iso _
  rw [← IsIso.inv_hom_id_assoc e.hom.τ₁ S₂.f, e.hom.comm₁₂]
  exact mono_comp _ _

/-- An isomorphism of short complexes transports `Epi` of the second map. -/
lemma epi_g_of_iso (e : S₁ ≅ S₂) (h : Epi S₁.g) : Epi S₂.g := by
  obtain ⟨-, h₂, h₃⟩ := (isIso_iff e.hom).1 inferInstance
  have := h
  have : Epi (inv e.hom.τ₂) := IsIso.epi_of_iso _
  have : Epi e.hom.τ₃ := IsIso.epi_of_iso _
  rw [← IsIso.inv_hom_id_assoc e.hom.τ₂ S₂.g, e.hom.comm₂₃]
  exact epi_comp _ _

end CategoryTheory.ShortComplex

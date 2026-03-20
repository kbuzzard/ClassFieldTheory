module

public import Mathlib.RingTheory.Unramified.Basic

public section

lemma Algebra.unramified_iff (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Unramified R A ↔ FormallyUnramified R A ∧ FiniteType R A :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

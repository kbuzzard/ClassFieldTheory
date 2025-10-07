import Mathlib

namespace RepresentationTheory

variable {k G} [CommRing k] [Group G]

noncomputable def Invariants.map {A B : Rep k G} (f : A ⟶ B) : ModuleCat.of k A.ρ.invariants ⟶
  ModuleCat.of k B.ρ.invariants := ModuleCat.ofHom <|
  (f.hom.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (Rep.hom_comm_apply f g c).symm
      simp_all [hc g]

variable (A B : Rep k G)

open groupCohomology CategoryTheory

lemma commSq1 (f : A ⟶ B): Invariants.map f ≫ (H0Iso B).inv =
    (H0Iso A).inv ≫ groupCohomology.map (MonoidHom.id G) f 0 := by
  sorry

lemma commSq' (f : A ⟶ B): (H0Iso A).hom ≫ Invariants.map f =
    groupCohomology.map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom := by
  sorry

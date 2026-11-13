module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep

universe u
variable {R G : Type u} [CommRing R] [Group G] {M : Rep R G}

namespace groupCohomology

-- TODO: upstream (mathlib's `Rep.res_id` is not tagged `@[simp]`)
attribute [simp] Rep.res_id

@[reassoc]
protected lemma map_zero {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (n : ℕ) :
    map f (0 : res f A ⟶ B) n = 0 := by
  rw [map, cochainsMap_zero, HomologicalComplex.homologyMap_zero]

variable (R G) in
/-- `H⁰(G, -)` is naturally isomorphic to the invariants functor, with components `H0Iso`. -/
def H0NatIso : functor R G 0 ≅ invariantsFunctor R G :=
  NatIso.ofComponents H0Iso fun f ↦ map_id_comp_H0Iso_hom f

@[simp] lemma H0NatIso_hom_app (M : Rep R G) : (H0NatIso R G).hom.app M = (H0Iso M).hom := rfl

@[simp] lemma H0NatIso_inv_app (M : Rep R G) : (H0NatIso R G).inv.app M = (H0Iso M).inv := rfl

end groupCohomology

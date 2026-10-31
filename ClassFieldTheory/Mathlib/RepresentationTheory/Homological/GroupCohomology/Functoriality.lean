module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep

universe u
variable {R G : Type u} [CommRing R] [Group G] {M : Rep R G}

namespace groupCohomology

@[simp]
lemma res_id : res (MonoidHom.id G) M = M := rfl

@[reassoc]
protected lemma map_zero {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (n : ℕ) :
    map f (0 : res f A ⟶ B) n = 0 := by
  dsimp [map]
  unfold groupCohomology
  -- unfolding map would unfold the type as well, and groupCohomology is a `def`
  simp

end groupCohomology

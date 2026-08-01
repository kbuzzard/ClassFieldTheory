module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep Limits

universe u
variable {R G : Type u} [CommRing R] [Group G] {M : Rep R G}

namespace groupCohomology

@[simp]
lemma res_id : res (MonoidHom.id G) M = M := rfl

protected lemma map_one {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (φ : Rep.res (1 : G →* H) A ⟶ B) (n : ℕ) [NeZero n] :
    map (1 : G →* H) φ n = 0 := by
  let ψ1 : Rep.res (1 : PUnit →* H) A ⟶ Rep.res (1 : PUnit →* H) A := 𝟙 _
  let ψ2 : Rep.res (1 : G →* PUnit) (Rep.res (1 : PUnit →* H) A) ⟶ B := Rep.ofHom
    { toLinearMap := φ.hom
      isIntertwining' := fun _ ↦ by ext; simp [← Rep.hom_comm_apply φ]}
  have h : (Rep.resFunctor 1).map ψ1 ≫ ψ2 = φ := by ext; simp [ψ1, ψ2]
  have := @map_comp k _ G PUnit H _ _ _ A (Rep.res (1 : PUnit →* H) A) B 1 1 ψ1 ψ2 n
  simp only [MonoidHom.one_comp, res_obj_ρ, h] at this
  rw [this]
  convert comp_zero
  refine CategoryTheory.Limits.IsZero.eq_zero_of_src ?_ _
  cases n; · simp_all
  exact isZero_groupCohomology_succ_of_subsingleton _ _

protected lemma map_one' {k G H : Type u} [CommRing k] [Group G] [Group H] (f : G →* H) (hf : f = 1)
    {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (n : ℕ) [NeZero n] :
    map f φ n = 0 := by
  subst hf
  exact groupCohomology.map_one φ n

@[reassoc]
protected lemma map_zero {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (n : ℕ) :
    map f (0 : res f A ⟶ B) n = 0 := by
  dsimp [map]
  unfold groupCohomology
  -- unfolding map would unfold the type as well, and groupCohomology is a `def`
  simp

end groupCohomology

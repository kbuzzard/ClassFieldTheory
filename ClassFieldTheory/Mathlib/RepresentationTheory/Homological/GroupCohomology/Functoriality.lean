module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep

universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H] {M : Rep R G} {N : Rep R H}
  {f g : G →* H} {φ : res f N ⟶ M} {ψ : res g N ⟶ M}

namespace groupCohomology

lemma map_congr (hfg : f = g) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℕ) :
    map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

lemma cochainsMap_congr (hfg : f = g) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) :
    cochainsMap f φ = cochainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simp]
lemma _root_.Representation.IntertwiningMap.coe_eq_toLinearMap {A G V W : Type*} [Semiring A]
    [Monoid G] [AddCommMonoid V] [AddCommMonoid W] [Module A V] [Module A W]
    (ρ : Representation A G V) (σ : Representation A G W) (f : ρ.IntertwiningMap σ) :
    SemilinearMapClass.semilinearMap f = f.toLinearMap := rfl

@[simp]
lemma res_id : res (MonoidHom.id G) M = M := rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
def mapIso (e : G ≃* H) (e' : M.V ≃ₗ[R] N.V) (he : ∀ g, e' ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ e') (n : ℕ) :
    groupCohomology M n ≅ groupCohomology N n where
  -- FIXME: Figure out why the `by exact` aren't necessary when importing all of mathlib
  hom := groupCohomology.map e.symm (ofHom ⟨e'.toLinearMap, fun h ↦ by
    choose g hg using e.surjective h
    simp [e.symm_apply_eq.2 hg.symm, he, hg]⟩) n
  inv := groupCohomology.map e (ofHom ⟨e'.symm.toLinearMap, fun g ↦
    e'.eq_comp_toLinearMap_iff _ _|>.1 <| by
      simp [LinearMap.comp_assoc, ← he g]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    refine map_congr (by simp) (by simp) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by simp) e'.comp_symm n

end groupCohomology

module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

@[expose] public noncomputable section

open CategoryTheory Rep

universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H] {M : Rep R G} {N : Rep R H}
  {f g : G →* H}
  {φ : M ⟶ res f N} {ψ : M ⟶ res g N}

namespace groupHomology

lemma map_congr (hfg : f = g) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℕ) :
    map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

lemma chainsMap_congr (hfg : f = g) (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) :
    chainsMap f φ = chainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simps]
def mapIso (e : G ≃* H) (e' : M.V ≃ₗ[R] N.V) (he : ∀ g, e' ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ e') (n : ℕ) :
    groupHomology M n ≅ groupHomology N n where
  hom := groupHomology.map (A := M) e (ofHom ⟨e', by simp [he]⟩) n
  inv := groupHomology.map (A := N) e.symm (ofHom ⟨e'.symm, fun h ↦
      e'.eq_comp_toLinearMap_iff _ _|>.1 <| by
    choose g hg using e.surjective h
    simp [LinearMap.comp_assoc, ← hg, ← he g]⟩) n
  hom_inv_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by simp) e'.symm_comp n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by simp) e'.comp_symm n

end groupHomology

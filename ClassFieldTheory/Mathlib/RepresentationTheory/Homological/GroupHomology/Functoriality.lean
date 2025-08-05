import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

noncomputable section

open CategoryTheory

universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H] {M : Rep R G} {N : Rep R H}
  {f g : G →* H}
  {φ : M ⟶ (Action.res (ModuleCat R) f).obj N} {ψ :  M ⟶ (Action.res (ModuleCat R) g).obj N}

namespace groupHomology

lemma map_congr (hfg : f = g) (hφψ : φ.hom = ψ.hom) (n : ℕ) : map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

lemma chainsMap_congr (hfg : f = g) (hφψ : φ.hom = ψ.hom) : chainsMap f φ = chainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simps]
def mapIso (e : G ≃* H) (e' : M.V ≅ N.V) (he : ∀ g, M.2 g ≫ e'.hom = e'.hom ≫ N.2 (e g)) (n : ℕ) :
    groupHomology M n ≅ groupHomology N n where
  hom := groupHomology.map e ⟨e'.hom, by aesop⟩ n
  inv := groupHomology.map e.symm ⟨e'.inv, by aesop (add simp [Iso.comp_inv_eq])⟩ n
  hom_inv_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by simp) (by simp) n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr (by simp) (by simp) n

end groupHomology

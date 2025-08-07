import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

open CategoryTheory

universe u
variable {R G H : Type u} [CommRing R] [Group G] [Group H] {M : Rep R G} {N : Rep R H}
  {f g : G →* H}
  {φ : (Action.res (ModuleCat R) f).obj N ⟶ M} {ψ : (Action.res (ModuleCat R) g).obj N ⟶ M}

namespace groupCohomology

lemma map_congr (hfg : f = g) (hφψ : φ.hom = ψ.hom) (n : ℕ) : map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

lemma cochainsMap_congr (hfg : f = g) (hφψ : φ.hom = ψ.hom) :
    cochainsMap f φ = cochainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simps]
def mapIso (e : G ≃* H) (e' : M.V ≅ N.V) (he : ∀ g, M.2 g ≫ e'.hom = e'.hom ≫ N.2 (e g)) (n : ℕ) :
    groupCohomology M n ≅ groupCohomology N n where
  -- FIXME: Figure out why the `by exact` aren't necessary when importing all of mathlib
  hom := groupCohomology.map e.symm ⟨by exact e'.hom, by aesop⟩ n
  inv := groupCohomology.map e ⟨by exact e'.inv, by aesop (add simp [Iso.comp_inv_eq])⟩ n
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by simp) (by simp) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr (by simp) (by simp) n

end groupCohomology

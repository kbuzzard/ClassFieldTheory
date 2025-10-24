import ClassFieldTheory.Cohomology.Functors.Restriction

/-
In this file we have a group homomorphism `φ : G →* Q` satisfying the condition

  `surj : Function.Surjective φ`.

From this, we define a functor

  `Rep.quotientToInvariantsFunctor' surj : Rep R G ⥤ Rep R Q`,

which takes a representation `M` of `G` to the subspace of vectors which are fixed by `φ.ker`,
with the obvious action of `Q`.

We use the abbreviation `M ↑ surj` for `(Rep.quotientToInvariantsFunctor' surj).obj M`.

We define the natural map of `G`-representations

  `((M ↑ surj) ↓ φ) ⟶ M`.

Using this map, we define the inflation map as a morphism of functors

  `groupCohomology.cochain_infl : quotientToInvariantsFunctor' surj ⋙ cochainsFunctor R Q ⟶ cochainsFunctor R G`.

Using this we define the inflation map on group cohomology:

  `infl (n : ℕ) : Rep.quotientToInvariantsFunctor' surj ⋙ functor R Q n ⟶ functor R G n`

Since this is defined on cochains first, we are able to deduce `δ`-naturality of the inflation map
on cohomology.
-/

open CategoryTheory
  ConcreteCategory
  Limits
  Rep
  groupCohomology
  HomologicalComplex

variable {R G : Type} [CommRing R] [Group G] --[DecidableEq G]

variable {Q : Type} [Group Q] {φ : G →* Q} (surj : Function.Surjective φ) -- [DecidableEq H]

namespace Rep
@[simps] noncomputable def quotientToInvariantsFunctor' :
    Rep R G ⥤ Rep R Q where
  obj M := M.quotientToInvariants φ.ker ↓ (QuotientGroup.quotientKerEquivOfSurjective φ surj).symm
  map f := ofHom {
    val := LinearMap.restrict (ModuleCat.Hom.hom f.hom) (by
      intro x hx g
      specialize hx g
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hx ⊢
      rw [←Rep.ρ_hom, ←LinearMap.comp_apply, ←ModuleCat.hom_comp, ←f.comm,
        ModuleCat.hom_comp, LinearMap.comp_apply, Rep.ρ_hom, hx])
    property h := by
      rename_i X Y
      ext ⟨x,hx⟩
      rw [Function.comp_apply, Function.comp_apply]
      apply Subtype.ext
      change (ModuleCat.Hom.hom f.hom  ∘ₗ X.ρ _) _ = ((Y.ρ _) ∘ₗ (ModuleCat.Hom.hom f.hom)) _
      rw [←Rep.ρ_hom, ←Rep.ρ_hom, ←ModuleCat.hom_comp, ←ModuleCat.hom_comp, f.comm]
  }
  map_id _ := rfl
  map_comp _ _ := rfl

lemma quotientToInvariantsFunctor'_obj_ρ (M : Rep R G) :
    ((quotientToInvariantsFunctor' surj).obj M).ρ =
    (M.quotientToInvariants φ.ker).ρ.comp ((QuotientGroup.quotientKerEquivOfSurjective φ surj).symm)
    := rfl

lemma quotientToInvariantsFunctor'_obj_ρ_apply (M : Rep R G) (g : G) :
    ((quotientToInvariantsFunctor' surj).obj M).ρ (φ g) =
    (M.quotientToInvariants φ.ker).ρ g
    := by
  rw [quotientToInvariantsFunctor'_obj_ρ]
  simp only [quotientToInvariantsFunctor'_obj, Action.res_obj_V, of_ρ, MonoidHom.coe_comp,
    MonoidHom.coe_coe, Function.comp_apply]
  congr
  rw [MulEquiv.symm_apply_eq]
  rfl

lemma quotientToInvariantsFunctor'_obj_ρ_apply₂ (M : Rep R G) (g : G)
    (v : (quotientToInvariantsFunctor' surj).obj M) :
    (((quotientToInvariantsFunctor' surj).obj M).ρ (φ g) v).val =
    M.ρ g v.val
    := by
  rw [quotientToInvariantsFunctor'_obj_ρ_apply]
  rfl

instance : (quotientToInvariantsFunctor' (R := R) surj).PreservesZeroMorphisms where
  map_zero _ _ := rfl

set_option quotPrecheck false in
/--
`M ↑ H` means the `H` invariants of `M`, as a representation of `G ⧸ H`.
-/
notation M " ↑ " surj => (Rep.quotientToInvariantsFunctor' surj).obj M

noncomputable def res_quotientToInvariantsFunctor'_ι (M : Rep R G) :
    ((M ↑ surj) ↓ φ) ⟶ M where
  hom := ofHom (Submodule.subtype _)
  comm g := by
    ext m
    simp only [quotientToInvariantsFunctor'_obj, Action.res_obj_V, Action.res_obj_ρ,
      RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
      RingHom.coe_coe, Function.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Submodule.coe_subtype, ρ_hom]
    rw [←Rep.quotientToInvariantsFunctor'_obj_ρ_apply₂ surj M]
    rfl

end Rep
namespace groupCohomology

noncomputable def cochain_infl :
    quotientToInvariantsFunctor' surj ⋙ cochainsFunctor R Q ⟶ cochainsFunctor R G where
  app M := cochainsMap φ <| res_quotientToInvariantsFunctor'_ι surj M
  naturality _ _ _ := rfl

/--
The inflation map `Hⁿ(G⧸H, M ↑ H) ⟶ Hⁿ(G,M)` as a natural transformation.
This is defined using the inflation map on cocycles.
-/
noncomputable def infl (n : ℕ) :
    Rep.quotientToInvariantsFunctor' surj ⋙ functor R Q n ⟶ functor R G n :=
  (groupCohomology.cochain_infl surj) ◫ 𝟙 (homologyFunctor _ _ n)



/--
Assume that we have a short exact sequence `0 → A → B → C → 0` in `Rep R G`
and that the sequence of `H`- invariants is also a short exact in `Rep R (G ⧸ H)` :

  `0 → Aᴴ → Bᴴ → Cᴴ → 0`.

Then we have a commuting square

`   Hⁿ(G ⧸ H, Cᴴ)  ⟶   H^{n+1}(G ⧸ H, Aᴴ) `
`         |                 |             `
`         ↓                 ↓             `
`     Hⁿ(G , C)    ⟶   H^{n+1}(G,A)       `

where the horizontal maps are connecting homomorphisms
and the vertical maps are inflation.
-/
lemma infl_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (hS' : (S.map (quotientToInvariantsFunctor' surj)).ShortExact)  (i j : ℕ) (hij : i + 1 = j) :
    δ hS' i j hij ≫ (infl surj j).app _ = (infl surj i).app _ ≫ δ hS i j hij
    := by
  let C := S.map (cochainsFunctor R G)
  let S' := S.map (quotientToInvariantsFunctor' surj)
  let C' := S'.map (cochainsFunctor R Q)
  let φ : C' ⟶ C := {
    τ₁ := (cochain_infl surj).app S.X₁
    τ₂ := (cochain_infl surj).app S.X₂
    τ₃ := (cochain_infl surj).app S.X₃
    comm₁₂ := ((cochain_infl surj).naturality S.f).symm
    comm₂₃ := ((cochain_infl surj).naturality S.g).symm
  }
  have ses₁ : C.ShortExact := map_cochainsFunctor_shortExact hS
  have ses₂ : C'.ShortExact := map_cochainsFunctor_shortExact hS'
  exact HomologySequence.δ_naturality φ ses₂ ses₁ i j hij

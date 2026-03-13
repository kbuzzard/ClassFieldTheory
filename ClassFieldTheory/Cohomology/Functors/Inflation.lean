import ClassFieldTheory.Cohomology.Functors.Restriction

/-!
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

  `groupCohomology.cochain_infl` of type
    `quotientToInvariantsFunctor' surj ⋙ cochainsFunctor R Q ⟶ cochainsFunctor R G`.

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

variable {R G : Type} [CommRing R] [Group G]

variable {Q : Type} [Group Q] {φ : G →* Q} (surj : Function.Surjective φ)

namespace Rep

@[simps! (isSimp := false) obj_V] noncomputable def quotientToInvariantsFunctor' :
    Rep R G ⥤ Rep R Q :=
  quotientToInvariantsFunctor R φ.ker ⋙
    (Rep.resEquiv R (QuotientGroup.quotientKerEquivOfSurjective _ surj)).inverse

/--
`M ↑ H` means the `H` invariants of `M`, as a representation of `G ⧸ H`.
-/
notation3 M " ↑ " surj => (Rep.quotientToInvariantsFunctor' surj).obj M

lemma quotientToInvariantsFunctor'_obj_ρ (M : Rep R G) :
    (M ↑ surj).ρ =
    (M.quotientToInvariants φ.ker).ρ.comp
      ((QuotientGroup.quotientKerEquivOfSurjective φ surj).symm) := rfl

@[simp] lemma QuotientGroup.quotientKerEquivOfSurjective_symm_apply
    {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : (⇑φ).Surjective) (x : G) :
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = x :=
  MulEquiv.symm_apply_eq _ |>.mpr rfl

lemma quotientToInvariantsFunctor'_obj_ρ_apply (M : Rep R G) (g : G) :
    (M ↑ surj).ρ (φ g) = (M.quotientToInvariants φ.ker).ρ g := by
  simp [quotientToInvariantsFunctor'_obj_V, quotientToInvariantsFunctor'_obj_ρ]

@[simp] lemma quotientToInvariantsFunctor'_obj_ρ_apply₂ (M : Rep R G) (g : G)
    (v : (quotientToInvariantsFunctor' surj).obj M) :
    ((M ↑ surj).ρ (φ g) v).val = M.ρ g v.val := by
  rw [quotientToInvariantsFunctor'_obj_ρ_apply]
  rfl

instance : (quotientToInvariantsFunctor' (R := R) surj).PreservesZeroMorphisms where
  map_zero _ _ := rfl

@[simps!] noncomputable def res_quotientToInvariantsFunctor'_ι (M : Rep R G) :
    ((M ↑ surj) ↓ φ) ⟶ M where
  hom := ModuleCat.ofHom (Submodule.subtype _)
  comm g := by ext; exact quotientToInvariantsFunctor'_obj_ρ_apply₂ surj ..

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
    (hS' : (S.map (quotientToInvariantsFunctor' surj)).ShortExact) (i j : ℕ) (hij : i + 1 = j) :
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

end groupCohomology

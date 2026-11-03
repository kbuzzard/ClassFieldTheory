module

public import ClassFieldTheory.Cohomology.Functors.Inflation
public import ClassFieldTheory.Cohomology.Functors.UpDown
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.Basic
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

universe u

variable {R G Q : Type u} [CommRing R] [Group G] [Group Q] {φ : G →* Q}
  (surj : Function.Surjective φ)

namespace groupCohomology

/--
Suppose we have a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(K,A) = 0` then the `K`-invariants form a short exact sequence in `Rep R Q`:

  `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`, where `K = φ.ker`.

This is the opening section of the long exact sequence of `K`-cohomology: the next term is
`H¹(K,A)`, which is assumed to be zero.
-/
lemma quotientToInvariantsFunctor'_shortExact_ofShortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (S.map (quotientToInvariantsFunctor' surj)).ShortExact := by
  have hT : (S.map (resFunctor φ.ker.subtype)).ShortExact := (shortExact_res _).2 hS
  -- the invariants complex is isomorphic to the `H⁰` complex of the restriction to `K`
  have isoInv : mapShortComplex₂ (S.map (resFunctor φ.ker.subtype)) 0 ≅
      (S.map (resFunctor φ.ker.subtype)).map (invariantsFunctor R φ.ker) :=
    ShortComplex.isoMk (H0Iso _) (H0Iso _) (H0Iso _)
      (map_id_comp_H0Iso_hom _).symm (map_id_comp_H0Iso_hom _).symm
  -- `H⁰(K,X₂) ⟶ H⁰(K,X₃)` is epi since the next term `H¹(K,X₁)` vanishes
  have hEpiH0 : Epi (mapShortComplex₂ (S.map (resFunctor φ.ker.subtype)) 0).g :=
    (mapShortComplex₃_exact hT (i := 0) rfl).epi_f (hS'.eq_zero_of_tgt _)
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective S.f).1 hS.mono_f
  -- it suffices to check short exactness after forgetting the `Q`-action
  rw [← ShortComplex.shortExact_map_iff_of_faithful _ (forget₂ (Rep R Q) (ModuleCat R))]
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_iso isoInv (mapShortComplex₂_exact hT 0)
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  · exact ShortComplex.epi_g_of_iso isoInv hEpiH0

attribute [local implicit_reducible] cochainsFunctor in
@[simps, implicit_reducible]
def inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ surj) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ φ.ker.subtype) (n + 1)
  f := (infl surj (n + 1)).app M
  g := (rest φ.ker.subtype (n + 1)).app M
  zero := by
    rw [infl, NatTrans.hcomp_id_app, HomologicalComplex.homologyFunctor_map, rest_app]
    dsimp [cochain_infl]
    rw [← map_comp, map_eq_zero]
    ext ⟨x, hx⟩
    simpa using MonoidHom.mem_ker.1 hx

instance isIso_δ_ofhM (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    IsIso (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
    (n + 1) (n + 1 + 1) rfl) := by
  have := coind₁'_quotientToInvariants_trivialCohomology (M := M) surj
  refine isIso_δ_of_isZero _ (n + 1) ?_ ?_
  <;> simp only [ShortComplex.map_X₂, upSES_X₂]
  <;> exact isZero_of_trivialCohomology

def IsoNext (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj n (up.obj M) ≅ inflationRestriction surj (n + 1) M :=
  ShortComplex.isoMk
    (@asIso _ _ _ _
      (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
        (n + 1) (n + 1 + 1) rfl)
      (isIso_δ_ofhM surj n M hM))
    (asIso (δ (shortExact_upSES M) (n + 1) (n + 1 + 1) rfl))
    (δUpResIso M φ.ker.subtype_injective (n + 1))
    (infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
      (n + 1) (n + 1 + 1) rfl)
    (rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl)

/-- The inflation–restriction complex is isomorphic to Mathlib's `HInfRes`: the two differ only
in that the first term is a cohomology group of `Q` rather than of `G ⧸ φ.ker`. -/
def isoHInfRes (n : ℕ) (M : Rep R G) :
    inflationRestriction surj n M ≅ HInfRes M φ.ker (n + 1) :=
  ShortComplex.isoMk
    (resEquiv_inv (n + 1) Q (M.quotientToInvariants φ.ker)
      (QuotientGroup.quotientKerEquivOfSurjective φ surj))
    (Iso.refl _)
    (Iso.refl _)
    (by
      change (resEquiv_inv (n + 1) Q _ _).hom ≫
          map (QuotientGroup.mk' φ.ker) (ofHom (M.ρ.quotientToInvariants_lift φ.ker)) (n + 1) =
        (infl surj (n + 1)).app M
      rw [resEquiv_inv_hom, ← map_comp, infl, NatTrans.hcomp_id_app,
        HomologicalComplex.homologyFunctor_map]
      exact map_congr (by ext g; simp [QuotientGroup.quotientKerEquivOfSurjective]) rfl (n + 1))
    (by
      change (HInfRes M φ.ker (n + 1)).g = (rest φ.ker.subtype (n + 1)).app M
      rw [HInfRes_g, rest_app])

theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    Mono (inflationRestriction surj n M).f := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following square commutes by `infl_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶  Hⁿ⁺¹(G,M)    `
  `     |                   |        `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶  Hⁿ(G,up M)   `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero => exact ShortComplex.mono_f_of_iso (isoHInfRes surj 0 M).symm
              inferInstanceAs(Mono (HInfRes M φ.ker 1).f)
  | succ n ih =>
    specialize @ih (up.obj M) <| fun i hi ↦ by
      refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
      exact hM (i + 1) (by omega)
    exact ShortComplex.mono_f_of_iso (IsoNext surj n M (hM 0 (by omega))) ih

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero => exact ShortComplex.exact_of_iso (isoHInfRes surj 0 M).symm (H1InfRes_exact M φ.ker)
  | succ n ih =>
    specialize @ih (up.obj M) <| fun i hi ↦ by
      refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
      exact hM (i + 1) (by omega)
    exact ShortComplex.exact_of_iso (IsoNext surj n M (hM 0 (by omega))) ih

end groupCohomology

end

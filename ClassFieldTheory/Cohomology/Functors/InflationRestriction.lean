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

namespace Representation

lemma quotientToInvariants_lift_apply {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (S : Subgroup G) [S.Normal]
    (x : invariants (ρ.comp S.subtype)) :
    ρ.quotientToInvariants_lift S x = (x : V) :=
  rfl

end Representation

variable {R G Q : Type u} [CommRing R] [Group G] [Group Q] {φ : G →* Q}
  (surj : Function.Surjective φ)

namespace groupCohomology

#check ShortComplex.ShortExact
#check quotientToInvariants
#check quotientToInvariants


/--
Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a SES of `G`-reps. Let `K` be a subgroup.
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact as `K`-reps
-/
lemma fact1 {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map (res φ.ker.subtype)).ShortExact :=
  hS.map_of_exact _

#check Functor

#check NatIso.ofComponents

def test : Rep R G ⥤ ModuleCat R := (res φ.ker.subtype) ⋙ (groupCohomology.functor R _ 0)

theorem commutative_diagram : ((res φ.ker.subtype) ⋙ (groupCohomology.functor R _ 0)) =
    (quotientToInvariantsFunctor' surj) ⋙ (forget₂ (Rep R _) (ModuleCat R))
    := by
  sorry

section MissingPrereqs

-- theorem Action.res_forget₂ (V G H : Type*) [Category V]  [HasForget V] [Monoid G]
--   [Monoid H] (f : G →* H) : sorry := sorry

end MissingPrereqs


-- theorem hello : (res φ.ker.subtype) ⋙ (forget₂ (Rep R _) (ModuleCat R))
--     ≅  (forget₂ (Rep R _) (ModuleCat R)) := by
--   apply NatIso.ofComponents
--   swap
--   · intro X
--     rw [Functor.comp_obj]


-- theorem attempt_1 :
--     (quotientToInvariantsFunctor' surj) ⋙ (forget₂ (Rep R _) (ModuleCat R))
--     ≅ invariantsFunctor R _ := by
--   apply NatIso.ofComponents
--   swap
--   · intro X
--     simp
--     unfold res
--     rw [quotientToInvariants, Representation.quotientToInvariants]
--     sorry


--   · intro X Y f

variable (φ) in
def thebadasscomplex (S : ShortComplex (Rep R G)) : ShortComplex (ModuleCat R) :=
  mapShortComplex₂ (S.map (res φ.ker.subtype)) 0

lemma mono_mapShortComplex₁₀_f {k} [CommRing k] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Mono (groupCohomology.mapShortComplex₂ X 0).f := by
  have : Mono X.f := hX.mono_f
  apply mono_map_0_of_mono


lemma epi_mapShortComplex₁_g {k} [CommRing k] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (i : ℕ) (hX' : IsZero <| groupCohomology X.1 (i + 1)) :
    Epi (groupCohomology.mapShortComplex₂ X i).g := by
  have : (groupCohomology.mapShortComplex₃ hX (show i + 1 = i + 1 by rfl)).f
    = (groupCohomology.mapShortComplex₂ X i).g := rfl
  rw [←this, ←ShortComplex.exact_iff_epi]
  · apply mapShortComplex₃_exact
  · apply IsZero.eq_of_tgt hX'

lemma mapShortComplex₁_shortExact₀ {k} [CommRing k] {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hX' : IsZero <| H1 X.1) :
    (groupCohomology.mapShortComplex₂ X 0).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply groupCohomology.mapShortComplex₂_exact hX 0
  · apply mono_mapShortComplex₁₀_f hX
  · apply epi_mapShortComplex₁_g hX 0 hX'


lemma fact2 {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (thebadasscomplex φ S).ShortExact := by
  apply mapShortComplex₁_shortExact₀
  · apply  hS.map_of_exact _
  · exact hS'

  -- have : (res φ.ker.subtype)
  -- If `H¹(K, A) = 0` then we have a SES of `K`-reps `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`.
  -- Fact 2: we have the usual cohomology LES. meh
  -- Fact 3: `0 ⟶ H0(K, A) ⟶ H0(K, B) ⟶ H0(K, C) ⟶ 0` : meh
  -- Fact 4: above implies `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0` : alright

/--
Consider a surjective group hom `φ : G →* Q`, with kernel `K`.
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
  ShortComplex.isoMk (resEquiv_inv (n + 1) Q (M.quotientToInvariants φ.ker)
    (QuotientGroup.quotientKerEquivOfSurjective φ surj)) (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.comp_id, HInfRes_f, inflationRestriction_f, resEquiv_inv_hom,
        ← map_comp, infl_app]
      refine map_congr ?_ ?_ _
      · ext x
        simp [← MulEquiv.eq_symm_apply]
      · ext x
        simp [res_quotientToInvariantsFunctor'_ι, quotientToInvariantsFunctor'_obj_ρ])
    (by
      rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, HInfRes_g,
        inflationRestriction_g, rest_app])

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

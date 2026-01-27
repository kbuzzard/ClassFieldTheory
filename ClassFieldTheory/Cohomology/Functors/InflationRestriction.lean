import ClassFieldTheory.Cohomology.Functors.Inflation
import ClassFieldTheory.Cohomology.Functors.UpDown
import Mathlib

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]
variable {Q : Type} [Group Q] {φ : G →* Q} (surj : Function.Surjective φ)

namespace groupCohomology

/--
Suppose we have a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(K,A) = 0` then the `K`-invariants form a short exact sequence in `Rep R Q`:

  `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`, where `K = φ.ker`.
-/
lemma quotientToInvariantsFunctor'_shortExact_ofShortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (S.map (quotientToInvariantsFunctor' surj)).ShortExact :=
  /-
  This is the opening section of the long exact sequence. The next term is `H¹(K,S.X₁)`, which
  is assumeed to be zero.
  -/
  -- (S.map (quotientToInvariantsFunctor' surj)).exact_iff_exact_map_forget₂.2 _
  -- forget this to module cat and then do
  -- .mk' ((S.map (quotientToInvariantsFunctor' surj)).moduleCat_exact_iff_range_eq_ker _) _ _
  sorry

-- example

@[simps]
def resEquiv_inv (n : ℕ) (G' : Type) [Group G'] (M : Rep R G) (e : G ≃* G') :
    groupCohomology ((Rep.resEquiv R e).inverse.obj M) n ≅ groupCohomology M n where
  hom := map e {
    hom := by exact 𝟙 M.V
    comm := by simp [Rep.res]
  } n
  inv := map e.symm {
    hom := by exact 𝟙 M.V
    comm := by simp [Rep.res]
  } n
  hom_inv_id := by
    rw [← map_comp, ← map_id]
    exact map_congr (by simp) (by simp [Rep.res_obj_V]) n
  inv_hom_id := by
    rw [← map_comp, ← map_id]
    exact map_congr (by simp) (by simp [Rep.res_obj_V]) n


-- theorem epi_δ_infl [DecidableEq G] (n : ℕ) (M : Rep R G) (hS' : IsZero (H1 (M ↓ φ.ker.subtype))) :
--     Epi (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hS')
--     (n + 1) (n + 2) rfl) := epi_δ_of_isZero _ (n + 1) (by simp [-coind₁'_obj]; sorry)

def inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ surj) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ φ.ker.subtype) (n + 1)
  f := (infl surj (n + 1)).app M
  g := (rest φ.ker.subtype (n + 1)).app M
  zero := by
    induction n generalizing M with
    | zero =>
      have : map _ _ _ ≫ map _ (𝟙 (M ↓ φ.ker.subtype)) _ = 0 :=
        (groupCohomology.H1InfRes M φ.ker).zero
      simp only [Nat.reduceAdd, infl, cochain_infl, Functor.hcomp_id, Functor.whiskerRight_app,
        Functor.comp_obj, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_map, rest_app]
      change map _ _ 1 ≫ _ = 0
      apply_fun ((resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
        (QuotientGroup.quotientKerEquivOfSurjective φ surj)).hom ≫ ·) at this
      rwa [comp_zero, resEquiv_inv_hom, ← Category.assoc, ← map_comp] at this
    | succ n ih =>
    ext x
    induction x using groupCohomology_induction_on with
    | h x =>
    simp only [infl, Functor.hcomp_id, Functor.whiskerRight_app, Functor.comp_obj,
      cochainsFunctor_obj, HomologicalComplex.homologyFunctor_map, rest, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    erw [groupCohomology.π_map_apply, groupCohomology.π_map_apply]
    nth_rw 2 [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [← cocyclesMap_comp]
    -- have := (resEquiv_inv (n + 1) Q (M.quotientToInvariants φ.ker) (QuotientGroup.quotientKerEquivOfSurjective φ surj)).hom
    -- dsimp at this
    -- conv_lhs => enter [2, 1, 1]; tactic =>
      -- convert cocyclesMap_id

    sorry
    -- have commSq1 := infl_δ_naturality surj (shortExact_upSES M)
    --   (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
    --   sorry) (n + 1) (n + 1 + 1) rfl
    -- have commSq2 := rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl
    -- rw [← @cancel_epi _ _ _ _ _ _ (epi_δ_infl surj n M sorry), ← Category.assoc]
    -- simp only [ShortComplex.map_X₃, upSES_X₃, upSES_X₁, functor_obj, ShortComplex.map_X₁,
    --   Functor.comp_obj, comp_zero] at commSq1 commSq2 ⊢
    -- rw [commSq1, Category.assoc, commSq2, ← Category.assoc, ih, zero_comp]

-- set_option pp.proofs true in
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
  induction n with
  | zero =>
  have h1 := groupCohomology.instMonoModuleCatFH1InfRes M φ.ker
  change Mono (map _ _ _) at h1
  have : Mono (resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
        (QuotientGroup.quotientKerEquivOfSurjective φ surj)).hom := IsIso.mono_of_iso _
  convert @mono_comp _ _ _ _ _ _ this _ h1 using 1
  simp only [inflationRestriction, Nat.reduceAdd, infl, cochain_infl, NatTrans.hcomp_app,
    Functor.comp_obj, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj, NatTrans.id_app,
    HomologicalComplex.homologyFunctor_map, Category.id_comp, resEquiv_inverse, resEquiv_inv_hom]
  rw [← map_comp]
  congr
  | succ n ih =>
  have commSq1 := infl_δ_naturality surj (shortExact_upSES M)
    (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
    (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl
  have commSq2 := rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl
  simp only [inflationRestriction]
  -- have : Mono (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
  --   (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl) :=
  --   groupCohomology.mono_δ_of_isZero _ _ (by
  --     dsimp [-coind₁'_obj];
  --     sorry)
  -- -- why is δ iso?
  -- simp [infl, cochain_infl]
  -- change Mono (map _ _ _)
  -- -- refine CategoryTheory.mono_comp_iff_of_mono _ _ |>.2 ?_
  sorry

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is a current PR.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  sorry


end groupCohomology

end

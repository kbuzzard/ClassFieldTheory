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

universe u

variable {R G Q : Type u} [CommRing R] [Group G] [Group Q] {φ : G →* Q} (surj : Function.Surjective φ)

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

@[simps]
def resEquiv_inv (n : ℕ) (G' : Type u) [Group G'] (M : Rep R G) (e : G ≃* G') :
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

lemma map_one {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (φ : (Action.res _ (1 : G →* H)).obj A ⟶ B) (n : ℕ) [NeZero n] :
    map (1 : G →* H) φ n = 0 := by
  let ψ1 : A ↓ (1 : PUnit →* H) ⟶ A ↓ 1 := 𝟙 _
  let ψ2 : ((A ↓ (1 : PUnit →* H)) ↓ (1 : G →* PUnit)) ⟶ B :=
    { hom := φ.hom
      comm := fun g ↦ by
        ext (x : A)
        simpa [res_obj_ρ'] using Rep.hom_comm_apply φ g x}
  have h : (Action.res _ 1).map ψ1 ≫ ψ2 = φ := by
    ext (a : A)
    simp [ψ1, ψ2]
  have := @map_comp k _ G PUnit H _ _ _ A (A ↓ 1) B 1 1 ψ1 ψ2 n
  simp [h] at this
  rw [this]
  convert comp_zero
  refine CategoryTheory.Limits.IsZero.eq_zero_of_src ?_ _
  cases n; · simp_all
  exact isZero_groupCohomology_succ_of_subsingleton _ _

lemma map_one' {k G H : Type u} [CommRing k] [Group G] [Group H] (f : G →* H) (hf : f = 1)
    {A : Rep k H} {B : Rep k G} (φ : (Action.res _ f).obj A ⟶ B) (n : ℕ) [NeZero n] :
    map f φ n = 0 := by
  subst hf
  exact map_one φ n

@[reassoc]
lemma map_zero {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (n : ℕ) :
    map f (0 : (Action.res _ f).obj A ⟶ B) n = 0 := by
  dsimp [map]
  simp

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
    dsimp [infl, rest, ← map.eq_def, cochain_infl]
    simp only [Category.id_comp]
    rw [← map_comp, map_one']
    ext ⟨x, hx⟩
    simp [MonoidHom.mem_ker.1 hx]

instance isIso_δ_ofhM (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    IsIso (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
    (n + 1) (n + 1 + 1) rfl) := by
  have := coind₁'_quotientToInvariants_trivialCohomology (M := M) surj
  refine isIso_δ_of_isZero _ (n + 1) ?_ ?_
  <;> simp only [ShortComplex.map_X₂, upSES_X₂]
  <;> exact isZero_of_trivialCohomology

abbrev mapToNext (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj n (up.obj M) ⟶ inflationRestriction surj (n + 1) M where
  τ₁ := δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
    (n + 1) (n + 1 + 1) rfl
  τ₂ := δ (shortExact_upSES M) (n + 1) (n + 1 + 1) rfl
  τ₃ := δ (shortExact_upSES_res M φ.ker.subtype) (n + 1) (n + 1 + 1) rfl
  comm₁₂ := infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
      (n + 1) (n + 1 + 1) rfl
  comm₂₃ := rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl

abbrev mapBack (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj (n + 1) M ⟶ inflationRestriction surj n (up.obj M) where
  τ₁ := have := isIso_δ_ofhM surj n M hM
    inv <| δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
    (n + 1) (n + 1 + 1) rfl
  τ₂ := inv <| δ (shortExact_upSES M) (n + 1) (n + 1 + 1) rfl
  τ₃ := (δUpResIso M φ.ker.subtype_injective (n + 1)).inv
  comm₁₂ := by
    simpa using infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
      (n + 1) (n + 1 + 1) rfl |>.symm
  comm₂₃ := by simpa [δUpResIso] using
    rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl |>.symm

abbrev IsoNext (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj n (up.obj M) ≅ inflationRestriction surj (n + 1) M where
  hom := mapToNext surj n M hM
  inv := mapBack surj n M hM
  hom_inv_id := by ext1 <;> simp [δUpResIso]
  inv_hom_id := by ext1 <;> simp [δUpResIso]

theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    Mono (inflationRestriction surj n M).f := by
  classical
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following square commutes by `infl_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶  Hⁿ⁺¹(G,M)    `
  `     |                   |        `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶  Hⁿ(G,up M)   `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
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
  simp only [inflationRestriction]
  simp only [upSES] at commSq1
  have := isIso_δ_ofhM surj n M (hM _ (by omega))
  rw [← this.eq_inv_comp] at commSq1
  simp [inflationRestriction] at ih
  rw [commSq1]
  specialize @ih (up.obj M) <| fun i hi ↦ by
    refine IsZero.of_iso _ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
    exact hM (i + 1) (by omega)
  exact mono_comp _ _

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is a current PR.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero =>
  have : (map _ _ _).hom.range = _ := ShortComplex.Exact.moduleCat_range_eq_ker <|
    H1InfRes_exact M φ.ker
  rw [← LinearEquiv.range_comp (resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
    (QuotientGroup.quotientKerEquivOfSurjective φ surj)).toLinearEquiv,
    Iso.toLinearMap_toLinearEquiv, ← ModuleCat.hom_comp] at this
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  convert this using 3
  clear * -
  simp only [inflationRestriction, Nat.reduceAdd, infl, cochain_infl, NatTrans.hcomp_app,
    Functor.comp_obj, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj, NatTrans.id_app,
    HomologicalComplex.homologyFunctor_map, Category.id_comp, resEquiv_inverse, resEquiv_inv_hom,
    ← map_comp]
  rw [map_congr]
  · ext g
    simp [QuotientGroup.quotientKerEquivOfSurjective]
  · simp only [Action.res_obj_V, Action.comp_hom, Action.res_map_hom, subtype_hom,
    res_quotientToInvariantsFunctor'_ι]
    rfl
  | succ n ih =>
  exact ShortComplex.exact_of_iso (IsoNext surj _ _ (hM 0 (by omega))) <| @ih (up.obj M) fun i hi ↦ by
    refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
    exact hM (i + 1) (by omega)

end groupCohomology

end

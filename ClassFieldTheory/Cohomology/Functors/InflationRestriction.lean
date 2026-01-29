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
    -- rw [← @cancel_epi _ _ _ _ _ _ (epi_δ_infl surj n M sorry), ← Category.assoc]
    -- simp only [ShortComplex.map_X₃, upSES_X₃, upSES_X₁, functor_obj, ShortComplex.map_X₁,
    --   Functor.comp_obj, comp_zero] at commSq1 commSq2 ⊢
    -- rw [commSq1, Category.assoc, commSq2, ← Category.assoc, ih, zero_comp]

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
  have : IsIso (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
    (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl) := by
    have := coind₁'_quotientToInvariants_trivialCohomology (M := M) surj
    refine isIso_δ_of_isZero _ (n + 1) ?_ ?_
    <;> simp only [ShortComplex.map_X₂, upSES_X₂]
    <;> exact isZero_of_trivialCohomology
  rw [← this.eq_inv_comp] at commSq1
  simp [inflationRestriction] at ih
  rw [commSq1]
  specialize @ih (up.obj M) <| fun i hi ↦ by
    refine IsZero.of_iso _ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
    exact hM (i + 1) (by omega)
  exact mono_comp _ _

example (C) [Category C] {A B : C} (f : A ⟶ B) [IsIso f] : inv f ≫ f = 𝟙 B := by exact (inv_comp_eq_id f).mpr rfl

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
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [not_lt_zero, IsEmpty.forall_iff, implies_true, inflationRestriction, Nat.reduceAdd,
    rest, LinearMap.mem_ker, H1π_comp_map_apply]
  obtain ⟨(y : M), hy⟩ := H1π_eq_zero_iff _ |>.1 hx
  have h1 := (mem_cocycles₁_iff x).1 x.2
  have h2 : ∀ s ∈ φ.ker, x s = M.ρ s y - y := fun s hs => funext_iff.1 hy.symm ⟨s, hs⟩
  let e : G ⧸ φ.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ surj
  refine ⟨H1π _ ⟨(fun g ↦ ⟨x.1 (e.symm g).out - M.ρ (e.symm g).out y + y, ?_⟩), ?_⟩, ?_⟩
  · intro s
    let g' := (e.symm g).out
    calc
      _ = x (s * g') - x s - M.ρ s (M.ρ g' y) + (x s + y) := by
        simp only [g', MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
          cocycles₁.val_eq_coe, map_add, map_sub, h1]
        abel_nf
        simp [h2]
      _ = x (g' * (g' ⁻¹ * s * g')) - M.ρ g' ((M.ρ (g' ⁻¹ * s * g') y) - y) - M.ρ g' y + y := by
        simp only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply, map_sub,
          Representation.self_inv_apply, g']
        abel
      _ = _ := by
        simp [g', eq_sub_of_add_eq' (h1 g' (g'⁻¹ * s * g')).symm,
          h2 (g'⁻¹ * s * g') (Subgroup.Normal.conj_mem' _ _ s.2 _)]
  · rw [mem_cocycles₁_iff]
    intro g' h'
    sorry
  · sorry
  | succ n ih =>
  have commSq1 := infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
      (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl
  have commSq2 := rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  simp only [inflationRestriction, rest, LinearMap.mem_ker, res] at hx x
  simp [inflationRestriction]
  let x' := (δUpIso M n).inv.hom x
  have eq := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker <| @ih (up.obj M) fun i hi ↦ by
    refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
    exact hM (i + 1) (by omega)
  simp only [inflationRestriction, rest] at eq
  have hx' : x' ∈ (map φ.ker.subtype (𝟙 (up.obj M ↓ φ.ker.subtype)) (n + 1)).hom.ker := by
    have := congr(($commSq2).hom x')
    simp only at this
    simp only [LinearMap.mem_ker]
    conv_lhs at this => enter [2]; tactic => unfold x'
    simp only [upSES, rest] at this
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Category.assoc, δUpIso, asIso_inv,
      (inv_comp_eq_id _).2 rfl, Category.id_comp] at this
    erw [hx] at this
    change 0 = (_ ≫ (δUpResIso M φ.ker.subtype_injective (n + 1)).hom).hom x' at this
    rw [ModuleCat.hom_comp] at this
    change 0 = ((δUpResIso _ _ _).toLinearEquiv.toLinearMap ∘ₗ _) x' at this
    rwa [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, eq_comm,
      LinearEquiv.map_eq_zero_iff] at this
  rw [← eq] at hx'
  obtain ⟨y, hy⟩ := hx'
  have : IsIso (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
    (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl) := by
    have := coind₁'_quotientToInvariants_trivialCohomology (M := M) surj
    refine isIso_δ_of_isZero _ (n + 1) ?_ ?_
    <;> simp only [ShortComplex.map_X₂, upSES_X₂]
    <;> exact isZero_of_trivialCohomology
  use (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M)
    (hM 0 (by omega))) (n + 1) (n + 1 + 1) rfl).hom y
  have := congr(($commSq1).hom y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, upSES] at this
  erw [this, hy] --`erw?` gives nothing
  unfold x'
  erw [← LinearMap.comp_apply]
  rw [← ModuleCat.hom_comp, δUpIso, asIso_inv, (inv_comp_eq_id _).2 rfl, ModuleCat.hom_id,
    LinearMap.id_apply]

end groupCohomology

end

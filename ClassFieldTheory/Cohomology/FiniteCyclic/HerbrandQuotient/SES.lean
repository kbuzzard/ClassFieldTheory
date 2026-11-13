module

public import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Herbrand quotient of short exact sequences of representations

This file shows that the Herbrand quotient is multiplicative, in the sense that if
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` is a short exact sequence of representations, then the Herbrand quotient
of `B` is the product of the Herbrand quotients of `A` and `C`.
-/

@[expose] public noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Finite G] [IsCyclic G]

open CategoryTheory
  groupCohomology
  Rep
  LinearMap
  IsCyclic

namespace Rep
variable {S : ShortComplex (Rep R G)} (hS : S.ShortExact)

include hS

-- TODO : upstream this into mathlib
omit [IsCyclic G] [Finite G] hS in
lemma _root_.Rep.res_id_map (X Y : Rep R G) (f : X ⟶ Y) :
    (resFunctor (MonoidHom.id G)).map f = f := rfl

/-- Given a short exact sequence of representations of a finite cyclic group, the long exact
sequence in cohomology is periodic with period six. -/
def herbrandSixTermSequence : CochainComplex (ModuleCat R) (Fin 6) where
  X
  | 0 => H2 S.X₁
  | 1 => H2 S.X₂
  | 2 => H2 S.X₃
  | 3 => H1 S.X₁
  | 4 => H1 S.X₂
  | 5 => H1 S.X₃
  d
  | 0, 1 => (functor R G 2).map S.f
  | 1, 2 => (functor R G 2).map S.g
  | 2, 3 => δ hS 2 3 rfl ≫ (periodicCohomology 3 1 <| by decide).hom.app S.X₁
  | 3, 4 => (functor R G 1).map S.f
  | 4, 5 => (functor R G 1).map S.g
  | 5, 0 => δ hS 1 2 rfl
  | _, _ => 0
  shape i j _ := by fin_cases i, j <;> tauto
  d_comp_d' i _ _ hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    subst hij hjk
    fin_cases i <;>
        dsimp only [Fin.reduceFinMk, Fin.reduceAdd]
    · simp [-functor_map, ← Functor.map_comp, S.zero]
    · simpa [-functor_map, ← Category.assoc, ← ShortComplex.map_g] using!
        (mapShortComplex₃ hS (Eq.refl 3)).zero
    · simp only [Fin.isValue, Category.assoc, ← NatTrans.naturality, functor_obj]
      rw [← S.map_f]
      simp
    · simp [-functor_map, ← Functor.map_comp]
    · rw [← ShortComplex.map_g]
      simp
    · rw [← ShortComplex.map_f]
      simp

/-! The short complexes `(herbrandSixTermSequence hS).sc' (j - 1) j (j + 1)`, unfolded. -/

lemma herbrandSixTermSequence_sc'_5_0_1 :
    (herbrandSixTermSequence hS).sc' 5 0 1 =
      ShortComplex.mk (δ hS 1 2 rfl) ((functor R G 2).map S.f) (δ_comp_map hS 1 2 rfl) := rfl

lemma herbrandSixTermSequence_sc'_0_1_2 :
    (herbrandSixTermSequence hS).sc' 0 1 2 = S.map (functor R G 2) := rfl

lemma herbrandSixTermSequence_sc'_1_2_3 :
    (herbrandSixTermSequence hS).sc' 1 2 3 =
      ShortComplex.mk ((functor R G 2).map S.g)
        (δ hS 2 3 rfl ≫ (periodicCohomology 3 1 (by decide)).hom.app S.X₁) (by simp) := rfl

lemma herbrandSixTermSequence_sc'_2_3_4 :
    (herbrandSixTermSequence hS).sc' 2 3 4 =
      ShortComplex.mk (δ hS 2 3 rfl ≫ (periodicCohomology 3 1 (by decide)).hom.app S.X₁)
        ((functor R G 1).map S.f) (by rw [Category.assoc, ← NatTrans.naturality]; simp) := rfl

lemma herbrandSixTermSequence_sc'_3_4_5 :
    (herbrandSixTermSequence hS).sc' 3 4 5 = S.map (functor R G 1) := rfl

lemma herbrandSixTermSequence_sc'_4_5_0 :
    (herbrandSixTermSequence hS).sc' 4 5 0 =
      ShortComplex.mk ((functor R G 1).map S.g) (δ hS 1 2 rfl) (map_comp_δ hS 1 2 rfl) := rfl

/-- The short complex `H²(G, X₂) ⟶ H²(G, X₃) ⟶ H¹(G, X₁)` obtained from `mapShortComplex₃` by
composing the connecting homomorphism with the periodicity isomorphism is exact. -/
lemma exact_map_δ_periodicCohomology :
    (ShortComplex.mk ((functor R G 2).map S.g)
      (δ hS 2 3 rfl ≫ (periodicCohomology 3 1 (by decide)).hom.app S.X₁) (by simp)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_map_δ hS 2 3 rfl)
  exact ShortComplex.isoMk (.refl _) (.refl _) ((periodicCohomology 3 1 (by decide)).app S.X₁)

/-- The short complex `H²(G, X₃) ⟶ H¹(G, X₁) ⟶ H¹(G, X₂)` obtained from `mapShortComplex₁` by
composing the connecting homomorphism with the periodicity isomorphism is exact. -/
lemma exact_δ_periodicCohomology_map :
    (ShortComplex.mk (δ hS 2 3 rfl ≫ (periodicCohomology 3 1 (by decide)).hom.app S.X₁)
      ((functor R G 1).map S.f) (by rw [Category.assoc, ← NatTrans.naturality]; simp)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_δ_map hS 2 3 rfl)
  exact ShortComplex.isoMk (.refl _) ((periodicCohomology 3 1 (by decide)).app S.X₁)
    ((periodicCohomology 3 1 (by decide)).app S.X₂)
    (comm₂₃ := by rw [Iso.app_hom, Iso.app_hom, NatTrans.naturality])

lemma herbrandSixTermSequence_exactAt (i : Fin 6) : (herbrandSixTermSequence hS).ExactAt i := by
  fin_cases i <;>
    refine (HomologicalComplex.exactAt_iff' _ _ _ _ (CochainComplex.prev _ _)
      (CochainComplex.next _ _)).mpr ?_ <;>
    dsimp only [Fin.reduceFinMk, Fin.reduceSub, Fin.reduceAdd]
  · rw [herbrandSixTermSequence_sc'_5_0_1]
    exact exact_δ_map hS 1 2 rfl
  · rw [herbrandSixTermSequence_sc'_0_1_2]
    exact mapShortComplex₂_exact hS 2
  · rw [herbrandSixTermSequence_sc'_1_2_3]
    exact exact_map_δ_periodicCohomology hS
  · rw [herbrandSixTermSequence_sc'_2_3_4]
    exact exact_δ_periodicCohomology_map hS
  · rw [herbrandSixTermSequence_sc'_3_4_5]
    exact mapShortComplex₂_exact hS 1
  · rw [herbrandSixTermSequence_sc'_4_5_0]
    exact exact_map_δ hS 1 2 rfl

lemma herbrandQuotient_ne_zero_of_shortExact₃
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0) :
    S.X₃.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 2).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 5).X₃ := by simpa using! h₁
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 5).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 2).X₁ := by simpa using! h₂
  exact ⟨(herbrandSixTermSequence_exactAt hS 5).moduleCat_finite,
    (herbrandSixTermSequence_exactAt hS 2).moduleCat_finite⟩

lemma herbrandQuotient_ne_zero_of_shortExact₂
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 4).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 1).X₁ := by simpa using! h₁
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 4).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 1).X₃ := by simpa using! h₃
  exact ⟨(herbrandSixTermSequence_exactAt hS 4).moduleCat_finite,
    (herbrandSixTermSequence_exactAt hS 1).moduleCat_finite⟩

lemma herbrandQuotient_ne_zero_of_shortExact₁
    (h₂ : S.X₂.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₁.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 3).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 0).X₃ := by simpa using! h₂
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 0).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 3).X₁ := by simpa using! h₃
  exact ⟨(herbrandSixTermSequence_exactAt hS 3).moduleCat_finite,
    (herbrandSixTermSequence_exactAt hS 0).moduleCat_finite⟩

lemma herbrandQuotient_eq_of_shortExact
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0)
    (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient = S.X₁.herbrandQuotient * S.X₃.herbrandQuotient := by
  /-
  We have a six term long exact sequence of finite `R`-modules.
  Hence the products of the orders of the even terms is
  equal to the product of the orders of the odd terms.
  This implies the relation.
  -/
  unfold herbrandQuotient at h₁ h₂ h₃ ⊢
  rw [ne_eq, div_eq_zero_iff, Rat.natCast_eq_zero_iff, not_or] at h₁ h₂ h₃
  cases h₁; cases h₂; cases h₃
  field_simp
  suffices h :
      Nat.card ((herbrandSixTermSequence hS).X 0) *
      Nat.card ((herbrandSixTermSequence hS).X 2) *
      Nat.card ((herbrandSixTermSequence hS).X 4) =
      Nat.card ((herbrandSixTermSequence hS).X 1) *
      Nat.card ((herbrandSixTermSequence hS).X 3) *
      Nat.card ((herbrandSixTermSequence hS).X 5) by
    simp only [herbrandSixTermSequence] at h
    symm
    norm_cast at h ⊢
    ac_nf at h ⊢
  have us (i j : Fin 6) :=
    Nat.card_congr (quotKerEquivRange ((herbrandSixTermSequence hS).d i j).hom).toEquiv ▸
    Submodule.card_eq_card_quotient_mul_card
      (LinearMap.ker ((herbrandSixTermSequence hS).d i j).hom)
  have ui (i j k : Fin 6) (hij : i + 1 = j := by decide) (hjk : j + 1 = k := by decide) :
      range ((herbrandSixTermSequence hS).d i j).hom =
      ker ((herbrandSixTermSequence hS).d j k).hom :=
    ((HomologicalComplex.exactAt_iff' _ i j k (by simp [← hij]) (by simp [hjk])).mp
      (herbrandSixTermSequence_exactAt hS j)).moduleCat_range_eq_ker
  rw [us 0 1, us 1 2, us 2 3, us 3 4, us 4 5, us 5 0, ui 5 0 1, ui 0 1 2, ui 1 2 3, ui 2 3 4,
    ui 3 4 5, ui 4 5 0]
  ac_rfl

end Rep

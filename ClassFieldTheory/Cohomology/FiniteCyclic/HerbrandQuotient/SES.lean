import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs
import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Herbrand quotient of short exact sequences of representations

This file shows that the Herbrand quotient is multiplicative, in the sense that if
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` is a short exact sequence of representations, then the Herbrand quotient
of `B` is the product of the Herbrand quotients of `A` and `C`.
-/

noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Fintype G] [IsCyclic G]

open CategoryTheory
  groupCohomology
  Rep
  LinearMap
  IsCyclic

namespace Rep
variable {S : ShortComplex (Rep R G)} (hS : S.ShortExact)

include hS

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
    · rw [← Functor.map_comp, S.zero, Functor.map_zero]
    · rw [← Category.assoc, ← ShortComplex.map_g]
      erw [(mapShortComplex₃ hS (Eq.refl 3)).zero]
      rw [Limits.zero_comp]
    · rw [Category.assoc, ← NatTrans.naturality, ← ShortComplex.map_f]
      erw [(mapShortComplex₁ hS (Eq.refl 3)).zero_assoc]
      rw [Limits.zero_comp]
    · rw [← Functor.map_comp, S.zero, Functor.map_zero]
    · rw [← ShortComplex.map_g]
      erw [(mapShortComplex₃ hS (Eq.refl 2)).zero]
    · rw [← ShortComplex.map_f]
      erw [(mapShortComplex₁ hS (Eq.refl 2)).zero]

lemma herbrandSixTermSequence_exactAt (i : Fin 6) : (herbrandSixTermSequence hS).ExactAt i := by
  fin_cases i <;>
      change ShortComplex.Exact (ShortComplex.mk ..) <;>
      rw [CochainComplex.prev, CochainComplex.next]
  · exact mapShortComplex₁_exact hS (Eq.refl 2)
  · exact mapShortComplex₂_exact hS 2
  · refine ShortComplex.exact_of_iso ?_ (mapShortComplex₃_exact hS (Eq.refl 3))
    exact ShortComplex.isoMk (.refl _) (.refl _) ((periodicCohomology 3 1 <| by decide).app S.X₁)
  · refine ShortComplex.exact_of_iso ?_ (mapShortComplex₁_exact hS (Eq.refl 3))
    refine ShortComplex.isoMk (.refl _)
      ((periodicCohomology 3 1 <| by decide).app S.X₁)
      ((periodicCohomology 3 1 <| by decide).app S.X₂) ?_ ?_
    · cat_disch
    · dsimp only [herbrandSixTermSequence, Fin.reduceFinMk, Fin.reduceAdd]
      rw [Iso.app_hom, ← NatTrans.naturality]
      cat_disch
  · exact mapShortComplex₂_exact hS 1
  · exact mapShortComplex₃_exact hS (Eq.refl 2)

lemma herbrandQuotient_ne_zero_of_shortExact₃
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0) :
    S.X₃.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 2).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 5).X₃ := by simpa using h₁
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 5).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 2).X₁ := by simpa using h₂
  exact ⟨(herbrandSixTermSequence_exactAt hS 5).finite_moduleCat,
    (herbrandSixTermSequence_exactAt hS 2).finite_moduleCat⟩

lemma herbrandQuotient_ne_zero_of_shortExact₂
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 4).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 1).X₁ := by simpa using h₁
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 4).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 1).X₃ := by simpa using h₃
  exact ⟨(herbrandSixTermSequence_exactAt hS 4).finite_moduleCat,
    (herbrandSixTermSequence_exactAt hS 1).finite_moduleCat⟩

lemma herbrandQuotient_ne_zero_of_shortExact₁
    (h₂ : S.X₂.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₁.herbrandQuotient ≠ 0 := by
  rw [herbrandQuotient_ne_zero] at *
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 3).X₃ ∧
      Finite ((herbrandSixTermSequence hS).sc 0).X₃ := by simpa using h₂
  obtain ⟨_, _⟩ :
      Finite ((herbrandSixTermSequence hS).sc 0).X₁ ∧
      Finite ((herbrandSixTermSequence hS).sc 3).X₁ := by simpa using h₃
  exact ⟨(herbrandSixTermSequence_exactAt hS 3).finite_moduleCat,
    (herbrandSixTermSequence_exactAt hS 0).finite_moduleCat⟩

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
  have us (i : Fin 6) :=
    Nat.card_congr (quotKerEquivRange ((herbrandSixTermSequence hS).d i (i + 1)).hom).toEquiv ▸
    Submodule.card_eq_card_quotient_mul_card
      (LinearMap.ker ((herbrandSixTermSequence hS).d i (i + 1)).hom)
  have ui (i : Fin 6) :
      range ((herbrandSixTermSequence hS).d (i - 1) i).hom =
      ker ((herbrandSixTermSequence hS).d i (i + 1)).hom :=
    CochainComplex.prev (Fin 6) i ▸ CochainComplex.next (Fin 6) i ▸
      (herbrandSixTermSequence_exactAt hS i).moduleCat_range_eq_ker
  rw [us 0, us 1, us 2, us 3, us 4, us 5]
  erw [ui 0, ui 1, ui 2, ui 3, ui 4, ui 5]
  dsimp only [Fin.reduceAdd]
  ac_rfl

end Rep

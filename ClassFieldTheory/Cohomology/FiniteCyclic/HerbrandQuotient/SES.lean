import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs

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

def herbrandSixTermSequence : CochainComplex (ModuleCat R) (Fin 6) where
  X
  | 0 => groupCohomology S.X₁ 2
  | 1 => groupCohomology S.X₂ 2
  | 2 => groupCohomology S.X₃ 2
  | 3 => groupCohomology S.X₁ 1
  | 4 => groupCohomology S.X₂ 1
  | 5 => groupCohomology S.X₃ 1
  d
  | 0,1 => (functor R G 2).map S.f
  | 1,2 => (functor R G 2).map S.g
  | 2,3 => δ hS 2 3 rfl ≫ (periodicCohomology 0).inv.app S.X₁
  | 3,4 => (functor R G 1).map S.f
  | 4,5 => (functor R G 1).map S.g
  | 5,0 => δ hS 1 2 rfl
  | _,_ => 0
  shape i j _ := by fin_cases i,j <;> tauto
  d_comp_d' i _ _ hij hjk := by
    simp only [ComplexShape.up_Rel, Fin.isValue] at hij hjk
    rw [← hjk, ← hij]
    sorry

lemma herbrandSixTermSequence_exactAt (i : Fin 6) : (herbrandSixTermSequence hS).ExactAt i :=
  /-
  It should be possible to get this out of Mathlib.
  -/
  sorry

lemma herbrandQuotient_nonzero_of_shortExact₃
  (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0) :
  S.X₃.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_nonzero_of_shortExact₂
  (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₂.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_nonzero_of_shortExact₁
  (h₁ : S.X₂.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₁.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_eq_of_shortExact
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0)
    (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient = S.X₁.herbrandQuotient * S.X₃.herbrandQuotient :=
  /-
  We have a six term long exact sequence of finite `R`-modules.
  Hence the products of the orders of the even terms is
  equal to the product of the orders of the odd terms.
  This implies the relation.
  -/
  sorry

end Rep

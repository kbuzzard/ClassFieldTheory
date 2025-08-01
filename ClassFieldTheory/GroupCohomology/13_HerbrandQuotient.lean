import Mathlib
import ClassFieldTheory.GroupCohomology.«09_CyclicGroup»
import ClassFieldTheory.GroupCohomology.«04_TateCohomology_def»

noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Finite G] [DecidableEq G] [IsCyclic G]
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

open CategoryTheory
  groupCohomology
  Rep
  LinearMap
  IsCyclic

namespace Representation

abbrev oneSubGen : A →ₗ[R] A := 1 - ρ (gen G)
abbrev herbrandZ0 := ker ρ.oneSubGen
abbrev herbrandZ1 := ker ρ.norm
abbrev herbrandB0 := range ρ.norm
abbrev herbrandB1 := range ρ.oneSubGen

lemma herbrandB0_le_herbrandZ0 : ρ.herbrandB0 ≤ ρ.herbrandZ0 := sorry

lemma herbrandB1_le_herbrandZ1 : ρ.herbrandB1 ≤ ρ.herbrandZ1 := sorry

abbrev herbrandH0 := ρ.herbrandZ0 ⧸ (ρ.herbrandB0.submoduleOf ρ.herbrandZ0)

abbrev herbrandH1 := ρ.herbrandZ1 ⧸ (ρ.herbrandB1.submoduleOf ρ.herbrandZ1)

def herbrandQuotient : ℚ := Nat.card ρ.herbrandH0 / Nat.card ρ.herbrandH1

lemma herbrandQuotient_of_finite [Finite A] : ρ.herbrandQuotient = 1 := sorry
  /-
  Consider the linear maps `f₁ f₂ : M → M` defined to be multiplication by `1 - gen G`
  and norm respectively. The kernel of `f₁` is the submodule of `G`-invariants, and the
  cokernel of `f₁` is the quotient module of coinvariants. We therefore have (for Tate groups):

    `H⁰(G,M) ≅ ker f₁ ⧸ range f₂` and `H⁻¹(G,M) ≅ ker f₂ ⧸ range f₁`.

  The result follows because `|ker fᵢ| * |range fᵢ| = |M|` for `i=1,2`.
  -/

end Representation

namespace Rep

def herbrandQuotient (M : Rep R G) : ℚ :=
    Nat.card (groupCohomology M 2) / Nat.card (groupCohomology M 1)

lemma herbrandQuotient_of : herbrandQuotient (of ρ) = ρ.herbrandQuotient :=
  /-
  show that `herbrandH0` and `herbrandH1` are isomorphic to the Tate cohomology groups
  `H⁰` and `H¹`. Then use the periodicity of the Tate cohomology groups.
  -/
  sorry

lemma herbrandQuotient_of_finite (M : Rep R G) [Finite M] : M.herbrandQuotient = 1 :=
  /-
  This is proved above for `Representation`.
  -/
  sorry

section six_term_sequence
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
    rw [←hjk,←hij]
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

end six_term_sequence

end Rep

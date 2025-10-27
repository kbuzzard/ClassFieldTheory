import ClassFieldTheory.Cohomology.FiniteCyclic.ExplicitTate

/-!
# Herbrand quotients

In this file, we define the Herbrand quotient of a representation of a finite cyclic group, which is
the size of its zeroth Tate cohomology group over the size of its first, both categorically
(that is, in the `Rep` category) and concretely (via `Representation`).

## Main declarations

* `Representation.herbrandQuotient`: Herbrand quotient of a representation, defined concretely.
* `Rep.herbrandQuotient`: Herbrand quotient of a representation, defined categorically.
-/

noncomputable section

variable {R G A : Type} [CommRing R] [Group G] [Fintype G] [IsCyclic G]
variable [AddCommGroup A] [Module R A] (ρ : Representation R G A)

open CategoryTheory
  groupCohomology
  Rep
  LinearMap
  IsCyclic

namespace Representation

/-- The Herbrand quotient of a representation is the size of its zeroth Tate group over
the size of its -1-st.

This version works for non-categorical representations. See `Rep.herbrandQuotient` for the
categorical one. -/
def herbrandQuotient : ℚ := Nat.card ρ.TateH0 / Nat.card ρ.TateHNeg1

end Representation

namespace Rep

/-- The Herbrand quotient of a representation is the size of its second cohomology group over
the size of its first.

This version works for non-categorical representations. See `Representation.herbrandQuotient` for
the categorical one. -/
def herbrandQuotient (M : Rep R G) : ℚ := Nat.card (H2 M) / Nat.card (H1 M)

@[simp] lemma herbrandQuotient_of : herbrandQuotient (of ρ) = ρ.herbrandQuotient := by
  rw [herbrandQuotient, Representation.herbrandQuotient,
    Nat.card_congr ρ.tateH0LinearEquivH2.toEquiv, Nat.card_congr ρ.tateHNeg1LinearEquivH1.toEquiv]

@[simp] lemma herbrandQuotient_ρ (M : Rep R G) : M.ρ.herbrandQuotient = M.herbrandQuotient := by
  simp [← herbrandQuotient_of]

omit [Fintype G] [IsCyclic G] in
@[simp] lemma herbrandQuotient_eq_zero {M : Rep R G} :
    M.herbrandQuotient = 0 ↔ Infinite (H1 M) ∨ Infinite (H2 M) := by
  simp [herbrandQuotient, Nat.card_eq_zero, or_comm]

omit [Fintype G] [IsCyclic G] in
lemma herbrandQuotient_ne_zero {M : Rep R G} :
    M.herbrandQuotient ≠ 0 ↔ Finite (H1 M) ∧ Finite (H2 M) := by simp

end Rep

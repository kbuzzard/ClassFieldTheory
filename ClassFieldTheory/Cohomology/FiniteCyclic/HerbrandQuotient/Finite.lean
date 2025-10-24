import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs
import ClassFieldTheory.Mathlib.LinearAlgebra.Isomorphisms
import ClassFieldTheory.Mathlib.LinearAlgebra.Quotient.Card

/-!
# Herbrand quotient of a finite representation

In this file, we show the Herbrand quotient of a trivial representation is `1`.
-/

variable {R G A : Type} [CommRing R] [Group G] [Fintype G] [IsCyclic G]
  [AddCommGroup A] [Module R A] (ρ : Representation R G A)

namespace Representation

lemma herbrandQuotient_of_finite [Finite A] : ρ.herbrandQuotient = 1 := by
  /-
  Consider the linear maps `oneSubGen` and `norm : M → M` defined to be multiplication by `1 - gen G`
  and norm respectively. The kernel of `oneSubGen` is the submodule of `G`-invariants, and the
  cokernel of `oneSubGen` is the quotient module of coinvariants. We therefore have (for Tate
  groups):

    `H⁰(G, M) ≅ ker oneSubGen ⧸ range norm` and `H⁻¹(G, M) ≅ ker norm ⧸ range oneSubGen`.

  The result follows because `|ker f| * |range f| = |M|` for any function `f : M → M`.
  -/
  simp only [herbrandQuotient, Submodule.natCard_quotient, tateB0_le_tateZ0,
    Submodule.natCard_submoduleOf, tateBNeg1_le_tateZNeg1, div_div_div_eq]
  norm_cast
  rw [mul_comm]
  simp [tateZ0, tateZNeg1, tateB0, tateBNeg1, -LinearMap.mem_range, -LinearMap.mem_ker]

end Representation

namespace Rep

lemma herbrandQuotient_of_finite (M : Rep R G) [Finite M] : M.herbrandQuotient = 1 := by
  simpa using M.ρ.herbrandQuotient_of_finite

end Rep

import ClassFieldTheory.Cohomology.FiniteCyclic.UpDown
import ClassFieldTheory.Cohomology.TateCohomology

noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
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

end Rep

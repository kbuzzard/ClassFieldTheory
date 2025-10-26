import Mathlib.Algebra.GroupWithZero.WithZero

namespace WithZero

@[elab_as_elim, induction_eliminator, cases_eliminator]
def expRecOn {M : Type*} {motive : Mᵐ⁰ → Sort*} (x : Mᵐ⁰)
    (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) : motive x :=
  Option.recOn x zero exp

@[simp] lemma expRecOn_zero {M : Type*} {motive : Mᵐ⁰ → Sort*}
    (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) :
    @WithZero.expRecOn M motive 0 zero exp = zero := rfl

@[simp] lemma expRecOn_exp {M : Type*} {motive : Mᵐ⁰ → Sort*}
    (x : M) (zero : motive 0) (exp : ∀ a : M, motive (.exp a)) :
    @WithZero.expRecOn M motive (.exp x) zero exp = exp x := rfl

theorem exp_surj' {M : Type*} {y : Mᵐ⁰} (hy : y ≠ 0) :
    ∃ x, exp x = y := by
  cases y <;> tauto

theorem exp_zero' {M : Type*} [Zero M] : exp (0 : M) = 1 := rfl

end WithZero

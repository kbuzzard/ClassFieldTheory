import Mathlib.Algebra.Module.Submodule.Range

/-!
# TODO

Rename `LinearMap.range_coe` to `LinearMap.range_coe`.
-/

namespace Submodule
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p q : Submodule R M}

@[simp] lemma submoduleOf_eq_top : p.submoduleOf q = ⊤ ↔ q ≤ p := by simp [submoduleOf]

end Submodule

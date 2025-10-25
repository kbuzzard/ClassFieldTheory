import Mathlib.RepresentationTheory.Basic

namespace Representation
variable {G : Type*} [Group G] [Fintype G]

variable (G) in
@[simp] lemma norm_trivial_int_eq_card : (trivial ℤ G ℤ).norm = Nat.card G := by
  ext; simp [Representation.norm]

end Representation

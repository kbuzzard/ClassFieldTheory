import Mathlib.Algebra.Order.Hom.Monoid

namespace OrderMonoidIso

variable {α β : Type*} [Preorder α] [Preorder β] [Mul α] [Mul β] (e : α ≃*o β)

nonrec theorem surjective : (⇑e).Surjective :=
  e.surjective

@[simp] theorem le_symm_apply {x y} : x ≤ e.symm y ↔ e x ≤ y :=
  e.toOrderIso.le_symm_apply

@[simp] theorem symm_apply_le {x y} : e.symm x ≤ y ↔ x ≤ e y :=
  e.toOrderIso.symm_apply_le

@[simp] theorem lt_symm_apply {x y} : x < e.symm y ↔ e x < y :=
  e.toOrderIso.lt_symm_apply

@[simp] theorem symm_apply_lt {x y} : e.symm x < y ↔ x < e y :=
  e.toOrderIso.symm_apply_lt

end OrderMonoidIso

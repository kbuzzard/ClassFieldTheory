import Mathlib.GroupTheory.GroupAction.Quotient

theorem QuotientGroup.mk_mul' {G : Type} [Group G] {S : Subgroup G} (g x : G) :
  QuotientGroup.mk (s := S) (g * x) = g • QuotientGroup.mk x := rfl

import Mathlib.RingTheory.Valuation.Basic

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]

section defs

variable (v : Valuation R Γ) (γ : Γ)

/-- The "valuation ball" is a valuation version of the open balls centered at 0 in a metric
topology. This is used in `ValuativeTopology` for the statement that a valuative relation is
compatible with a given topology -/
def ball : Set R :=
  { x | v x < γ }

/-- The valuative version of `Metric.closedBall`. -/
def closedBall (v : Valuation R Γ) (γ : Γ) : Set R :=
  { x | v x ≤ γ }

/-- The valuative version of `Metric.sphere`. -/
def sphere (v : Valuation R Γ) (γ : Γ) : Set R :=
  { x | v x = γ }

end defs


section simp_lemmas

variable {v : Valuation R Γ} {x : R} {γ : Γ}

@[simp] lemma mem_ball_iff :
    x ∈ v.ball γ ↔ v x < γ :=
  Iff.rfl

@[simp] lemma mem_closedBall_iff :
    x ∈ v.closedBall γ ↔ v x ≤ γ :=
  Iff.rfl

@[simp] lemma mem_sphere_iff :
    x ∈ v.sphere γ ↔ v x = γ :=
  Iff.rfl

end simp_lemmas


namespace IsEquiv

variable {Γ' : Type*} [LinearOrderedCommMonoidWithZero Γ']
  {v : Valuation R Γ} {v' : Valuation R Γ'} (h : IsEquiv v v') {x y : R}
include h

theorem le_iff_le : v x ≤ v y ↔ v' x ≤ v' y :=
  h x y

-- #check lt_iff_lt
-- #check val_eq -- change to eq_iff_eq

-- #check le_one_iff_le_one
-- #check lt_one_iff_lt_one
-- #check eq_one_iff_eq_one

theorem one_le_iff_one_le : 1 ≤ v y ↔ 1 ≤ v' y := by
  simpa only [map_one] using h 1 y

theorem one_lt_iff_one_lt : 1 < v y ↔ 1 < v' y := by
  simpa only [map_one] using h.lt_iff_lt (x := 1)

variable (x)

theorem ball_eq_ball : v.ball (v x) = v'.ball (v' x) := by
  ext y; simp_rw [mem_ball_iff, h.lt_iff_lt]

theorem closedBall_eq_closedBall : v.closedBall (v x) = v'.closedBall (v' x) := by
  ext y; simp_rw [mem_closedBall_iff, h.le_iff_le]

theorem sphere_eq_sphere : v.sphere (v x) = v'.sphere (v' x) := by
  ext y; simp_rw [mem_sphere_iff, h.val_eq]

end IsEquiv

end Valuation

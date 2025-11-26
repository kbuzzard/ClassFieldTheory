import Mathlib.RingTheory.Valuation.Basic

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]

section defs

variable (v : Valuation R Γ) (γ : Γ)

/-- The "valuation ball" is a valuation version of the open balls centered at 0 in a metric
topology. This is used in `IsValuativeTopology` for the statement that a valuative relation is
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

theorem ext_lt_one {F Γ₀ : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] {v₁ v₂ : Valuation F Γ₀} (equiv : v₁.IsEquiv v₂)
    (h : ∀ ⦃x⦄, v₁ x < 1 → v₁ x = v₂ x) : v₁ = v₂ := by
  ext x
  obtain hx1 | hx1 | h1x := lt_trichotomy (v₁ x) 1
  · exact h hx1
  · rw [hx1, eq_comm]
    exact equiv.eq_one_iff_eq_one.mp hx1
  · refine inv_injective ?_
    rw [← map_inv₀, ← map_inv₀]
    refine h ?_
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1x

theorem ne_zero_of_unit' {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [Nontrivial Γ₀] (v : Valuation R Γ₀) (x : Rˣ) :
    v x ≠ 0 :=
  (x.map (v : R →* Γ₀)).ne_zero

theorem ne_zero_of_isUnit' {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [Nontrivial Γ₀] (v : Valuation R Γ₀) (x : R) (hx : IsUnit x) :
    v x ≠ 0 :=
  ne_zero_of_unit' v hx.unit

end Valuation

import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs
import ClassFieldTheory.Mathlib.RepresentationTheory.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Herbrand quotient of the trivial representation

In this file, we show the Herbrand quotient of a trivial representation is `1`.
-/

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

open groupCohomology

namespace Representation

omit [Fintype G] in
@[simp] lemma oneSubGen_trivial_int_eq_zero : (trivial ℤ G ℤ).oneSubGen = 0 := by
  ext; simp

omit [Fintype G] in
@[simp] lemma tateZ0_trivial_int_eq_top : (trivial ℤ G ℤ).tateZ0 = ⊤ := by simp

omit [IsCyclic G] in
@[simp] lemma tateB0_trivial_int_eq_span_card :
    (trivial ℤ G ℤ).tateB0 = Ideal.span {(Nat.card G : ℤ)} := by
  ext; simp [tateB0, Ideal.mem_span_singleton', mul_comm]

def tateH0TrivIntAddEquivQuotCard :
    (trivial ℤ G ℤ).TateH0 ≃ₗ[ℤ] ℤ ⧸ Ideal.span {(Nat.card G : ℤ)} :=
  Submodule.Quotient.equiv _ _
    (LinearEquiv.ofEq _ _ tateZ0_trivial_int_eq_top ≪≫ₗ Submodule.topEquiv) <| by
      simp only [Submodule.submoduleOf, tateB0_trivial_int_eq_span_card]
      exact Submodule.map_comap_eq_of_surjective (LinearEquiv.surjective _) _

variable (G) in
noncomputable def tateH0TrivIntEquivZModCard :
    (trivial ℤ G ℤ).TateH0 ≃ₗ[ℤ] ZMod (Nat.card G) :=
  tateH0TrivIntAddEquivQuotCard ≪≫ₗ (Int.quotientSpanNatEquivZMod _).toIntLinearEquiv

theorem card_tateH0_trivial_int : Nat.card (trivial ℤ G ℤ).TateH0 = Nat.card G := by
  rw [Nat.card_congr (tateH0TrivIntEquivZModCard G).toEquiv, Nat.card_zmod]

instance : Subsingleton (trivial ℤ G ℤ).tateZNeg1 := by
  unfold tateZNeg1
  rw [norm_trivial_int_eq_card]
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using ha
  obtain rfl : b = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using hb
  simp

instance : Subsingleton (trivial ℤ G ℤ).TateHNeg1 := Quot.Subsingleton

variable (G) in
theorem herbrandQuotient_trivial_int_eq_card : herbrandQuotient (trivial ℤ G ℤ) = Nat.card G := by
  unfold herbrandQuotient
  rw [card_tateH0_trivial_int, Nat.card_of_subsingleton (0 : (trivial ℤ G ℤ).TateHNeg1)]
  simp only [Nat.cast_one, div_one]

end Representation

variable (G) in
lemma Rep.herbrandQuotient_trivial_int_eq_card : herbrandQuotient (trivial ℤ G ℤ) = Nat.card G := by
  classical rw [trivial, herbrandQuotient_of, Representation.herbrandQuotient_trivial_int_eq_card]

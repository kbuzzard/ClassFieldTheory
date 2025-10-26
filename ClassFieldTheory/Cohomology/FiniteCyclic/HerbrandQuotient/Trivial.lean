import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Defs
import Mathlib.Data.ZMod.QuotientRing

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

open groupCohomology
  Representation

omit [IsCyclic G] in
@[simp] lemma norm_trivial_int_eq_card : (trivial ℤ G ℤ).norm = Nat.card G := by
  ext; simp [Representation.norm]

omit [Fintype G] in
@[simp] lemma oneSubGen_trivial_int_eq_zero : (trivial ℤ G ℤ).oneSubGen = 0 := by
  ext; simp

omit [Fintype G] in
@[simp] lemma herbrandZ0_trivial_int_eq_top : (trivial ℤ G ℤ).herbrandZ0 = ⊤ := by simp

omit [IsCyclic G] in
@[simp] lemma herbrandB0_trivial_int_eq_span_card :
    (trivial ℤ G ℤ).herbrandB0 = Ideal.span {(Nat.card G : ℤ)} := by
  ext; simp [herbrandB0, Ideal.mem_span_singleton', mul_comm]

def herbrandH0TrivIntAddEquivQuotCard : (trivial ℤ G ℤ).herbrandH0 ≃ₗ[ℤ]
    ℤ ⧸ Ideal.span {(Nat.card G : ℤ)} :=
  Submodule.Quotient.equiv _ _
    (LinearEquiv.ofEq _ _ herbrandZ0_trivial_int_eq_top ≪≫ₗ Submodule.topEquiv) <| by
      simp only [Submodule.submoduleOf, herbrandB0_trivial_int_eq_span_card]
      exact Submodule.map_comap_eq_of_surjective (LinearEquiv.surjective _) _

variable (G) in
noncomputable def herbrandH0TrivIntEquivZModCard :
    (trivial ℤ G ℤ).herbrandH0 ≃ₗ[ℤ] ZMod (Nat.card G) :=
  herbrandH0TrivIntAddEquivQuotCard ≪≫ₗ (Int.quotientSpanNatEquivZMod _).toIntLinearEquiv

theorem card_herbrandH0_trivial_int : Nat.card (trivial ℤ G ℤ).herbrandH0 = Nat.card G := by
  rw [Nat.card_congr (herbrandH0TrivIntEquivZModCard G).toEquiv, Nat.card_zmod]

instance : Subsingleton (trivial ℤ G ℤ).herbrandZ1 := by
  unfold herbrandZ1
  rw [norm_trivial_int_eq_card]
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have : a = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using ha
  have : b = 0 := by simpa [ne_of_gt (Nat.card_pos (α := G))] using hb
  simp [*]

instance : Subsingleton (trivial ℤ G ℤ).herbrandH1 :=
  Quot.Subsingleton

variable (G) in
theorem Representation.herbrandQuotient_trivial_int_eq_card :
    herbrandQuotient (trivial ℤ G ℤ) = Nat.card G := by
  unfold herbrandQuotient
  rw [card_herbrandH0_trivial_int, Nat.card_of_subsingleton (0 : (trivial ℤ G ℤ).herbrandH1)]
  simp only [Nat.cast_one, div_one]

variable (G) in
theorem Rep.herbrandQuotient_trivial_int_eq_card :
    Rep.herbrandQuotient (trivial ℤ G ℤ) = Nat.card G := by
  classical rw [trivial, herbrandQuotient_of,
    Representation.herbrandQuotient_trivial_int_eq_card]

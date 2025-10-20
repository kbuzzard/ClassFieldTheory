import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

namespace UniqueFactorizationMonoid

variable {M : Type*} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]

theorem factors_irreducible_of_subsingleton_units
    {x : M} (hx : Irreducible x) (hx₀ : x ≠ 0) :
    UniqueFactorizationMonoid.factors x = {x} := by
  obtain ⟨p, hp, hpx⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hx₀ hx dvd_rfl
  replace hpx := associated_iff_eq.mp hpx; subst hpx
  obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem hp
  have assoc := UniqueFactorizationMonoid.factors_prod hx₀
  rw [hm, Multiset.prod_cons, associated_iff_eq, mul_eq_left₀ hx₀] at assoc
  suffices m = 0 by rw [hm, this, Multiset.cons_zero]
  induction m using Multiset.induction with
  | empty => rfl
  | cons y m ih =>
    rw [Multiset.prod_cons] at assoc
    have := eq_one_of_mul_right assoc; subst this
    have : 1 ∈ UniqueFactorizationMonoid.factors x := by rw [hm]; aesop
    exact ((UniqueFactorizationMonoid.irreducible_of_factor 1 this).not_isUnit (by simp)).elim

theorem factors_spec_of_subsingleton_units
    {M : Type*} [CancelCommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    {x : M} {m : Multiset M} (h₀ : 0 ∉ m) (h₁ : Associated x m.prod) (h₂ : ∀ y ∈ m, Irreducible y) :
    UniqueFactorizationMonoid.factors x = m := by
  rw [associated_iff_eq] at h₁; subst h₁
  obtain _ | _ := subsingleton_or_nontrivial M
  · simp [Multiset.eq_zero_of_forall_notMem (s := m) (fun x ↦ by rwa [Subsingleton.elim x 0])]
  induction m using Multiset.induction with
  | empty => simp
  | cons x m ih =>
    have := UniqueFactorizationMonoid.factors_mul (by aesop : x ≠ 0)
      (Multiset.prod_ne_zero (mt Multiset.mem_cons_of_mem h₀))
    rw [associated_eq_eq, Multiset.rel_eq] at this
    rw [Multiset.prod_cons, this,
      UniqueFactorizationMonoid.factors_irreducible_of_subsingleton_units (by aesop) (by aesop),
      ih (by aesop) (by aesop), Multiset.singleton_add]

end UniqueFactorizationMonoid

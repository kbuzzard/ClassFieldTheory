import Mathlib

variable {R : Type*} [CommRing R]

lemma _root_.Module.isTorsionBy_one {A : Type*} [AddCommGroup A] [Module R A]
    (htors : Module.IsTorsionBy R A 1) : Subsingleton A :=
  .intro <| fun a b ↦ by simp_all [Module.IsTorsionBy]

open AddCommGroup in
lemma AddCommGroup.foo (A : Type*) [AddCommGroup A] [Module R A] (n : ℕ) [hn : NeZero n]
    (htors : Module.IsTorsionBy R A n) (hp : ∀ (p : ℕ) (_ : Fact p.Prime) (hpn : p ∣ n),
      (primaryComponent A p).carrier.Finite ∧ Nat.card (primaryComponent A p) ≤ p ^ padicValNat p n) :
    Finite A ∧ Nat.card A ≤ n := by
  induction n using Nat.recOnPrimePow generalizing A hn with
  | zero => exact (NeZero.ne 0 rfl).elim
  | one =>
    haveI := Module.isTorsionBy_one (by simpa using htors)
    exact ⟨inferInstance, Finite.card_le_one_iff_subsingleton.2 this⟩
  | prime_pow_mul t p m hpprime hpt hmpos IH =>
  if ht : t = 0 then simp_all else
  haveI : NeZero t := ⟨ht⟩

  specialize IH (Submodule.torsionBy R A t) (by simp) ?_
  · sorry

  sorry

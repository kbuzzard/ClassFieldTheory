import Mathlib.Algebra.CharP.Lemmas

protected theorem Commute.add_pow_prime_pow_eq'
    {R : Type*} [Semiring R] {p : ℕ} (hp : Nat.Prime p) {x y : R} (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * ∑ k ∈ Finset.Ioo 0 (p ^ n),
      x ^ (k - 1) * y ^ (p ^ n - k - 1) * ((p ^ n).choose k / p :) := by
  rw [h.add_pow_prime_pow_eq hp]
  congr 1
  simp_rw [mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_Ioo] at hi
  rw [h.left_comm, ← mul_assoc x, ← pow_succ', (h.symm.pow_right _).left_comm, ← mul_assoc y,
    ← pow_succ', Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]

theorem add_pow_prime_pow_eq'
    {R : Type*} [CommSemiring R] {p : ℕ} (hp : Nat.Prime p) (x y : R) (n : ℕ) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * ∑ k ∈ Finset.Ioo 0 (p ^ n),
      x ^ (k - 1) * y ^ (p ^ n - k - 1) * ((p ^ n).choose k / p :) :=
  (Commute.all x y).add_pow_prime_pow_eq' hp _

theorem exists_add_pow_prime_pow_eq'
    {R : Type*} [CommSemiring R] {p : ℕ} (hp : Nat.Prime p) (x y : R) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r :=
  ⟨_, add_pow_prime_pow_eq' hp x y n⟩

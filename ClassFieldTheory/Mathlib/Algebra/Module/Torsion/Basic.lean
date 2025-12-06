import Mathlib.Algebra.Module.Torsion.Basic

@[simps]
def Module.IsTorsionBy.coprime_decompose {k m1 m2: ℕ} {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (hk : k = m1 * m2) (hmm : m1.Coprime m2) (hA : Module.IsTorsionBy R M k):
    M ≃ₗ[R] Submodule.torsionBy R M m1 × Submodule.torsionBy R M m2 where
  toFun m := ⟨⟨(m2 : R) • m, by simp [← mul_smul, ← Nat.cast_mul, ← hk, hA]⟩,
    ⟨(m1 : R) • m, by simp [← mul_smul, mul_comm, ← Nat.cast_mul, ← hk, hA]⟩⟩
  map_add' := by simp
  map_smul' := by simp [← mul_smul, mul_comm]
  invFun := fun ⟨x1, x2⟩ ↦ (m1.gcdB m2 : R) • x1.1 + (m1.gcdA m2 : R) • x2.1
  left_inv x := by
    simp only [← smul_assoc, smul_eq_mul, ← add_smul]
    convert one_smul R x using 2
    rw [← Nat.cast_one, ← Nat.coprime_iff_gcd_eq_one (m := m1) (n := m2)|>.1 hmm,
      ← AddCommGroupWithOne.intCast_ofNat (m1.gcd m2), Nat.gcd_eq_gcd_ab m1 m2]
    simpa using by grind
  right_inv := fun ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ ↦ by
    simp only [Submodule.mem_torsionBy_iff] at hx1 hx2
    simp only [smul_add, ← smul_assoc, smul_eq_mul, mul_comm, Prod.mk.injEq, Subtype.mk.injEq]
    simp only [mul_smul, hx2, smul_zero, add_zero, hx1, zero_add]
    constructor
    · rw [← add_zero (_ • _ • x1), ← smul_zero (m1.gcdA m2), ← hx1, ← smul_assoc, ← smul_assoc,
        ← add_smul, smul_eq_mul, zsmul_eq_mul, ← AddCommGroupWithOne.intCast_ofNat, ← Int.cast_mul,
        ← AddCommGroupWithOne.intCast_ofNat m1, ← Int.cast_mul, ← Int.cast_add, mul_comm,
        mul_comm _ (m1 : ℤ), add_comm, ← Nat.gcd_eq_gcd_ab m1 m2, Nat.coprime_iff_gcd_eq_one.1 hmm]
      simp
    · rw [← add_zero (_ • _ • x2), ← smul_zero (m1.gcdB m2), ← hx2, ← smul_assoc, ← smul_assoc,
        ← add_smul, smul_eq_mul, zsmul_eq_mul, ← AddCommGroupWithOne.intCast_ofNat, ← Int.cast_mul,
        ← AddCommGroupWithOne.intCast_ofNat m2, ← Int.cast_mul, ← Int.cast_add, mul_comm,
        mul_comm _ (m2 : ℤ), ← Nat.gcd_eq_gcd_ab m1 m2, Nat.coprime_iff_gcd_eq_one.1 hmm]
      simp

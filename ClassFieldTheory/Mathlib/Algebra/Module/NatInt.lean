import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Int.GCD

lemma AddCommGroup.isTorsion_gcd_iff {M} (a b : ℕ) [AddCommGroup M] (x : M) :
    (a.gcd b) • x = 0 ↔ a • x = 0 ∧ b • x = 0 := by
  constructor
  · intro h
    obtain ⟨⟨n1, hn1⟩, ⟨n2, hn2⟩⟩ := Nat.gcd_dvd a b
    exact ⟨hn1 ▸ mul_comm _ n1 ▸ mul_smul n1 _ x ▸ smul_zero (A := M) n1 ▸ congr(HSMul.hSMul n1 $h),
      hn2 ▸ mul_comm _ n2 ▸ mul_smul n2 _ x ▸ smul_zero (A := M) n2 ▸ congr(HSMul.hSMul n2 $h)⟩
  · rintro ⟨ha, hb⟩
    rw [← natCast_zsmul, Nat.gcd_eq_gcd_ab, mul_comm (a : ℤ), mul_comm (b : ℤ)]
    simp [add_smul, mul_smul, ha, hb]

import ClassFieldTheory.Mathlib.Algebra.Group.Torsion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion

variable {M N : Type*}

@[simp] lemma isTorsion_additive [Monoid M] :
    AddMonoid.IsTorsion (Additive M) ↔ Monoid.IsTorsion M := .rfl

@[simp] lemma isTorsion_multiplicative [AddMonoid M] :
    Monoid.IsTorsion (Multiplicative M) ↔ AddMonoid.IsTorsion M := .rfl

@[simp] lemma isTorsion_zmod_iff {n : ℕ} : AddMonoid.IsTorsion (ZMod n) ↔ n ≠ 0 where
  mp h := by rintro rfl; exact not_isTorsion_of_isAddTorsionFree (G := ℤ) h
  mpr hn := by
    have : NeZero n := ⟨hn⟩
    simp [AddMonoid.IsTorsion, ← addOrderOf_ne_zero_iff, -addOrderOf_eq_zero_iff,
      ZMod.natCast_zmod_surjective.forall, ZMod.addOrderOf_coe, hn, Nat.gcd_le_left,
      Nat.pos_iff_ne_zero.2 hn]

variable [Monoid M] [Monoid N]

variable (M N) in
-- TODO: Make `Monoid.IsTorsion` a typeclass
@[to_additive]
lemma subsingleton_monoidHom_of_isTorsion_isMulTorsionFree (hM : Monoid.IsTorsion M)
    [IsMulTorsionFree N] : Subsingleton (M →* N) where
  allEq f g := by
    ext m
    obtain ⟨n, hn, hrm⟩ := isOfFinOrder_iff_pow_eq_one.1 <| hM m
    refine pow_left_injective hn.ne' ?_
    simp_all [← map_pow]

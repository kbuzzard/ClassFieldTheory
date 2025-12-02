import Mathlib.Algebra.Group.Units.Basic

theorem IsUnit.of_mul {M : Type*} [Monoid M] {x y z : M}
    (hxy : IsUnit (x * y)) (hzx : IsUnit (z * x)) : IsUnit x :=
  let ⟨a, ha⟩ := hxy.exists_right_inv
  let ⟨b, hb⟩ := hzx.exists_left_inv
  isUnit_iff_exists_and_exists.mpr ⟨⟨y * a, by rwa [← mul_assoc]⟩, b * z, by rwa [mul_assoc]⟩

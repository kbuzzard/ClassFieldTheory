/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Lifting coprime elements through a surjective local ring hom

If `f : R →+* S` is surjective and reflects units and `IsCoprime (f x) (f y)` then
`IsCoprime x y`.

-/

theorem _root_.IsUnit.of_mul {M : Type*} [Monoid M] {x y z : M}
    (hxy : IsUnit (x * y)) (hzx : IsUnit (z * x)) : IsUnit x :=
  let ⟨a, ha⟩ := hxy.exists_right_inv
  let ⟨b, hb⟩ := hzx.exists_left_inv
  isUnit_iff_exists_and_exists.mpr ⟨⟨y * a, by rwa [← mul_assoc]⟩, b * z, by rwa [mul_assoc]⟩
#min_imports
theorem _root_.isLocalHom_iff_one {R S F : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MulHomClass F R S] {f : F} (hf : (⇑f).Surjective) :
    IsLocalHom f ↔ ∀ ⦃x⦄, f x = 1 → IsUnit x := by
  refine ⟨fun h x hx ↦ .of_map f _ <| hx ▸ isUnit_one, fun h ↦ ⟨fun x hx ↦ ?_⟩⟩
  obtain ⟨y, hxy, hyx⟩ := isUnit_iff_exists.mp hx
  obtain ⟨y, rfl⟩ := hf y
  rw [← map_mul] at hxy hyx
  exact .of_mul (h hxy) (h hyx)
#min_imports

theorem IsLocalHom.of_ker_le_nilradical {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf1 : (⇑f).Surjective) (hf2 : RingHom.ker f ≤ nilradical R) : IsLocalHom f :=
  (isLocalHom_iff_one hf1).mpr fun x hx ↦
  sub_add_cancel x 1 ▸ IsNilpotent.isUnit_add_one <| hf2 <| by simp [hx]

theorem IsCoprime.of_map {R S : Type*} [CommRing R] [CommRing S] {x y : R}
    (f : R →+* S) (hf1 : (⇑f).Surjective) [IsLocalHom f]
    (hfxy : IsCoprime (f x) (f y)) : IsCoprime x y := by
  obtain ⟨a, b, hab⟩ := hfxy
  obtain ⟨a, rfl⟩ := hf1 a
  obtain ⟨b, rfl⟩ := hf1 b
  simp_rw [← map_mul, ← map_add] at hab
  let ⟨u, hu⟩ := (IsUnit.of_map f _ (hab ▸ isUnit_one)).exists_right_inv
  exact ⟨a * u, b * u, by simpa [add_mul, mul_right_comm] using hu⟩

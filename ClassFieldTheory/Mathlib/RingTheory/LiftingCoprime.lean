/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Lifting coprime elements through a surjective local ring hom

If `f : R →+* S` is surjective and reflects units and `IsCoprime (f x) (f y)` then
`IsCoprime x y`.

-/

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

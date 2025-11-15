/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Lifting coprime elements through a kernel-nilpotent surjective ring hom

If `f : R →+* S` is surjective with nilpotent kernel and `IsCoprime (f x) (f y)` then
`IsCoprime x y`.

-/

theorem IsCoprime.of_map {R S : Type*} [CommRing R] [CommRing S] {x y : R}
    (f : R →+* S) (hf1 : (⇑f).Surjective) (hf2 : RingHom.ker f ≤ nilradical R)
    (hfxy : IsCoprime (f x) (f y)) :
    IsCoprime x y := by
  obtain ⟨a, b, hab⟩ := hfxy
  obtain ⟨a, rfl⟩ := hf1 a
  obtain ⟨b, rfl⟩ := hf1 b
  simp_rw [← f.map_one, ← sub_eq_zero (b := f 1), ← map_mul, ← map_add, ← map_sub,
    ← RingHom.mem_ker] at hab
  let ⟨u, hu⟩ := (mem_nilradical.mp <| hf2 hab).isUnit_add_one.exists_right_inv
  exact ⟨a * u, b * u, by simpa [add_mul, mul_right_comm] using hu⟩

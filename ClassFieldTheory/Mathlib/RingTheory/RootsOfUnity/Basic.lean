import Mathlib.RingTheory.RootsOfUnity.Basic

open Polynomial

theorem image_rootsOfUnity_eq_nthRoots {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hn : n ≠ 0) : Units.val '' (rootsOfUnity n R : Set Rˣ) = (nthRootsFinset n 1 : Finset R) := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_rootsOfUnity, Units.ext_iff,
    Units.val_pow_eq_pow_val, Units.val_one, mem_nthRootsFinset (pos_of_ne_zero hn)]
  exact ⟨by grind, fun hxn ↦ ⟨.ofPowEqOne _ _ hxn hn, hxn, rfl⟩⟩

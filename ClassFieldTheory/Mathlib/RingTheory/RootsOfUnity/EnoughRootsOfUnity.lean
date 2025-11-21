import ClassFieldTheory.Mathlib.FieldTheory.Separable
import ClassFieldTheory.Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

open Polynomial

/-- If a domain `R` satisfies that `X ^ n - 1` splits in `R` and `n ≠ 0` then `R` has enough
`n`-th roots of unity. -/
theorem HasEnoughRootsOfUnity.of_splits {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hr : (X ^ n - 1 : R[X]).Factors) (hn : (n : R) ≠ 0) : HasEnoughRootsOfUnity R n := by
  have := NeZero.mk <| show n ≠ 0 by aesop
  refine .of_card_le ?_
  classical
  rw [Fintype.card_eq_nat_card, ← SetLike.coe_sort_coe,
    ← Nat.card_image_of_injective Units.val_injective, image_rootsOfUnity_eq_nthRoots this.out,
    SetLike.coe_sort_coe, Nat.card_eq_finsetCard, nthRootsFinset,
    Multiset.toFinset_card_of_nodup (nodup_nthRoots_one_of_natCast_ne_zero hn), nthRoots, C_1,
    ← hr.natDegree_eq_card_roots, ← C_1, natDegree_X_pow_sub_C]

/-- If `M` has enough `n`-th roots of unity and we are given a primitive root `ζ`, then any `n`-th
root of unity is a power of `ζ`. -/
theorem HasEnoughRootsOfUnity.exists_pow {M : Type*} [CommMonoid M] {n : ℕ} (hn : n ≠ 0)
    [HasEnoughRootsOfUnity M n] {ζ : M} (hζ : IsPrimitiveRoot ζ n) {ω : M} (hω : ω ^ n = 1) :
    ∃ i < n, ζ ^ i = ω := by
  have := NeZero.mk hn
  let ζ' : rootsOfUnity n M := ⟨.ofPowEqOne _ _ hζ.1 hn, Units.ext hζ.1⟩
  have hoζ' : orderOf ζ' = n := by
    rw [ ← orderOf_injective (Subgroup.subtype _) Subtype.val_injective ζ',
      ← orderOf_injective (Units.coeHom _) Units.val_injective]
    exact hζ.eq_orderOf.symm
  have hζ' : Subgroup.zpowers ζ' = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_zpowers, hoζ']
  classical
  simp_rw [Subgroup.eq_top_iff', mem_zpowers_iff_mem_range_orderOf, Finset.mem_image,
    Finset.mem_range, hoζ'] at hζ'
  obtain ⟨i, hin, hi⟩ := hζ' ⟨.ofPowEqOne _ _ hω hn, Units.ext hω⟩
  exact ⟨i, hin, congr(($hi).val.val)⟩

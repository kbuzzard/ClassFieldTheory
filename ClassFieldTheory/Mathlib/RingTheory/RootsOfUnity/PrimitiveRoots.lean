import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ClassFieldTheory.Mathlib.Data.Finset.Range
import ClassFieldTheory.Mathlib.FieldTheory.Separable

open Polynomial

theorem IsPrimitiveRoot.nthRoots_one_eq {R : Type*}
    [CommRing R] [IsDomain R] {n : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    nthRoots n (1 : R) = (Multiset.range n).map (ζ ^ ·) := by
  simp_rw [hζ.nthRoots_eq (one_pow n), mul_one]

theorem IsPrimitiveRoot.nthRootsFinset_one_eq {R : Type*}
    [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    nthRootsFinset n (1 : R) = (Finset.range n).image (ζ ^ ·) := by
  simp_rw [nthRootsFinset, hζ.nthRoots_one_eq, @Multiset.toFinset_map, Multiset.toFinset_range]
  congr
  subsingleton

/-- Over domain `R`, `ζ : R` is a primitive `n`-th root iff the multiset `{ ζ ^ i | 0 ≤ i < n }`
is equal to the multiset `nthRoots n 1`, and the multiset has no duplicates. -/
theorem isPrimitiveRoot_iff_nthRoots_and_nodup {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : 1 < n) {ζ : R} :
    IsPrimitiveRoot ζ n ↔
    (Multiset.range n).map (ζ ^ ·) = nthRoots n 1 ∧ (nthRoots n (1 : R)).Nodup := by
  classical
  refine ⟨fun hζ ↦ ⟨hζ.nthRoots_one_eq.symm, hζ.nthRoots_one_nodup⟩,
    fun ⟨h₁, h₂⟩ ↦ IsPrimitiveRoot.iff (by grind) |>.mpr ⟨?_, fun i h0i hin ↦ ?_⟩⟩
  · rw [← mem_nthRoots (by grind), ← h₁, Multiset.mem_map]
    simp_rw [Multiset.mem_range]
    exact ⟨1, hn, pow_one ζ⟩
  · rw [← h₁] at h₂
    replace h₂ := Multiset.inj_on_of_nodup_map h₂
    simp_rw [Multiset.mem_range] at h₂
    simpa [h0i.ne'] using h₂ i hin 0 (h0i.trans hin)

/-- If `f : R →+* S` and `ζ : R` is a primitive `n`-th root and `(n : S) ≠ 0` then `f ζ` is
a primitive `n`-th root in `S`. -/
theorem _root_.IsPrimitiveRoot.map_of_ne_zero {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (f : R →+* S) (hn : (n : S) ≠ 0) :
    IsPrimitiveRoot (f ζ) n := by
  by_cases hn1 : n = 1
  · rw [hn1, IsPrimitiveRoot.one_right_iff] at hζ
    simp [hζ, hn1]
  have : n ≠ 0 := by aesop
  replace hn1 : 1 < n := by grind
  have hζ' := hζ
  rw [isPrimitiveRoot_iff_nthRoots_and_nodup hn1] at hζ' ⊢
  constructor
  · simp_rw [← map_pow]
    change Multiset.map (f ∘ (ζ ^ ·)) _ = _
    rw [← Multiset.map_map, hζ'.1, nthRoots,
      (monic_X_pow_sub_C _ this).roots_map_of_card_eq_natDegree, Polynomial.map_sub,
      Polynomial.map_pow, map_X, map_C, map_one, nthRoots]
    · rw [← nthRoots, hζ.card_nthRoots_one, natDegree_X_pow_sub_C]
  · exact nodup_nthRoots_one_of_natCast_ne_zero hn

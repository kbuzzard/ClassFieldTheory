import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

theorem Ideal.IsMaximal.irreducible_of_ne_bot {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} [hI : I.IsMaximal] (ne_bot : I ≠ ⊥) : Irreducible I := by
  refine ⟨Ideal.isUnit_iff.not.mpr hI.ne_top, fun x y hxy ↦ ?_⟩
  rw [Ideal.isUnit_iff, Ideal.isUnit_iff]
  by_cases hx : x = ⊤
  · tauto
  by_cases hy : y = ⊤
  · tauto
  refine absurd hxy <| ne_of_gt ?_
  rw [← hI.eq_of_le hx (hxy ▸ Ideal.mul_le_right), ← hI.eq_of_le hy (hxy ▸ Ideal.mul_le_left)]
  simpa [sq] using Ideal.pow_right_strictAnti _ ne_bot hI.ne_top (by decide : 1 < 2)

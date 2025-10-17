import Mathlib.RingTheory.Localization.AtPrime.Basic

instance isLocalization_self (R : Type*) [CommSemiring R] [IsLocalRing R] :
    IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) where
  map_units x := of_not_not x.2
  surj x := ⟨(x, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa⟩

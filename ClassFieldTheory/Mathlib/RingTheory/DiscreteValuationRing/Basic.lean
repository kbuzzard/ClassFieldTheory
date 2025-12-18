import ClassFieldTheory.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ClassFieldTheory.Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

@[simp] theorem irreducible_maximalIdeal :
    Irreducible (IsLocalRing.maximalIdeal R) :=
  Ideal.IsMaximal.irreducible_of_ne_bot not_a_field'

theorem factors_maximalIdeal_pow (n : ℕ) :
    UniqueFactorizationMonoid.factors (IsLocalRing.maximalIdeal R ^ n) =
    Multiset.replicate n (IsLocalRing.maximalIdeal R) :=
  UniqueFactorizationMonoid.factors_spec_of_subsingleton_units
    (Multiset.mem_replicate.not.mpr <| mt And.right not_a_field'.symm)
    (by simp) (by simp [Multiset.mem_replicate])

theorem factors_maximalIdeal :
    UniqueFactorizationMonoid.factors (IsLocalRing.maximalIdeal R) = {IsLocalRing.maximalIdeal R} :=
  by simpa using factors_maximalIdeal_pow (n := 1)

end IsDiscreteValuationRing

import Mathlib.Algebra.Module.Torsion

open Function

namespace Module
variable {R M N : Type*}

section AddCommMonoid
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (R M) in
/-- A `R`-module `M` is torsion-free if scalar multiplication by any non-zero divisor element of `R`
is injective. -/
class IsTorsionFree where
  smul_right_injective {r : R} (hr : r ∈ nonZeroDivisors R) : Injective fun m : M ↦ r • m

instance [IsAddTorsionFree M] : IsTorsionFree ℕ M where
  smul_right_injective {n} hn := nsmul_right_injective (by simpa using hn)

-- TODO: Make `IsTorsion` a typeclass. Make it semiring-compatible
lemma subsingleton_linearMap_of_isTorsion_isTorsionFree (hM : IsTorsion R M) [IsTorsionFree R N] :
    Subsingleton (M →ₗ[R] N) where
  allEq f g := by
    ext m
    obtain ⟨⟨r, hr⟩, hrm⟩ := hM (x := m)
    refine IsTorsionFree.smul_right_injective hr ?_
    simp_all [← map_smul]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M]

instance [IsAddTorsionFree M] : IsTorsionFree ℤ M where
  smul_right_injective {n} hn := zsmul_right_injective (by simpa using hn)

end AddCommGroup
end Module

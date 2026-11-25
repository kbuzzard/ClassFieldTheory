module

public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuative extensions are extensions of valuations

If `B` is a valuative extension of `A`, then every valuation on `B` compatible with its valuative
relation extends every valuation on `A` compatible with its valuative relation. In particular
`(valuation A).HasExtension (valuation B)` holds, so mathlib's
`Valuation.HasExtension.instAlgebraInteger` makes `𝒪[B]` an `𝒪[A]`-algebra.
-/

public section

/-- If `B` is a valuative extension of `A`, then every valuation on `B` compatible with its
valuative relation extends every valuation on `A` compatible with its valuative relation. -/
instance ValuativeExtension.hasExtension {A B ΓA ΓB : Type*} [CommRing A] [Ring B]
    [LinearOrderedCommMonoidWithZero ΓA] [LinearOrderedCommMonoidWithZero ΓB]
    [ValuativeRel A] [ValuativeRel B] [Algebra A B] [ValuativeExtension A B]
    (vA : Valuation A ΓA) (vB : Valuation B ΓB) [vA.Compatible] [vB.Compatible] :
    vA.HasExtension vB :=
  ⟨ValuativeRel.isEquiv _ _⟩

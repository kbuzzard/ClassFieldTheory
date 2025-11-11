import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# TODO

Rename `mapDomain.linearEquiv`!
-/

namespace Finsupp
variable {α β M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

attribute [simp] coe_lmapDomain

-- TODO: Rename in mathlib
@[simp, norm_cast] alias toLinearMap_mapDomainLinearEquiv  := mapDomain.toLinearMap_linearEquiv

@[simp] lemma coe_mapDomainLinearEquiv (e : α ≃ β) :
    ⇑(mapDomain.linearEquiv M R e) = equivMapDomain e := by ext; simp [mapDomain.linearEquiv]

end Finsupp

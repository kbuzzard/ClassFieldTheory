import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# TODO

Rename `mapDomain.linearEquiv`!
-/

namespace Finsupp
variable {α β M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable (M R) in
@[simp] lemma coe_lmapDomain (f : α → β) : ⇑(lmapDomain M R f) = mapDomain f := rfl

-- TODO: Rename in mathlib
@[simp, norm_cast] alias toLinearMap_mapDomainLinearEquiv  := mapDomain.toLinearMap_linearEquiv

@[simp] lemma coe_mapDomainLinearEquiv (e : α ≃ β) :
    ⇑(mapDomain.linearEquiv M R e) = equivMapDomain e := by ext; simp [mapDomain.linearEquiv]

end Finsupp

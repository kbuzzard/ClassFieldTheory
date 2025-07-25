import Mathlib.LinearAlgebra.Finsupp.Defs

namespace Finsupp
variable {α β M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable (M R) in
@[simp] lemma coe_lmapDomain (f : α → β) : ⇑(lmapDomain M R f) = mapDomain f := rfl

-- TODO: Rename `mapDomain.linearEquiv`!
@[simp, norm_cast] lemma toLinear_mapDomainLinearEquiv (e : α ≃ β) :
    mapDomain.linearEquiv M R e = lmapDomain M R e := rfl

-- TODO: Rename `mapDomain.linearEquiv`!
@[simp] lemma coe_mapDomainLinearEquiv (e : α ≃ β) :
    ⇑(mapDomain.linearEquiv M R e) = equivMapDomain e := by ext; simp [mapDomain.linearEquiv]

end Finsupp

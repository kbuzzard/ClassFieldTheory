import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.LocalField.Basic
/-!

# Instances for nonarch local fields

-/

namespace IsNonarchimedeanLocalField

open ValuativeRel

-- Andrew Yang says he has a sorry-free proof of this:
lemma valuation_ringEquiv {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (e : L ≃+* L) (x : L) :
    valuation L (e x) = valuation L x := sorry

instance (G : Type*) [Group G] (L : Type*) [Field L] [TopologicalSpace L] [ValuativeRel L]
    [IsNonarchimedeanLocalField L] [MulSemiringAction G L] : MulSemiringAction G 𝒪[L] where
  smul g r := ⟨g • r.1, by
    obtain ⟨r, hr⟩ := r
    rw [Valuation.mem_integer_iff] at hr
    rwa [← valuation_ringEquiv (MulSemiringAction.toRingEquiv G L g) r] at hr⟩
  one_smul r := Subtype.ext <| one_smul G _
  mul_smul g h r := Subtype.ext <| mul_smul g h _
  smul_zero g := Subtype.ext <| smul_zero g
  smul_add g r s := Subtype.ext <| smul_add g _ _
  smul_one g := Subtype.ext <| smul_one g
  smul_mul g r s := Subtype.ext <| smul_mul' g _ _

-- Andrew has this on a branch (this is not specific to nonarch local fields)
instance (K : Type*) [CommRing K] [ValuativeRel K]
    (L : Type*) [CommRing L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] :
    SMul 𝒪[K] 𝒪[L] where
  smul r s := ⟨r.1 • s.1, by
    obtain ⟨r, hr⟩ := r
    obtain ⟨s, hs⟩ := s
    rw [Valuation.mem_integer_iff] at hr hs ⊢
    rw [Algebra.smul_def, Valuation.map_mul]
    apply mul_le_one₀ _ zero_le' hs
    rw [← map_one (valuation L), ← Valuation.Compatible.vle_iff_le,
      ← RingHom.map_one (algebraMap K L), ValuativeExtension.vle_iff_vle]
    rw [← map_one (valuation K), ← Valuation.Compatible.vle_iff_le] at hr
    exact hr⟩

-- Probably not how I'm supposed to be doing this (this is not specific to nonarch local fields)
instance (K : Type*) [CommRing K] [ValuativeRel K]
    (L : Type*) [CommRing L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] :
    Algebra 𝒪[K] 𝒪[L] where
  algebraMap := {
    toFun r := ⟨algebraMap K L r.1, sorry⟩ -- there is probably a better approach to this instance
    map_add' := sorry
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
  }
  commutes' := sorry
  smul_def' := sorry

instance (G : Type*) [Group G] (K : Type*) [CommRing K] [ValuativeRel K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G 𝒪[K] 𝒪[L] where -- this needs nonarch local field
  smul_comm σ _ _ := Subtype.ext <| smul_comm σ _ _

instance (G : Type*) [Group G] (K : Type*) [CommRing K] [ValuativeRel K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsGaloisGroup G 𝒪[K] 𝒪[L] where
  faithful := sorry -- follows from `IsGaloisGroup G K L`
  commutes := inferInstance
  isInvariant := sorry -- follows from `IsGaloisGroup G K L`

end IsNonarchimedeanLocalField

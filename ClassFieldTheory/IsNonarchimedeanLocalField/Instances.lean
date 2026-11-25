module

public import ClassFieldTheory.Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.LocalField.Basic

/-!
# Instances for nonarch local fields
-/

public section

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

-- The `𝒪[K]`-algebra structure on `𝒪[L]` is mathlib's `Valuation.HasExtension.instAlgebraInteger`,
-- via `ValuativeExtension.hasExtension`.

instance (G : Type*) [Group G] (K : Type*) [CommRing K] [ValuativeRel K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G 𝒪[K] 𝒪[L] where -- this needs nonarch local field
  smul_comm σ _ _ := Subtype.ext <| smul_comm σ _ _

end IsNonarchimedeanLocalField

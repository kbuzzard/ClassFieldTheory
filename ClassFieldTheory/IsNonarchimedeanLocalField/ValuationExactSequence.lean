import ClassFieldTheory.Cohomology.Subrep.ShortExact
import ClassFieldTheory.IsNonarchimedeanLocalField.Actions
import ClassFieldTheory.IsNonarchimedeanLocalField.Valuation
import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-!
# 1 → 𝒪[L]ˣ → Lˣ → ℤ → 0 as G-module

If L/K is a finite Galois extension of nonarch local fields, we construct the
short exact sequence `0 → Additive 𝒪[K]ˣ → Additive (Kˣ) → ℤ → 0` in `Rep ℤ G`
-/

/-- The `G`-module `Mˣ` where `G` acts on `M` distributively. -/
noncomputable abbrev Rep.units
    (G M : Type) [Monoid G] [CommMonoid M] [MulDistribMulAction G M] :
    Rep ℤ G :=
  let : MulDistribMulAction G Mˣ := Units.mulDistribMulActionRight
  Rep.ofMulDistribMulAction G Mˣ

namespace IsNonarchimedeanLocalField

open ValuativeRel CategoryTheory

/-- The `G`-rep `𝒪[L]ˣ` where `G = Gal(L/K)`. -/
@[simps!] noncomputable abbrev repUnitsInteger (G K L : Type) [Monoid G]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    [MulSemiringAction G L] [SMulCommClass G K L] : Rep ℤ G :=
  have := invariant (M := G) K (L := L)
  Rep.units G 𝒪[L]

/-- The short complex `0 ⟶ 𝒪[L]ˣ ⟶ Lˣ ⟶ ℤ ⟶ 0` of `G`-modules where `G = Gal(L/K)`. -/
noncomputable def valuationShortComplex (G K L : Type) [Group G] [Finite G]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [MulSemiringAction G L]
    [Algebra K L] [ValuativeExtension K L]
    [IsGaloisGroup G K L] : ShortComplex (Rep ℤ G) where
  X₁ := repUnitsInteger G K L
  X₂ := .units G L
  X₃ := .trivial ℤ G ℤ
  f :=
  { hom := ModuleCat.ofHom (kerV L).toIntLinearMap
    comm g := rfl }
  g :=
  { hom := ModuleCat.ofHom (v L).toIntLinearMap
    comm g := by
      ext (u : Additive Lˣ)
      obtain ⟨u, rfl⟩ := Additive.ofMul.surjective u
      simp [Rep.units]
      simp [Rep.ofMulDistribMulAction, valuationInt, valuation_smul K]
      rfl }
  zero := by ext; exact exact_kerV_v.apply_apply_eq_zero _

variable {G K L : Type} [Group G] [Finite G]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [MulSemiringAction G L]
  [Algebra K L] [ValuativeExtension K L]
  [IsGaloisGroup G K L]

-- use v_surjective, ker_v_ker, ker_v_injective in IsNonarchimedeanLocalField.Valuation
lemma valuationShortComplex.shortExact : (valuationShortComplex G K L).ShortExact :=
  .mk' (ShortComplex.ShortExact.rep_exact_iff_function_exact.mpr exact_kerV_v)
    ((Rep.mono_iff_injective _).mpr kerV_injective)
    ((Rep.epi_iff_surjective _).mpr v_surjective)

end IsNonarchimedeanLocalField

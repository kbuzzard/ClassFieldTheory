import ClassFieldTheory.IsNonarchimedeanLocalField.Valuation
import ClassFieldTheory.IsNonarchimedeanLocalField.Instances
/-

# 1 → 𝒪[L]ˣ → Lˣ → ℤ → 0 as G-module

If L/K is a finite Galois extension of nonarch local fields, we construct the
short exact sequence `0 → Additive (𝒪[K]ˣ) → Additive (Kˣ) → ℤ → 0` in `Rep ℤ G`

-/
section elsewhere

@[reducible] def Units.instMulDistribMulAction_right
    (G R : Type*) [Monoid G] [Semiring R] [MulSemiringAction G R] :
    MulDistribMulAction G Rˣ := {
  smul g r := ⟨g • r, g • r⁻¹, by simp [← smul_mul'], by simp [← smul_mul']⟩
  one_smul r := by ext; exact one_smul G (r : R)
  mul_smul g h r := by ext; exact mul_smul g h (r : R)
  smul_mul g r s := by ext; exact smul_mul' g (r : R) (s : R)
  smul_one g := by ext; exact smul_one g
}

noncomputable def Rep.ofAlgebraAutOnUnits' (G R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] :
    Rep ℤ G :=
  letI : MulDistribMulAction G Sˣ := Units.instMulDistribMulAction_right G S
  Rep.ofMulDistribMulAction G Sˣ

namespace IsNonarchimedeanLocalField

open ValuativeRel CategoryTheory

noncomputable def valuationShortComplex (G K L : Type) [Group G] [Finite G]
    [CommRing K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [MulSemiringAction G L]
    [Algebra K L] [ValuativeExtension K L]
    [IsGaloisGroup G K L] : ShortComplex (Rep ℤ G) where
  X₁ := Rep.ofAlgebraAutOnUnits' G 𝒪[K] 𝒪[L]
        -- restrict along an isomorphism
  X₂ := Rep.ofAlgebraAutOnUnits' G K L
  X₃ := .trivial ℤ G ℤ
  f := {
    hom := ModuleCat.ofHom (ker_v L).toIntLinearMap
    comm g := rfl
  }
  g := {
    hom := ModuleCat.ofHom (v L).toIntLinearMap
    comm g := by
      ext (u : Additive Lˣ)
      obtain ⟨u, rfl⟩ := Additive.ofMul.surjective u
      sorry
  }
  zero := sorry -- v(𝒪[L]ˣ) = 0

variable {G K L : Type} [Group G] [Finite G]
    [CommRing K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [MulSemiringAction G L]
    [Algebra K L] [ValuativeExtension K L]
    [IsGaloisGroup G K L]

lemma valuationShortComplex.shortExact : (valuationShortComplex G K L).ShortExact := sorry

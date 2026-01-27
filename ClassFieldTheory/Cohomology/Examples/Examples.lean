import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!

# Group cohomology -- an overview

This file demonstrates what is already in mathlib. Analogous results for group
homology are also there.

-/

suppress_compilation

universe u

section cohomology

open groupCohomology

section category_theory_version

open CategoryTheory

-- let G be a group
variable (G : Type u) [Group G]
    -- let R be a coefficient ring (R = ℤ in the talk but the general case is no harder)
    (R : Type u) [CommRing R]
    -- and let M be an R[G]-module in category theory land
    (M : Rep R G) (n : ℕ)

-- `groupCohomology` now spits out terms of type `ModuleCat R`.
-- #check groupCohomology M n -- ModuleCat R

-- this is the inhomogeneous cocycles so useful for computation
example (n : ℕ) : cocycles M n ⟶ groupCohomology M n := groupCohomology.π M n

example (n : ℕ) : Epi (groupCohomology.π M n) := inferInstance

-- Here `P` is *any* projective resolution of the trivial G-module R
example (P : ProjectiveResolution (Rep.trivial R G R)) :
    groupCohomology M n ≅ (P.complex.linearYonedaObj R M).homology n :=
  groupCohomologyIso M n P

-- 1-cocycles and 1-coboundaries

example (f : G → M) : f ∈ cocycles₁ M ↔ ∀ g h : G, f (g * h) = f g + (M.ρ g) (f h) := by
  rw [mem_cocycles₁_iff]
  grind

example (f : G → M) : f ∈ coboundaries₁ M ↔ ∃ m, f = fun g ↦ M.ρ g m - m := by
  apply exists_congr
  simp [d₀₁, eq_comm]

example : coboundaries₁ M ≤ cocycles₁ M := coboundaries₁_le_cocycles₁ M

example : ModuleCat.of R (cocycles₁ M) ⟶ groupCohomology M 1 := H1π M

example : Epi (H1π M) := inferInstance

example (f : cocycles₁ M) : H1π M f = 0 ↔ ↑f ∈ coboundaries₁ M :=
  H1π_eq_zero_iff f

-- explicit short complex computing H¹(G,M): M ⟶ Hom(G,M) ⟶ Hom(G²,M)
example : (shortComplexH1 M).X₁ = M.V := rfl
example : (shortComplexH1 M).X₂ = ModuleCat.of R (G → M.V) := rfl
example : (shortComplexH1 M).X₃ = ModuleCat.of R (G × G → M.V) := rfl
example (m : M.V) : d₀₁ M m = fun g ↦ M.ρ g m - m := rfl
example (f : G → M.V) : d₁₂ M f = fun (g,h) ↦ M.ρ g (f h) - f (g * h) + f g := rfl
example : (shortComplexH1 M).f = d₀₁ M := rfl
example : (shortComplexH1 M).g = d₁₂ M := rfl

example : groupCohomology M 1 ≅ (shortComplexH1 M).moduleCatLeftHomologyData.H := H1Iso M

-- long exact sequence is just lots and lots of short exact sequences!

open CategoryTheory ShortComplex

-- let 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0 be a short exact sequence of R[G]-modules
variable (X : ShortComplex (Rep R G)) (hX : ShortExact X)

-- indices i and j = i + 1 for long exact sequence
variable (i j : ℕ) (hij : i + 1 = j)

-- Hⁱ(G,X₃) ⟶ Hʲ(G,X₁) ⟶ Hʲ(G,X₂) is exact when j=i+1
example : (mapShortComplex₁ hX hij).X₁ = groupCohomology X.X₃ i := rfl
example : (mapShortComplex₁ hX hij).X₂ = groupCohomology X.X₁ j := rfl
example : (mapShortComplex₁ hX hij).X₃ = groupCohomology X.X₂ j := rfl
example : (mapShortComplex₁ hX hij).f = (map_cochainsFunctor_shortExact hX).δ i j hij := rfl
example : (mapShortComplex₁ hX hij).g = (functor R G j).map X.f := rfl
example : (mapShortComplex₁ hX hij).Exact := mapShortComplex₁_exact hX hij

-- Hʲ(G,X₁) ⟶ Hʲ(G,X₂) ⟶ Hʲ(G,X₃) is exact
example : (mapShortComplex₂ X j).Exact := mapShortComplex₂_exact hX j

-- Hⁱ(G,X₂) ⟶ Hⁱ(G,X₃) ⟶ Hʲ(G,X₁) is exact
example : (mapShortComplex₃ hX hij).Exact := mapShortComplex₃_exact hX hij

end category_theory_version

section type_version

-- let G be a group
variable (G : Type u) [Group G]
    -- let R be a coefficient ring (R = ℤ in the talk but the general case is no harder)
    (R : Type u) [CommRing R]
    -- and let M be equipped with commuting actions of G and R, this time in type land.
    (M : Type u) [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]

example (f : G → M) : IsCocycle₁ f ↔ ∀ g h : G, f (g * h) = g • f h + f g := by
  rfl

example (f : G → M) : IsCoboundary₁ f ↔ ∃ m : M, ∀ g : G, g • m - m = f g := by
  rfl

example (f : G → M) :  IsCocycle₁ f ↔ f ∈ cocycles₁ (Rep.ofDistribMulAction R G M) := by
  constructor
  · exact fun h ↦ (mem_cocycles₁_iff (A := Rep.ofDistribMulAction R G M) f).2 h
  · exact fun a ↦ isCocycle₁_of_mem_cocycles₁ f a

end type_version

end cohomology

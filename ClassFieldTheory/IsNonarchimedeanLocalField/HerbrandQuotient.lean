import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.SES
import ClassFieldTheory.Cohomology.FiniteCyclic.HerbrandQuotient.Trivial
import ClassFieldTheory.IsNonarchimedeanLocalField.ValuationExactSequence
/-

# Herbrand quotient of Lˣ

If L/K is a finite cyclic extension of nonarchimedean local fields then `h(Lˣ)=[L:K]`.

-/

open IsNonarchimedeanLocalField

open scoped ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    (G : Type) [Group G] [Finite G] [IsCyclic G]
    [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- herbrand quotient of `𝒪[L]ˣ is 1` -/
theorem Rep.herbrandQuotient_isNonarchimedeanLocalField_integer_units :
    herbrandQuotient
    (repUnitsInteger G K L : Rep ℤ G) = 1 := by
  sorry -- hard work -- see https://kbuzzard.github.io/ClassFieldTheory/blueprint/sect0003.html#lem:herbrand%20local%20units
  -- This is the assertion that if L/K is cyclic then h(𝒪[L]ˣ)=1
  -- we have lemma 80 https://kbuzzard.github.io/ClassFieldTheory/blueprint/sect0003.html#lem:serre_approx

/-- herbrand quotient of `Lˣ is [L:K]` -/
theorem Rep.herbrandQuotient_isNonarchimedeanLocalField_units :
    herbrandQuotient
    ((Rep.res (IsGaloisGroup.mulEquivAlgEquiv G K L)).obj (Rep.ofAlgebraAutOnUnits K L) : Rep ℤ G)
    = Module.finrank K L := by
  have := Fintype.ofFinite G
  have h1 : (valuationShortComplex G K L).X₁.herbrandQuotient = 1 :=
    Rep.herbrandQuotient_isNonarchimedeanLocalField_integer_units K L G
  have h1' : (valuationShortComplex G K L).X₁.herbrandQuotient ≠ 0 := by
    simp [h1]
  have h3 : (valuationShortComplex G K L).X₃.herbrandQuotient = Nat.card G :=
    Rep.herbrandQuotient_trivial_int_eq_card G
  have h3' : (valuationShortComplex G K L).X₃.herbrandQuotient ≠ 0 := by
    simp [h3]
  have := herbrandQuotient_eq_of_shortExact valuationShortComplex.shortExact h1' ?_ h3'
  · convert this
    simp [h1, h3, -Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank G K L]
  · apply Rep.herbrandQuotient_ne_zero_of_shortExact₂
      valuationShortComplex.shortExact h1' h3'

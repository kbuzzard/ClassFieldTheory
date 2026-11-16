module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# The normal basis theorem for an abstract Galois group

Mathlib proves the normal basis theorem `IsGalois.normalBasis` for the Galois group `Gal(L/K)` of
a finite Galois extension `L/K`. This file proves it for an abstract finite group `G` acting on `L`
with `IsGaloisGroup G K L`, so that the basis is indexed by `G` and `G` acts by `g • x`.

## Main results

* `IsGaloisGroup.exists_linearIndependent_smul`: the normal basis theorem. There is `x : L` such
  that the elements `g • x`, for `g : G`, are linearly independent over `K`.
* `IsGaloisGroup.normalBasis G K L`: a `K`-basis of `L` indexed by `G` that is a single `G`-orbit,
  namely `normalBasis G K L g = g • normalBasis G K L 1` (`IsGaloisGroup.normalBasis_apply`).
* `IsGaloisGroup.smul_normalBasis`: `G` acts on `normalBasis G K L` by left multiplication on the
  indices.
* `IsGaloisGroup.normalBasis_repr_smul`: `G` acts on the coordinates with respect to
  `normalBasis G K L` by left multiplication on the indices, so `(normalBasis G K L).repr`
  identifies `L` with the left regular representation of `G` over `K`.

## Implementation notes

As for `IsGalois.normalBasis`, the basis is built with `basisOfLinearIndependentOfCardEqFinrank`
from `IsGaloisGroup.exists_linearIndependent_smul` and `IsGaloisGroup.card_eq_finrank`. The linear
independence comes from `exists_linearIndependent_algEquiv_apply`, transported along
`IsGaloisGroup.mulEquivAlgEquiv G K L : G ≃* Gal(L/K)`.

For `G = Gal(L/K)`, simp rewrites `σ • x` to `σ x` (`AlgEquiv.smul_def`), which the simp lemmas
of this file do not match; use `simp [← AlgEquiv.smul_def]` there.
-/

public section

namespace IsGaloisGroup

variable (G K L : Type*) [Group G] [Finite G] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L]

/-- **Normal basis theorem** for an abstract Galois group: if `G` is a finite Galois group for
`L/K`, then there is `x : L` such that the elements `g • x`, for `g : G`, are linearly independent
over `K`. See `IsGaloisGroup.normalBasis` for the corresponding basis. -/
theorem exists_linearIndependent_smul : ∃ x : L, LinearIndependent K fun g : G ↦ g • x := by
  have := finiteDimensional G K L
  obtain ⟨x, hx⟩ := exists_linearIndependent_algEquiv_apply K L
  exact ⟨x, by simpa [Function.comp_def] using hx.comp _ (mulEquivAlgEquiv G K L).injective⟩

/-- Given a finite Galois group `G` for `L/K`, `normalBasis G K L` is a basis of `L` over `K`,
indexed by `G`, that is a single `G`-orbit (see `IsGaloisGroup.normalBasis_apply`). -/
noncomputable def normalBasis : Module.Basis G K L :=
  letI := Fintype.ofFinite G
  basisOfLinearIndependentOfCardEqFinrank (exists_linearIndependent_smul G K L).choose_spec
    (Fintype.card_eq_nat_card.trans <| card_eq_finrank G K L)

variable {G K L}

/-- The basis `normalBasis G K L` is the `G`-orbit of `normalBasis G K L 1`. -/
theorem normalBasis_apply (g : G) : normalBasis G K L g = g • normalBasis G K L 1 := by
  simp [normalBasis]

/-- `G` acts on `normalBasis G K L` by left multiplication on the indices. -/
@[simp]
theorem smul_normalBasis (g h : G) : g • normalBasis G K L h = normalBasis G K L (g * h) := by
  rw [normalBasis_apply h, normalBasis_apply (g * h), mul_smul]

/-- `G` acts on the coordinates with respect to `normalBasis G K L` by left multiplication on the
indices: the coordinate of `g • x` at `h` is the coordinate of `x` at `g⁻¹ * h`. -/
@[simp]
theorem normalBasis_repr_smul (g : G) (x : L) :
    (normalBasis G K L).repr (g • x) =
      ((normalBasis G K L).repr x).equivMapDomain (Equiv.mulLeft g) := by
  have : g⁻¹ • normalBasis G K L = (normalBasis G K L).reindex (Equiv.mulLeft g) := by
    ext; simp
  simpa using congr(($this).repr x)

end IsGaloisGroup

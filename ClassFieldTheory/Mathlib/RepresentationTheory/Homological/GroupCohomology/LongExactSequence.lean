module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

@[expose] public noncomputable section

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

namespace groupCohomology

-- `δ` is built on `X.map (cochainsFunctor k G)`, so `comp_δ`/`δ_comp` need `cochainsFunctor` to
-- unfold, to identify `(X.map (cochainsFunctor k G)).Xᵢ.homology n` with `groupCohomology X.Xᵢ n`.
attribute [local implicit_reducible] cochainsFunctor in
/-- `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` composes to zero. -/
@[reassoc (attr := simp)]
lemma map_comp_δ (i j : ℕ) (hij : i + 1 = j) :
    map (MonoidHom.id G) X.g i ≫ δ hX i j hij = 0 :=
  (map_cochainsFunctor_shortExact hX).comp_δ i j (ComplexShape.up_mk i j hij)

attribute [local implicit_reducible] cochainsFunctor in
/-- `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` composes to zero. -/
@[reassoc (attr := simp)]
lemma δ_comp_map (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map (MonoidHom.id G) X.f j = 0 :=
  (map_cochainsFunctor_shortExact hX).δ_comp i j (ComplexShape.up_mk i j hij)

end groupCohomology

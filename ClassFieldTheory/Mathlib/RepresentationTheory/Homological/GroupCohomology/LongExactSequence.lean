import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

open CategoryTheory ShortComplex

universe u
variable {R G : Type u} [CommRing R] [Group G]

namespace groupCohomology

lemma map_cochainsFunctor_eval_shortExact (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact (X.map <| cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℕ) n) :=
  (map_cochainsFunctor_shortExact hX).map_of_exact (HomologicalComplex.eval ..)

theorem δ_naturality {X1 X2 : ShortComplex (Rep R G)} (hX1 : X1.ShortExact)
    (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i j : ℕ) (hij : i + 1 = j) :
    (δ hX1 i j hij) ≫ map (.id G) F.τ₁ j  = map (.id G) F.τ₃ i ≫ δ hX2 i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor R G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

end groupCohomology

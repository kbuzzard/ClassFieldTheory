import Mathlib
import ClassFieldTheory.GroupCohomology.«03_inflation»
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]
variable {Q : Type} [Group Q] [DecidableEq Q] {φ : G →* Q} (surj : Function.Surjective φ)

namespace groupCohomology

#check ShortComplex.ShortExact
#check quotientToInvariants
#check quotientToInvariants


/--
Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a SES of `G`-reps. Let `K` be a subgroup.
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact as `K`-reps
-/
lemma fact1 {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map (res φ.ker.subtype)).ShortExact :=
  hS.map_of_exact _

#check Functor

#check NatIso.ofComponents

def test : Rep R G ⥤ ModuleCat R := (res φ.ker.subtype) ⋙ (groupCohomology.functor R _ 0)

theorem commutative_diagram : ((res φ.ker.subtype) ⋙ (groupCohomology.functor R _ 0)) =
    (quotientToInvariantsFunctor' surj) ⋙ (forget₂ (Rep R _) (ModuleCat R))
    := by
  sorry

section MissingPrereqs

-- theorem Action.res_forget₂ (V G H : Type*) [Category V]  [HasForget V] [Monoid G]
--   [Monoid H] (f : G →* H) : sorry := sorry

end MissingPrereqs


-- theorem hello : (res φ.ker.subtype) ⋙ (forget₂ (Rep R _) (ModuleCat R))
--     ≅  (forget₂ (Rep R _) (ModuleCat R)) := by
--   apply NatIso.ofComponents
--   swap
--   · intro X
--     rw [Functor.comp_obj]


-- theorem attempt_1 :
--     (quotientToInvariantsFunctor' surj) ⋙ (forget₂ (Rep R _) (ModuleCat R))
--     ≅ invariantsFunctor R _ := by
--   apply NatIso.ofComponents
--   swap
--   · intro X
--     simp
--     unfold res
--     rw [quotientToInvariants, Representation.quotientToInvariants]
--     sorry


--   · intro X Y f

variable (φ) in
def thebadasscomplex (S : ShortComplex (Rep R G)) : ShortComplex (ModuleCat R) :=
  mapShortComplex₂ (S.map (res φ.ker.subtype)) 0

lemma mono_mapShortComplex₁₀_f {k} [CommRing k] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Mono (groupCohomology.mapShortComplex₂ X 0).f := by
  have : Mono X.f := hX.mono_f
  apply mono_map_0_of_mono


lemma epi_mapShortComplex₁_g {k} [CommRing k] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (i : ℕ) (hX' : IsZero <| groupCohomology X.1 (i + 1)) :
    Epi (groupCohomology.mapShortComplex₂ X i).g := by
  have : (groupCohomology.mapShortComplex₃ hX (show i + 1 = i + 1 by rfl)).f
    = (groupCohomology.mapShortComplex₂ X i).g := rfl
  rw [←this, ←ShortComplex.exact_iff_epi]
  · apply mapShortComplex₃_exact
  · apply IsZero.eq_of_tgt hX'

lemma mapShortComplex₁_shortExact₀ {k} [CommRing k] {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hX' : IsZero <| H1 X.1) :
    (groupCohomology.mapShortComplex₂ X 0).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · apply groupCohomology.mapShortComplex₂_exact hX 0
  · apply mono_mapShortComplex₁₀_f hX
  · apply epi_mapShortComplex₁_g hX 0 hX'


lemma fact2 {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (thebadasscomplex φ S).ShortExact := by
  apply mapShortComplex₁_shortExact₀
  · apply  hS.map_of_exact _
  · exact hS'

  -- have : (res φ.ker.subtype)
  -- If `H¹(K, A) = 0` then we have a SES of `K`-reps `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`.
  -- Fact 2: we have the usual cohomology LES. meh
  -- Fact 3: `0 ⟶ H0(K, A) ⟶ H0(K, B) ⟶ H0(K, C) ⟶ 0` : meh
  -- Fact 4: above implies `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0` : alright

/--
Consider a surjective group hom `φ : G →* Q`, with kernel `K`.
Suppose we have a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(K,A) = 0` then the `K`-invariants form a short exact sequence in `Rep R Q`:

  `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`, where `K = φ.ker`.
-/
lemma quotientToInvariantsFunctor'_shortExact_ofShortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (S.map (quotientToInvariantsFunctor' surj)).ShortExact := by
  /-
  This is the opening section of the long exact sequence. The next term is `H¹(K,S.X₁)`, which
  is assumeed to be zero.
  -/
  sorry


def inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ surj) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ φ.ker.subtype) (n + 1)
  f := (infl surj (n + 1)).app M
  g := (rest φ.ker.subtype (n + 1)).app M
  zero := sorry

theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    Mono (inflationRestriction surj n M).f :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following square commutes by `infl_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶  Hⁿ⁺¹(G,M)    `
  `     |                   |        `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶  Hⁿ(G,up M)   `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  sorry

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is a current PR.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  sorry


end groupCohomology

end

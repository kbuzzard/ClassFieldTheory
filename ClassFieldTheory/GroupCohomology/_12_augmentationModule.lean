import Mathlib
import ClassFieldTheory.GroupCohomology._5_TrivialCohomology
import ClassFieldTheory.GroupCohomology._2_restriction
import ClassFieldTheory.GroupCohomology._6_LeftRegular
import ClassFieldTheory.GroupCohomology._8_DimensionShift


/-!
Let `R` be a commutative ring and `G` a group.
We define the augmentation module `aug R G : Rep R G` to be the kernel of
the augmentation map "ε : R[G] ⟶ R".

We construct the short exact sequence of `H`-modules for every subgroup `H` of `G`.

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`.

In the case that `G` is finite, the representation `R[G]` is coinduced, and so has
trivial cohomology (with respect to any subgroup `H`).
This implies that the connecting homomorphisms give isomorphisms for all `n > 0`

  `Hⁿ(H,R) ≅ Hⁿ⁺¹(H, aug R G)`.

We also have isomorphisms

  `H¹(H,aug R G) ≅ R ⧸ |H|R`,

  `H²(H,aug R G) ≅ 0`, assuming `NoZeroSMulDivisors ℕ R`.

-/

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

variable (R G: Type) [CommRing R] [Group G]

noncomputable section AugmentationModule

/--
The augmentation module `aug R G` is the kernel of the augmentation map

  `ε : leftRegular R G ⟶ trivial R G R`.

-/
abbrev Rep.aug : Rep R G := kernel (ε R G)

namespace Rep.aug

/--
The inclusion of `aug R G` in `leftRegular R G`.
-/
abbrev ι : aug R G ⟶ leftRegular R G := kernel.ι (ε R G)

lemma ε_comp_ι : ι R G ≫ ε R G = 0 := kernel.condition (ε R G)

lemma ε_apply_ι (v : aug R G) : ε R G (ι R G v) = 0 :=
  sorry
  -- use the previous lemma.

lemma sum_coeff_ι [Fintype G] (v : aug R G) : ∑ g : G, (ι R G v) g = 0 :=
  sorry
  -- use the previous lemma.

/--
There is an element of `aug R G` whose image in the left regular representation is `of g - of 1`.
-/
lemma exists_ofSubOfOne (g : G) : ∃ v : aug R G, ι R G v = leftRegular.of g - leftRegular.of 1 := by
  apply exists_kernelι_eq
  rw [map_sub, ε_of, ε_of, sub_self]

/--
The element of `aug R G` whose image in `leftRegular R G` is `of g - of 1`.
-/
def ofSubOfOne (g : G) : aug R G := (exists_ofSubOfOne R G g).choose

@[simp] lemma ofSubOfOne_spec (g : G) :
    ι R G (ofSubOfOne R G g) = leftRegular.of g - leftRegular.of 1 :=
  (exists_ofSubOfOne R G g).choose_spec

/--
The short exact sequence

    `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`.

-/
def aug_shortExactSequence : ShortComplex (Rep R G) where
  X₁ := aug R G
  X₂ := leftRegular R G
  X₃ := trivial R G R
  f := ι R G
  g := ε R G
  zero := ε_comp_ι R G

/--
The sequence in `Rep R G`:

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence.
-/
lemma isShortExactSequence  : (aug_shortExactSequence R G).ShortExact := sorry

/--
The sequence

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence of `H`-modules for any `H →* G`.
-/
lemma isShortExactSequence' {H : Type} [Group H] (φ : H →* G) :
    ((aug_shortExactSequence R G).map (res φ)).ShortExact := by
  sorry

open Finsupp

def leftRegularToInd₁' : (G →₀ R) →ₗ[R] G →₀ R := lmapDomain R R (fun x ↦ x⁻¹)

lemma leftRegularToInd₁'_comp_lsingle (x : G) : leftRegularToInd₁' R G ∘ₗ lsingle x = lsingle x⁻¹
    := by
  sorry

lemma leftRegularToInd₁'_comm (g : G) : leftRegularToInd₁' R G ∘ₗ (leftRegular R G).ρ g
    = (Representation.trivial R G R).ind₁' g ∘ₗ leftRegularToInd₁' R G := by
  ext : 1
  rw [LinearMap.comp_assoc, ρ_comp_lsingle, leftRegularToInd₁'_comp_lsingle,
    LinearMap.comp_assoc, leftRegularToInd₁'_comp_lsingle, Representation.ind₁'_comp_lsingle,
    mul_inv_rev, Representation.isTrivial_def, LinearMap.comp_id]

lemma leftRegularToInd₁'_comm' (g : G) :
    leftRegularToInd₁' R G ∘ₗ (Representation.trivial R G R).ind₁' g =
    (leftRegular R G).ρ g ∘ₗ leftRegularToInd₁' R G := by
  ext : 1
  rw [LinearMap.comp_assoc, Representation.ind₁'_comp_lsingle, Representation.isTrivial_def,
    LinearMap.comp_id, leftRegularToInd₁'_comp_lsingle, LinearMap.comp_assoc,
    leftRegularToInd₁'_comp_lsingle, ρ_comp_lsingle, mul_inv_rev, inv_inv]

lemma leftRegularToInd₁'_comp_leftRegularToInd₁' :
    leftRegularToInd₁' R G ∘ₗleftRegularToInd₁' R G = 1 := by
  ext : 1
  rw [LinearMap.comp_assoc, leftRegularToInd₁'_comp_lsingle, leftRegularToInd₁'_comp_lsingle,
    inv_inv]
  rfl

/--
The left regular representation is isomorphic to `ind₁'.obj (trivial R G R)`
-/
def _root_.Rep.leftRegular.iso_ind₁' : leftRegular R G ≅ ind₁'.obj (trivial R G R) where
  hom := {
    hom := ofHom (leftRegularToInd₁' R G)
    comm g := by
      ext : 1
      apply leftRegularToInd₁'_comm
  }
  inv := {
    hom := ofHom (leftRegularToInd₁' R G)
    comm g := by
      ext : 1
      apply leftRegularToInd₁'_comm'
  }
  hom_inv_id := by
    ext : 2
    apply leftRegularToInd₁'_comp_leftRegularToInd₁'
  inv_hom_id := by
    ext : 2
    apply leftRegularToInd₁'_comp_leftRegularToInd₁'

/--
For a finite group, the left regular representation is acyclic.
-/
instance _root_.Rep.leftRegular.trivialCohomology [Finite G] [DecidableEq G]:
    (leftRegular R G).TrivialCohomology :=
  .of_iso (iso_ind₁' R G)

/--
The connecting homomorphism from `Hⁿ⁺¹(G,R)` to `Hⁿ⁺²(G,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso [Finite G] [DecidableEq G] (n : ℕ) :
    IsIso (δ (isShortExactSequence R G) (n + 1) (n + 2) rfl) :=
  /-
  This connecting homomorphism is sandwiched between two modules H^{n+1}(G,R[G]) and H^{n+2}(G,R[G]),
  where P is the left regular representation.
  Then use `Rep.leftRegular.trivialCohomology` to show that both of these are zero.
  -/
  sorry

lemma H2_aug_isZero [Finite G] [NoZeroSMulDivisors ℕ R] : IsZero (H2 (aug R G)) :=
  /-
  This follows from `cohomology_aug_succ_iso` and `groupCohomology.H1_isZero_of_trivial`.
  -/
  sorry



/--
If `H` is a subgroup of a finite group `G` then the connecting homomorphism
from `Hⁿ⁺¹(H,R)` to `Hⁿ⁺²(H,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso' [Finite G] {H : Type} [Group H] {φ : H →* G}
    (inj : Function.Injective φ) [DecidableEq H] (n : ℕ) :
    IsIso (δ (isShortExactSequence' R G φ) (n + 1) (n + 2) rfl) :=
  /-
  The proof is similar to that of `cohomology_aug_succ_iso` but uses
  `Rep.leftRegular.isZero_groupCohomology'` in place of `Rep.leftRegular.isZero_groupCohomology`.
  -/
  sorry

def H1_iso [Finite G] :
    H1 (aug R G) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card G : R)}) :=
  /-
  If Tate cohomology is defined, then this is proved in the same way as the previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    `H⁰(G,R[G]) ⟶ H⁰(G,R) ⟶ H¹(aug R G) ⟶ 0`.

  We clearly have `H⁰(G,R) ≅ R`.
  The group `H⁰(G,R[G])` is also cyclic over `R`, and is generated by the norm element,
  i.e. the sum of all elements of `G`. The image of the norm element in `H⁰(G,R)` is `|G|`,
  since every element of the group is mapped by `ε` to `1`.
  -/
  sorry

def H1_iso' [Finite G] {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) :
    H1 (aug R G ↓ φ) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card H : R)}) :=
  /-
  If Tate cohomology is defined, then this is proved in the same way as the previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    H⁰(H,R[G]) ⟶ H⁰(H,R) ⟶ H¹(aug R G) ⟶ 0.

  We clearly have H⁰(H,R) = R.
  The group H⁰(H,R[G]) is generated by the indicator functions of cosets of `H`,
  The image of such a function in H⁰(H,R) is |H|, since every element of the
  group is mapped by `ε` to `1`.
  -/
  sorry

end Rep.aug

end AugmentationModule

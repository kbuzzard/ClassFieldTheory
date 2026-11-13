module

public import ClassFieldTheory.Cohomology.Functors.Restriction
public import ClassFieldTheory.Cohomology.IndCoind.TrivialCohomology
public import ClassFieldTheory.Cohomology.LeftRegular
public import ClassFieldTheory.Cohomology.TrivialCohomology
public import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

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

  `H²(H, aug R G) ≅ 0`, assuming `IsAddTorsionFree R`.

-/

public noncomputable section

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

namespace groupCohomology

universe u

-- `homology_exact₃` is stated for `X.map (cochainsFunctor k G)`, so matching it with `map` and
-- `δ` needs `cochainsFunctor` to unfold, to identify `(X.map (cochainsFunctor k G)).Xᵢ.homology n`
-- with `groupCohomology X.Xᵢ n` (as for `map_comp_δ`).
attribute [local implicit_reducible] cochainsFunctor in
/-- Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` at `Hⁱ(G, X₃)`, stated with
`groupCohomology.map` and `groupCohomology.δ` instead of `mapShortComplex₃`. -/
lemma range_map_eq_ker_δ {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) {i j : ℕ} (hij : i + 1 = j) :
    LinearMap.range (map (MonoidHom.id G) X.g i).hom = LinearMap.ker (δ hX i j hij).hom :=
  ((map_cochainsFunctor_shortExact hX).homology_exact₃ i j
    (ComplexShape.up_mk i j hij)).moduleCat_range_eq_ker

open RepresentationTheory.groupCohomology in
/-- For a trivial representation `A`, the isomorphism `H0IsoOfIsTrivial A` is `zeroι A`. -/
lemma H0IsoOfIsTrivial_hom_eq_zeroι {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
    [A.IsTrivial] : (H0IsoOfIsTrivial A).hom = zeroι A := by
  ext x
  simp [zeroι, shortComplexH0_f]

end groupCohomology

variable (R G : Type) [CommRing R] [Group G]

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

lemma ε_apply_ι (v : aug R G) : (ε R G).hom (ι R G|>.hom v) = 0 := congr($(ε_comp_ι R G) v)

lemma sum_coeff_ι [Fintype G] (v : aug R G) : ∑ g : G, ((ι R G).hom v).coeff g = 0 := by
  rw [← ε_apply_ι R G v, ε_eq_sum]

/--
There is an element of `aug R G` whose image in the left regular representation is `of g - of 1`.
-/
lemma exists_ofSubOfOne (g : G) : ∃ v : aug R G, (ι R G).hom v =
    .single g 1 - .single 1 1 := by
  apply exists_kernelι_eq
  rw [map_sub, ε_of, ε_of, sub_self]

/--
The element of `aug R G` whose image in `leftRegular R G` is `of g - of 1`.
-/
def ofSubOfOne (g : G) : aug R G := (exists_ofSubOfOne R G g).choose

@[simp] lemma ofSubOfOne_spec (g : G) :
    ι R G (ofSubOfOne R G g) = .single g 1 - .single 1 1 :=
  (exists_ofSubOfOne R G g).choose_spec

/-- The short exact sequence `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`. -/
abbrev aug_shortExactSequence : ShortComplex (Rep R G) where
  X₁ := aug R G
  X₂ := leftRegular R G
  X₃ := trivial R G R
  f := ι R G
  g := ε R G
  zero := ε_comp_ι R G

lemma aug_shortExactSequence_X₁ : (aug_shortExactSequence R G).X₁ = aug R G := rfl

lemma aug_shortExactSequence_X₃ : (aug_shortExactSequence R G).X₃ = trivial R G R := rfl

/--
The sequence in `Rep R G`:

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence.
-/
lemma aug_isShortExact : (aug_shortExactSequence R G).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := equalizer.ι_mono
  epi_g := ε_epi

/--
The sequence

  `0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0`

is a short exact sequence of `H`-modules for any `H →* G`.
-/
lemma aug_isShortExact' {H : Type} [Group H] (φ : H →* G) :
    ((aug_shortExactSequence R G).map (resFunctor φ)).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.map_of_exact (aug_isShortExact R G) _

open Finsupp

def leftRegularToInd₁' : MonoidAlgebra R G →ₗ[R] G →₀ R :=
  lmapDomain R R (fun x ↦ x⁻¹) ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The inverse of `leftRegularToInd₁'`. -/
def ind₁'ToLeftRegular : (G →₀ R) →ₗ[R] MonoidAlgebra R G :=
  (MonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ lmapDomain R R (fun x ↦ x⁻¹)

@[simp]
lemma leftReugularToInd₁'_single (g : G) :
    leftRegularToInd₁' R G (.single g 1) = single g⁻¹ 1 := by
  ext; simp [leftRegularToInd₁']

@[simp]
lemma ind₁'ToLeftRegular_single (g : G) :
    ind₁'ToLeftRegular R G (single g 1) = .single g⁻¹ 1 := by
  simp [ind₁'ToLeftRegular]

lemma leftRegularToInd₁'_comp_lsingle (x : G) :
    leftRegularToInd₁' R G ∘ₗ MonoidAlgebra.lsingle x = lsingle x⁻¹ := by ext; simp

lemma ind₁'ToLeftRegular_comp_lsingle (x : G) :
    ind₁'ToLeftRegular R G ∘ₗ lsingle x = MonoidAlgebra.lsingle x⁻¹ := by ext; simp

lemma leftRegularToInd₁'_comm (g : G) : leftRegularToInd₁' R G ∘ₗ (leftRegular R G).ρ g
    = (Representation.trivial R G R).ind₁' g ∘ₗ leftRegularToInd₁' R G := by
  ext; simp

lemma ind₁'ToLeftRegular_comm (g : G) :
    ind₁'ToLeftRegular R G ∘ₗ (Representation.trivial R G R).ind₁' g =
    (leftRegular R G).ρ g ∘ₗ ind₁'ToLeftRegular R G := by
  ext; simp

lemma ind₁'ToLeftRegular_comp_leftRegularToInd₁' :
    ind₁'ToLeftRegular R G ∘ₗ leftRegularToInd₁' R G = LinearMap.id := by
  ext x : 1
  rw [LinearMap.comp_assoc, leftRegularToInd₁'_comp_lsingle, ind₁'ToLeftRegular_comp_lsingle,
    inv_inv, LinearMap.id_comp]

lemma leftRegularToInd₁'_comp_ind₁'ToLeftRegular :
    leftRegularToInd₁' R G ∘ₗ ind₁'ToLeftRegular R G = LinearMap.id := by
  ext x : 1
  rw [LinearMap.comp_assoc, ind₁'ToLeftRegular_comp_lsingle, leftRegularToInd₁'_comp_lsingle,
    inv_inv, LinearMap.id_comp]

/--
The left regular representation is isomorphic to `ind₁'.obj (trivial R G R)`
-/
def _root_.Rep.leftRegular.iso_ind₁' : leftRegular R G ≅ ind₁'.obj (trivial R G R) where
  hom := ofHom ⟨leftRegularToInd₁' R G, fun g ↦ leftRegularToInd₁'_comm R G g⟩
  inv := ofHom ⟨ind₁'ToLeftRegular R G, fun g ↦ ind₁'ToLeftRegular_comm R G g⟩
  hom_inv_id := by
    ext : 2
    apply ind₁'ToLeftRegular_comp_leftRegularToInd₁'
  inv_hom_id := by
    ext : 2
    apply leftRegularToInd₁'_comp_ind₁'ToLeftRegular

/--
For a finite group, the left regular representation is acyclic for cohomology.
-/
instance _root_.Rep.leftRegular.trivialCohomology [Finite G] :
    (leftRegular R G).TrivialCohomology := .of_iso (iso_ind₁' R G)

/--
The left regular representation is acyclic for homology.
-/
instance _root_.Rep.leftRegular.trivialHomology :
    (leftRegular R G).TrivialHomology := .of_iso (iso_ind₁' R G)

set_option linter.unusedFintypeInType false in
/--
For a finite group, the left regular representation is acyclic for Tate cohomology.
-/
instance _root_.Rep.leftRegular.trivialTateCohomology [Fintype G] :
    (leftRegular R G).TrivialTateCohomology := .of_iso (iso_ind₁' R G)

/--
The connecting homomorphism from `Hⁿ⁺¹(G,R)` to `Hⁿ⁺²(G,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso [Finite G] (n : ℕ) :
    IsIso (δ (aug_isShortExact R G) (n + 1) (n + 2) rfl) :=
  /-
  This connecting homomorphism is sandwiched between two modules `H^{n + 1}(G, R[G])` and
  `H^{n + 2}(G, R[G])`, where `P` is the left regular representation.
  Then use `Rep.leftRegular.trivialCohomology` to show that both of these are zero.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ Rep.isZero_of_trivialCohomology
    Rep.isZero_of_trivialCohomology

lemma tateCohomology_auc_succ_iso [Fintype G] (n : ℤ) :
    IsIso (TateCohomology.δ (aug_isShortExact R G) n) := by
  have : TrivialTateCohomology (leftRegular R G) := inferInstance
  exact TateCohomology.isIso_δ _ this _

lemma H2_aug_isZero [Finite G] [IsAddTorsionFree R] : IsZero (H2 (aug R G)) :=
  /-
  This follows from `cohomology_aug_succ_iso` and `groupCohomology.H1_isZero_of_trivial`.
  -/
  .of_iso (H1_isZero_of_trivial _) <| (@asIso _ _ _ _ (δ (aug_isShortExact R G) 1 2 rfl)
    (cohomology_aug_succ_iso R G 0)).symm

/--
If `H` is a subgroup of a finite group `G` then the connecting homomorphism
from `Hⁿ⁺¹(H,R)` to `Hⁿ⁺²(H,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso' [Finite G] {H : Type} [Group H] {φ : H →* G}
    (inj : Function.Injective φ) (n : ℕ) :
    IsIso (δ (aug_isShortExact' R G φ) (n + 1) (n + 2) rfl) :=
  /-
  The proof is similar to that of `cohomology_aug_succ_iso` but uses
  `Rep.leftRegular.isZero_groupCohomology'` in place of `Rep.leftRegular.isZero_groupCohomology`.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ (isZero_of_injective _ _ _ (by omega) inj) <|
    isZero_of_injective _ _ _ (by omega) inj

  /-
  If Tate cohomology is defined, then this is proved in the same way as a previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    `H⁰(G,R[G]) ⟶ H⁰(G,R) ⟶ H¹(aug R G) ⟶ 0`.

  We clearly have `H⁰(G,R) ≅ R`.
  The group `H⁰(G,R[G])` is also cyclic over `R`, and is generated by the norm element,
  i.e. the sum of all elements of `G`. The image of the norm element in `H⁰(G,R)` is `|G|`,
  since every element of the group is mapped by `ε` to `1`.
  -/
def H1_iso [Fintype G] :
    H1 (aug R G) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card G : R)}) :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| by
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact R G) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <| by
    simpa using by exact isZero_of_trivialCohomology)
  refine Submodule.Quotient.equiv _ _ (H0trivial R G).symm.toLinearEquiv ?_
  rw [← range_map_eq_ker_δ]
  apply le_antisymm
  · simp only [Nat.card_eq_fintype_card]
    intro (x : H0 _)
    simp only [Submodule.mem_map, Ideal.mem_span_singleton', exists_exists_eq_and,
      LinearMap.mem_range, forall_exists_index]
    rintro a rfl
    refine ⟨a • leftRegular.norm R G, ?_⟩
    apply (H0trivial R G).toLinearEquiv.injective
    rw [← Iso.toLinearEquiv_symm, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
      Iso.toLinearEquiv_apply, map_smul, map_smul, map_comp_H0trivial_apply,
      leftRegular.zeroι_norm]
    simp
  · rw [Submodule.map_equiv_eq_comap_symm, LinearMap.range_eq_map, ← leftRegular.span_norm,
      Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff]
    simp only [Nat.card_eq_fintype_card, Submodule.comap_coe, LinearEquiv.coe_coe,
      Set.mem_preimage, SetLike.mem_coe]
    rw [Iso.toLinearEquiv_symm, Iso.symm_symm_eq, Iso.toLinearEquiv_apply,
      map_comp_H0trivial_apply, leftRegular.zeroι_norm, map_sum]
    simp

  /-
  If Tate cohomology is defined, then this is proved in the same way as a previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    `H⁰(H,R[G]) ⟶ H⁰(H,R) ⟶ H¹(aug R G) ⟶ 0`.

  We clearly have `H⁰(H,R) = R`.
  The group `H⁰(H,R[G])` is generated by the indicator functions of cosets of `H`,
  The image of such a function in `H⁰(H,R)` is `|H|`, since every element of the
  group is mapped by `ε` to `1`.
  -/
def H1_iso' [Finite G] {H : Type} [Group H] [Fintype H] {φ : H →* G}
    (inj : Function.Injective φ) :
    H1 (aug R G ↓ φ) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card H : R)}) := by
  have := Rep.trivialCohomology_iff_res.1 (trivialCohomology R G) φ inj
  have : (trivial R G R ↓ φ).IsTrivial := ⟨fun _ ↦ by ext; simp⟩
  refine LinearEquiv.toModuleIso <|.symm ?_
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact' R G φ) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <|
      isZero_of_trivialCohomology (M := leftRegular R G ↓ φ))
  refine Submodule.Quotient.equiv _ _ (H0IsoOfIsTrivial (trivial R G R ↓ φ)).symm.toLinearEquiv ?_
  rw [← range_map_eq_ker_δ, LinearMap.range_eq_map, ← leftRegular.res_span_norm R G φ inj,
    Submodule.map_span, Submodule.map_span, ← Set.range_comp]
  have key (g : G) : (map (MonoidHom.id H) (resMap φ (ε R G)) 0).hom (res_norm R φ g) =
      (H0IsoOfIsTrivial (trivial R G R ↓ φ)).symm.toLinearEquiv (Nat.card H : R) := by
    rw [← Iso.toLinearEquiv_symm, LinearEquiv.eq_symm_apply, Iso.toLinearEquiv_apply,
      H0IsoOfIsTrivial_hom_eq_zeroι, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      RepresentationTheory.groupCohomology.zeroι_naturality, ModuleCat.hom_comp,
      LinearMap.comp_apply, leftRegular.zeroι_res_norm]
    simp
  simp [key, Iso.toLinearEquiv_apply _, Function.comp_def]

end Rep.aug

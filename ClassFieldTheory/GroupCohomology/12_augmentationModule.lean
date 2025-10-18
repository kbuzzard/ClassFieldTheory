import Mathlib
import ClassFieldTheory.GroupCohomology.«05_TrivialCohomology»
import ClassFieldTheory.GroupCohomology.«02_restriction»
import ClassFieldTheory.GroupCohomology.«06_LeftRegular»
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import ClassFieldTheory.Mathlib.RepresentationTheory.Invariants


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

lemma ε_apply_ι (v : aug R G) : ε R G (ι R G v) = 0 := congr($(ε_comp_ι R G) v)

lemma sum_coeff_ι [Fintype G] (v : aug R G) : ∑ g : G, (ι R G v) g = 0 := by
  rw [← ε_apply_ι R G v, ε_eq_sum]

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
abbrev aug_shortExactSequence : ShortComplex (Rep R G) where
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
    ((aug_shortExactSequence R G).map (res φ)).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.map_of_exact (aug_isShortExact R G) _

open Finsupp

def leftRegularToInd₁' : (G →₀ R) →ₗ[R] G →₀ R := lmapDomain R R (fun x ↦ x⁻¹)

@[simp]
lemma leftReugularToInd₁'_single (g : G) :
    leftRegularToInd₁' R G (single g 1) = single g⁻¹ 1 := by
  ext; simp [leftRegularToInd₁']

lemma leftRegularToInd₁'_comp_lsingle (x : G) :
    leftRegularToInd₁' R G ∘ₗ lsingle x = lsingle x⁻¹ := by ext; simp

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
    leftRegularToInd₁' R G ∘ₗ leftRegularToInd₁' R G = 1 := by
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
instance _root_.Rep.leftRegular.trivialCohomology [Fintype G] :
    (leftRegular R G).TrivialCohomology := .of_iso (iso_ind₁' R G)

/--
The connecting homomorphism from `Hⁿ⁺¹(G,R)` to `Hⁿ⁺²(G,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso [Fintype G] (n : ℕ) :
    IsIso (δ (aug_isShortExact R G) (n + 1) (n + 2) rfl) :=
  /-
  This connecting homomorphism is sandwiched between two modules H^{n+1}(G,R[G]) and H^{n+2}(G,R[G]),
  where P is the left regular representation.
  Then use `Rep.leftRegular.trivialCohomology` to show that both of these are zero.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ Rep.isZero_of_trivialCohomology
    Rep.isZero_of_trivialCohomology

lemma H2_aug_isZero [Fintype G] [IsAddTorsionFree R] : IsZero (H2 (aug R G)) :=
  /-
  This follows from `cohomology_aug_succ_iso` and `groupCohomology.H1_isZero_of_trivial`.
  -/
  .of_iso (H1_isZero_of_trivial _) <| (@asIso _ _ _ _ (δ (aug_isShortExact R G) 1 2 rfl)
    (cohomology_aug_succ_iso R G 0)).symm

/--
If `H` is a subgroup of a finite group `G` then the connecting homomorphism
from `Hⁿ⁺¹(H,R)` to `Hⁿ⁺²(H,aug R G)` is an isomorphism.
-/
lemma cohomology_aug_succ_iso' [Fintype G] {H : Type} [Group H] {φ : H →* G}
    (inj : Function.Injective φ) (n : ℕ) :
    IsIso (δ (aug_isShortExact' R G φ) (n + 1) (n + 2) rfl) :=
  /-
  The proof is similar to that of `cohomology_aug_succ_iso` but uses
  `Rep.leftRegular.isZero_groupCohomology'` in place of `Rep.leftRegular.isZero_groupCohomology`.
  -/
  groupCohomology.isIso_δ_of_isZero _ _ (isZero_of_injective _ _ _ (by omega) inj) <|
    isZero_of_injective _ _ _ (by omega) inj

lemma ModuleCat.Iso_symm_iso (M N : ModuleCat R) (e : M ≅ N)  :
  e.symm.toLinearEquiv = e.toLinearEquiv.symm := rfl

lemma ModuleCat.Iso_hom (M N : ModuleCat R) (e : M ≅ N) (x : M) : e.toLinearEquiv x = e.hom x := rfl

abbrev leftRegular.norm' [Fintype G] : (leftRegular R G).ρ.invariants :=
  ⟨∑ g : G, leftRegular.of g, fun g ↦ by
    simpa [leftRegular.of] using show ∑ x : G, leftRegular.of (g * x) = _ from
    Finset.sum_equiv (Equiv.mulLeft g) (by grind) <| fun _ _ ↦ rfl⟩

abbrev leftRegular.res_norm' [Fintype G] {H : Type} [Group H] (g : G) (φ : H →* G)
    (inj : φ.toFun.Injective) : (leftRegular R G ↓ φ).ρ.invariants :=
  letI : Fintype H := Fintype.ofInjective _ inj
  ⟨∑ h : H, leftRegular.of (φ h * g), fun h ↦ by
    simpa [leftRegular.of] using show ∑ x : H, leftRegular.of _ = _ by
      simpa [← mul_assoc, ← leftRegular.of_def] using Finset.sum_equiv (Equiv.mulLeft h) (by grind)
        (by simp)⟩

attribute [local simp] leftRegular.of in
def leftRegular.norm [Fintype G] : H0 (leftRegular R G) :=
  (H0Iso (leftRegular R G)).toLinearEquiv.symm (leftRegular.norm' R G)

def leftRegular.res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G) (inj : φ.toFun.Injective) (g : G) :
    H0 ((leftRegular R G) ↓ φ) :=
  (H0Iso ((leftRegular R G) ↓ φ)).toLinearEquiv.symm (leftRegular.res_norm' R G g φ inj)

open RepresentationTheory.groupCohomology

lemma leftRegular.zeroι_norm [Fintype G] :
    zeroι _ (norm R G) = ∑ g : G, leftRegular.of g := by
  have := (H0Iso (leftRegular R G)).toLinearEquiv.apply_symm_apply
    ⟨∑ g : G, MonoidAlgebra.of _ _ g,
    fun g ↦ by simpa using show ∑ x : G, MonoidAlgebra.of _ _ (g * x) = _ from
      Finset.sum_equiv (Equiv.mulLeft g) (by grind) <| fun _ _ ↦ rfl⟩
  exact congr($this)

lemma leftRegular.H0Iso_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) :
    (H0Iso ((leftRegular R G) ↓ φ)).hom (res_norm R G φ inj g) = res_norm' R G g φ inj :=
  (H0Iso _).toLinearEquiv.apply_symm_apply _

lemma leftRegular.zeroι_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) :
    letI : Fintype H := Fintype.ofInjective _ inj
    zeroι _ (res_norm R G φ inj g) = ∑ h : H, leftRegular.of (φ h * g) := by
  letI : Fintype H := Fintype.ofInjective _ inj
  dsimp [zeroι]
  erw [leftRegular.H0Iso_res_norm] -- `erw?` does nothing

lemma leftRegular.span_norm' [Fintype G] :
    Submodule.span R {norm' R G} = ⊤ := by
  ext ⟨x, hx⟩
  simp only [of_ρ, Submodule.mem_span_singleton, Subtype.ext_iff, SetLike.val_smul,
    Submodule.mem_top, iff_true]
  replace hx : ∃ a : R, ∀ g : G, x g = a := ⟨x 1, fun g ↦ by
    simpa using Finsupp.ext_iff.1 (hx g⁻¹) 1⟩
  exact ⟨hx.choose, Finsupp.ext_iff.2 fun g ↦ by simp [← hx.choose_spec g, leftRegular.of]⟩

-- instance [Fintype G] {H} [Group H] (φ : H →* G) (inj : Function.Injective φ) :
--   Fintype {(leftRegular.res_norm' R G g φ inj) | g : G} := by exact?
-- attribute [local simp] Fintype.ofFinite in
lemma leftRegular.res_span_norm' [Fintype G] {H : Type} [Group H] (φ : H →* G) (inj : φ.toFun.Injective) :
    Submodule.span R {res_norm' R G g φ inj | g : G} = ⊤ := by
  -- classical
  apply le_antisymm
  · simp
  · rintro x -
    choose σ hσ using Quotient.mk_surjective (s := QuotientGroup.rightRel φ.range)
    classical

    have : x = ∑ i, (show G →₀ _ from x.1) (σ i) • res_norm' R G (σ i) φ inj := by
      ext;
      simp [Finsupp.ext_iff, leftRegular.of_apply (R := R)]
      intro a
      rw [Finset.sum_eq_single (Quotient.mk _ a)]
      · have (i j : G) : QuotientGroup.rightRel φ.range i j → (show G →₀ R from x.1) i =
          (show G →₀ R from x.1) j := fun hij ↦ by
          obtain ⟨x, hx⟩ := x
          simp
          simp at hx
          obtain ⟨k, hk⟩ := by simpa [QuotientGroup.rightRel_apply] using hij
          have := by simpa [Representation.ofMulAction_def, Finsupp.ext_iff] using hx k
          simpa [mapDomain, Finsupp.sum_fintype, Finsupp.single_apply,
            hk, mul_assoc, inv_mul_eq_one] using this j
        simp at this
        rw [this a (σ ⟦a⟧) (by rw [← Quotient.eq, hσ])]
        letI := Fintype.ofInjective ⇑φ inj
        suffices @Finset.card H {x | φ x * σ ⟦a⟧ = a} = 1 by simp [this]
        rw [Finset.card_eq_one]
        have := hσ ⟦a⟧
        rw [Quotient.eq] at this
        obtain ⟨⟨_, ⟨h, rfl⟩⟩, hhh⟩ := this
        use h⁻¹
        ext h'
        simp
        constructor
        · intro final
          simp [← hhh] at final
          change _ * (_ * _) = _ at final
          simp [← mul_assoc] at final
          rw [← φ.map_mul, ← φ.map_one] at final
          apply inj at final
          exact eq_inv_of_mul_eq_one_left final
        rintro rfl
        simp [← hhh]
        change _ * (_ * _) = _
        simp
      · intro b _ hab
        have : Fintype H := Fintype.ofInjective _ inj
        suffices Finset.card {x | φ x * σ b = a} = 0 by simp_all
        simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const]
        intro h eq
        apply_fun Quotient.mk (QuotientGroup.rightRel φ.range) at eq
        refine hab ?_
        nth_rw 1 [← hσ b]
        simp [← eq, QuotientGroup.rightRel_apply]
      · simp
    rw [this]
    apply sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨σ i, rfl⟩


lemma leftRegular.span_norm [Fintype G] : Submodule.span R {norm R G} = ⊤ := by
  rw [norm, ← Set.image_singleton, ← Submodule.map_span, leftRegular.span_norm']
  simp

lemma leftRegular.res_span_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) :
    letI : Fintype H := Fintype.ofInjective _ inj
    Submodule.span R (Set.range (res_norm R G φ inj)) = ⊤ := by

  sorry

def H0trivial : H0 (trivial R G R) ≅ ModuleCat.of R R :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| (Submodule.topEquiv.symm ≪≫ₗ LinearEquiv.ofEq _ _
  (by ext; simp) ≪≫ₗ (CategoryTheory.Iso.toLinearEquiv (H0Iso (trivial R G R))).symm)



@[elementwise]
lemma blah2 {ρ : Rep R G} (f : ρ ⟶ trivial R G R) :
    groupCohomology.map (.id _) f 0 ≫ (H0trivial R G).hom = zeroι _ ≫ f.hom := by
  ext x
  simp only [H0trivial, of_ρ, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.ofEq_symm,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply, Submodule.topEquiv_apply,
    LinearEquiv.coe_ofEq_apply]
  rw [ModuleCat.Iso_hom, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, map_id_comp_H0Iso_hom]
  simp [zeroι]

lemma leftRegular.groupCoh_map_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) :
    letI : Fintype H := Fintype.ofInjective _ inj
    groupCohomology.map (.id _) ((res φ).map (ε R G)) 0 (res_norm R G φ inj g) =
      (H0trivial R H).toLinearEquiv.symm (Fintype.card H : R) := by
  apply (H0trivial R H).toLinearEquiv.eq_symm_apply.mpr
  erw [blah2_apply]
  rw [leftRegular.zeroι_res_norm]
  simp [ε, leftRegular.of]

def H1_iso [Fintype G] :
    H1 (aug R G) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card G : R)}) :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| by
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact R G) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <| by
    simpa using by exact isZero_of_trivialCohomology)
  refine Submodule.Quotient.equiv _ _ (H0trivial R G).symm.toLinearEquiv ?_
  erw [← CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker <|
    (mapShortComplex₃_exact) (aug_isShortExact R G) (rfl : 0 + 1 = 1)]
  apply le_antisymm
  · simp only [Nat.card_eq_fintype_card, Nat.reduceAdd]
    intro (x : H0 _)
    simp only [Submodule.mem_map, Ideal.mem_span_singleton', exists_exists_eq_and,
      LinearMap.mem_range, forall_exists_index]
    rintro a rfl
    refine ⟨a • leftRegular.norm R G, ?_⟩
    apply (H0trivial R G).toLinearEquiv.injective
    erw [ModuleCat.Iso_symm_iso, LinearEquiv.apply_symm_apply, blah2_apply]
    simp only [map_smul, smul_eq_mul]
    rw [leftRegular.zeroι_norm, map_sum]
    conv => enter [1, 2, 2, x]; erw [ε_of]
    simp
  · erw [Submodule.map_equiv_eq_comap_symm]
    rw [LinearMap.range_eq_map, ← leftRegular.span_norm, Submodule.map_le_iff_le_comap,
      Submodule.span_le, Set.singleton_subset_iff]
    simp only [Nat.reduceAdd, ShortComplex.SnakeInput.L₁'_X₁,
      HomologicalComplex.HomologySequence.snakeInput_L₀, Functor.mapShortComplex_obj,
      ShortComplex.map_X₂, cochainsFunctor_obj, HomologicalComplex.homologyFunctor_obj,
      ShortComplex.SnakeInput.L₁'_X₂, ShortComplex.map_X₃, ShortComplex.SnakeInput.L₁'_f,
      ShortComplex.map_g, cochainsFunctor_map, HomologicalComplex.homologyFunctor_map,
      Nat.card_eq_fintype_card, Submodule.comap_coe, LinearEquiv.coe_coe, Set.mem_preimage,
      SetLike.mem_coe]
    erw [blah2_apply]
    erw [leftRegular.zeroι_norm]
    convert_to (hom (ε R G).hom) (∑ g, leftRegular.of g) ∈ Ideal.span {(Fintype.card G : R)}
    rw [map_sum]
    conv => enter [2, 2, x]; tactic => erw [ε_of]
    simpa [Ideal.mem_span_singleton'] using ⟨1, one_mul _⟩

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

def H1_iso' [Fintype G] {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) :
    H1 (aug R G ↓ φ) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card H : R)}) :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| by
  letI : Fintype H := Fintype.ofInjective (⇑φ) inj
  have : ShortComplex.Exact {
    X₁ := H0 (leftRegular R G ↓ φ)
    X₂ := H0 (trivial R H R)
    X₃ := H1 (aug R G ↓ φ)
    f := groupCohomology.map (.id _) ((res φ).map (ε R G)) 0
    g := groupCohomology.δ (aug_isShortExact' R G φ) 0 1 rfl
    zero := _
  } := mapShortComplex₃_exact (aug_isShortExact' R G φ) (rfl : 0 + 1 = 1)
  refine ?_ ≪≫ₗ LinearMap.quotKerEquivOfSurjective (δ (aug_isShortExact' R G φ) 0 1 rfl).hom
    (ModuleCat.epi_iff_surjective _|>.1 <| epi_δ_of_isZero _ 0 <| by
    simpa using @isZero_of_trivialCohomology R H _ _ _
      (Rep.trivialCohomology_iff_res.1 (trivialCohomology R G) φ inj) ..)
  refine Submodule.Quotient.equiv _ _ (H0trivial R H).symm.toLinearEquiv ?_
  erw [← CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker this]
  simp only [ShortComplex.map_X₃]
  rw [LinearMap.range_eq_map, ← leftRegular.res_span_norm R G φ inj, Submodule.map_span,
    ← Set.range_comp]
  erw [Submodule.map_span]
  congr 1
  ext
  simp
  conv => enter [2, 1, y]; erw [leftRegular.groupCoh_map_res_norm]
  simp [eq_comm]
  rfl

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

end Rep.aug

end AugmentationModule

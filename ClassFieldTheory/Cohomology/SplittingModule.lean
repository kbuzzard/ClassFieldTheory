import ClassFieldTheory.Cohomology.AugmentationModule
import ClassFieldTheory.Cohomology.TrivialCohomology
import ClassFieldTheory.Cohomology.TrivialityCriterion
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

open
  CategoryTheory
  ConcreteCategory
  Limits
  Rep
  groupCohomology
  BigOperators

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

noncomputable section Split
variable [Fintype G]
variable {M : Rep R G}

namespace Rep.split

set_option linter.unusedVariables false in
abbrev carrier (σ : H2 M) : Type := (aug R G) × M

variable (σ : H2 M)

omit [Fintype G] in
lemma H2π_surjective : (H2π M : cocycles₂ M → H2 M).Surjective := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

/--
`cocycle σ` is a 2-cocycle representing the cohomology class of `σ`.
-/
abbrev cocycle := (H2π_surjective σ).choose

omit [Fintype G] in
/--
`cocycle σ` is a 2-cocycle representing the cohomology class of `σ`.
-/
lemma cocycle_spec : H2π M (cocycle σ) = σ := (H2π_surjective σ).choose_spec

def representation : Representation R G (carrier σ) where
  toFun g := {
    toFun v := {
      fst := (aug R G).ρ g v.fst
      snd := M.ρ g v.snd + ∑ x : G, (aug.ι R G).hom.hom v.fst x • cocycle σ ⟨g, x⟩
    }
    map_add' x y := by
      ext
      · simp
      · simp [add_smul, Finset.sum_add_distrib, add_add_add_comm (M.ρ g x.2) (M.ρ g y.2)]
    map_smul' g v := by
      ext
      · simp
      · simp [mul_smul, Finset.smul_sum]
  }
  map_one' := by
    ext : 1
    · simp only [map_one, Module.End.one_apply, equalizer_as_kernel]
      ext v : 1
      rw [LinearMap.comp_apply]
      dsimp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Finsupp.coe_add, Pi.add_apply,
        Prod.mk_add_mk, Module.End.one_apply, AddHom.toFun_eq_coe, RingHom.id_apply, AddHom.coe_mk,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, Prod.smul_mk, LinearMap.coe_inl, LinearMap.coe_mk, LinearMap.coe_comp,
        Function.comp_apply]
      ext : 1
      · rfl
      · dsimp only
        rw [zero_add]
        simp only [cocycles₂_map_one_fst]
        rw [← Finset.sum_smul, aug.sum_coeff_ι, zero_smul]
    · ext v : 1
      simp
  map_mul' g₁ g₂ := by
    simp only [map_mul, Module.End.mul_apply]
    ext v
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
        Function.comp_apply, map_zero, zero_add, Module.End.mul_apply, map_sum, map_smul]
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
        Function.comp_apply, map_zero, zero_add, Module.End.mul_apply, map_sum, map_smul]
      have (a b c : _) :=
        eq_sub_iff_add_eq.mpr ((groupCohomology.mem_cocycles₂_iff _).mp (cocycle σ).2 a b c)
      simp only [cocycles₂.val_eq_coe] at this
      simp only [this, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [← Finset.sum_smul, Rep.aug.sum_coeff_ι, zero_smul, sub_zero, add_right_inj]
      conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft g₂)]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      erw [Rep.hom_comm_apply]
      simp [-equalizer_as_kernel] -- removes a `rfl` here shows I'm in the right direction
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inr,
        Function.comp_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero, Module.End.mul_apply]
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inr,
        Function.comp_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
        Finset.sum_const_zero, add_zero, Module.End.mul_apply]

def _root_.Rep.split : Rep R G := Rep.of (split.representation σ)

lemma apply (g : G) (vm : carrier σ) : (split σ).ρ g vm
    = ⟨(aug R G).ρ g vm.1, M.ρ g vm.2 + ∑ x : G, aug.ι R G vm.1 x • cocycle σ ⟨g, x⟩⟩ := rfl

lemma apply_fst (g : G) (vm : carrier σ) :
    ((split σ).ρ g vm).fst = (aug R G).ρ g vm.1 := rfl

lemma apply_snd (g : G) (vm : carrier σ) :
    ((split σ).ρ g vm).snd = M.ρ g vm.2 + ∑ x : G, aug.ι R G vm.1 x • cocycle σ ⟨g, x⟩ := rfl

@[ext] lemma ext (vm vm' : split σ) (hv : vm.1 = vm'.1) (hm : vm.2 = vm'.2) : vm = vm' := by
  change (⟨vm.1,vm.2⟩ : aug R G × M) = ⟨vm'.1,vm'.2⟩
  rw [hv,hm]

@[simp] lemma add_fst (vm vm' : split σ) : (vm + vm').1 = vm.1 + vm'.1 := rfl
@[simp] lemma add_snd (vm vm' : split σ) : (vm + vm').2 = vm.2 + vm'.2 := rfl
@[simp] lemma sub_fst (vm vm' : split σ) : (vm - vm').1 = vm.1 - vm'.1 := rfl
@[simp] lemma sub_snd (vm vm' : split σ) : (vm - vm').2 = vm.2 - vm'.2 := rfl


/--
The natural inclusion of a `G`-module `M` in the splitting module
of a 2-cocycle `σ : Z²(G,M)`.
-/
def ι : M ⟶ split σ := by
  apply ofHom
  exact {
    val := LinearMap.inr R (aug R G) M
    property g := by
      ext m : 1
      simp only [ρ_hom, Function.comp_apply]
      rw [apply]
      ext
      · change 0 = (aug R G).ρ g 0
        rw [map_zero]
      · change M.ρ g m = (M.ρ g) m + ∑ x : G, (aug.ι R G) 0 x • cocycle σ (g, x)
        rw [map_zero]
        simp
  }

lemma ι_apply (m : M) : ι σ m = ⟨0,m⟩ := rfl

/--
The projection from the splitting module of a 2-cocycle to `aug R G`.
-/
def π : split σ ⟶ aug R G :=
  ofHom
  { val := LinearMap.fst R (aug R G) M
    property _ := rfl }

def shortExactSequence : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := split σ
  X₃ := aug R G
  f := ι σ
  g := π σ
  zero := by ext; rfl

/--
The sequence

`  0 ⟶ M ⟶ split σ ⟶ aug R G ⟶ 1  `

is a short exact sequence in `Rep R G`.
-/
lemma isShortExact : ShortComplex.ShortExact (shortExactSequence σ) := by
  have : Mono (shortExactSequence σ).f := (Rep.mono_iff_injective _).mpr LinearMap.inr_injective
  have : Epi (shortExactSequence σ).g := (Rep.epi_iff_surjective _).mpr LinearMap.fst_surjective
  constructor
  apply Functor.reflects_exact_of_faithful (forget₂ _ (ModuleCat R))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Function.Exact.inr_fst

/--
The sequence

  0 ⟶ M ⟶ split σ ⟶ aug R G ⟶ 1

is a short exact sequence in `Rep R H` for every subgroup `H` of `G`.
-/
lemma res_isShortExact {H : Type} [Group H] (φ : H →* G) :
    ((shortExactSequence σ).map (res φ)).ShortExact := by
  rw [shortExact_res]
  exact isShortExact ..

/--
The function from the group `G` to the splitting module of a 2-cocycle `σ`,
which takes `g : G` to ([1]-[g], σ (g,1)).

The coboundary of this function is equal to the image of `σ` in H²(G,split).
-/
noncomputable def τ (g : G) : split σ :=
  ⟨aug.ofSubOfOne R G g, M.ρ g (cocycle σ (1,1))⟩

open leftRegular

/--
Given a 2-cocycle `σ`, the image of `σ` in the splitting module of `σ` is equal to the
coboundary of `τ σ`.
-/
lemma τ_property (g h : G) : (split σ).ρ g (τ σ h) - τ σ (g * h) + τ σ g = ι σ (cocycle σ (g,h))
    := by
  classical
  rw [τ, apply, τ, τ, ι_apply]
  ext
  · simp only [aug.ofSubOfOne_spec, Finsupp.coe_sub, Pi.sub_apply, add_fst, sub_fst]
    apply (Rep.mono_iff_injective _).mp (inferInstanceAs (Mono (aug.ι R G)))
    simp only [map_add, map_sub, map_zero]
    rw [Rep.hom_comm_apply]
    simp only [of_ρ]
    erw [Rep.aug.ofSubOfOne_spec, Rep.aug.ofSubOfOne_spec, Rep.aug.ofSubOfOne_spec]
    simp [of_def]
  · simp [leftRegular.of, Finsupp.single_apply, sub_smul]
    have : (cocycle σ) (g, 1) = (M.ρ g) ((cocycle σ) (1, 1)) := by
      simpa [add_comm] using (mem_cocycles₂_iff (cocycle σ)).mp (cocycle σ).2 g 1 1
    simp [this]
/--
Given a 2-cocycle `σ : Z²(G,M)`, the image of `σ` in `Z²(G,split σ)` is a coboundary.
-/
lemma splits : ι σ ∘ cocycle σ ∈ coboundaries₂ (split σ) := by
  use τ σ
  ext : 1
  rw [d₁₂_hom_apply, Function.comp_apply, τ_property]

/--
The restriction of the 2-cohomology class `σ : H²(G,M)` to a subgroup `H`.
-/
abbrev _root_.groupCohomology.H2res {H : Type} [Group H] (φ : H →* G) :
    H2 (M ↓ φ) :=
  map φ (𝟙 (M ↓ φ)) 2 σ

notation σ "↡" φ => H2res σ φ

/--
If `M` is an `R[G]`-module and `σ : H²(G,M)`, we say `σ` is a *finite class formation* if
for all subgroups `H` of `G`,
1) `H¹(H,M|H)=0`;
2) The `R`-module `H²(H,M|H)` is spanned as an `R`-module by `Res(σ)`;
3) The kernel of `R → H²(H,M|H)` is `|H|R`

In other words, for all subgroups H of G, H¹(H,M)=0 and H²(H,M)=R/|H|R
with the isomorphism given by sending 1 ∈ R/|H|R to σ.
-/
class FiniteClassFormation (σ : H2 M) where
  isZero_H1 {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) : IsZero (H1 (M ↓ φ))
  hypothesis₂ (σ) {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) :
    Submodule.span R {σ ↡ φ} = ⊤
  hypothesis₂' (σ) {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) :
    LinearMap.ker (LinearMap.toSpanSingleton R (H2 (M ↓ φ)) (σ ↡ φ)) = Ideal.span {(Nat.card H : R)}

def H2Map₂ {A B : Rep R G} (f : A ⟶ B) : H2 A ⟶ H2 B := map (MonoidHom.id G) f 2

omit [Fintype G] in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2Map₂_H2π {A B : Rep R G} (f : A ⟶ B) :
    H2π _ ≫ H2Map₂ f = mapCocycles₂ (.id _) f ≫ H2π _ := by
  simp [H2π, H2Map₂, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₂_hom_assoc]

variable {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ)

-- unif_hint (ρ : Rep R G) where ⊢ (ρ ↓ φ).V ≟ ρ.V
-- don't need this as well due to our change!

-- set_option pp.all true in
include inj in
/--
If `σ` generates `H²(G,M)` then the map `H²(G,M) ⟶ H²(G,split σ)` is zero.
-/
lemma TateTheorem_lemma_1 [FiniteClassFormation σ] : H2Map₂ ((res φ).map (ι σ)) = 0 := by
  suffices ⊤ ≤ LinearMap.ker (H2Map₂ ((res φ).map (ι σ))).hom by
    ext x; simpa using this Submodule.mem_top
  rw [← FiniteClassFormation.hypothesis₂ (σ := σ) inj, Submodule.span_le, Set.singleton_subset_iff]
  simp only [H2res, SetLike.mem_coe, LinearMap.mem_ker]
  conv_lhs => enter [2, 2]; rw [← Rep.split.cocycle_spec σ]
  simp only [H2π_comp_map_apply, H2Map₂_H2π_apply]
  suffices (H2π (split σ)).hom ((mapCocycles₂ (.id G) (ι σ)).hom (cocycle σ)) = 0 by
    trans (map φ (𝟙 (split σ ↓ φ)) 2).hom ((H2π (split σ)).hom
      ((mapCocycles₂ (.id G) (ι σ)).hom (cocycle σ)))
    · simp; rfl
    · simp only [this, map_zero]
  rw [H2π_eq_zero_iff]
  exact Rep.split.splits _

/--
Every surjective linear map from `R ⧸ I` to `R ⧸ I` is also injective.
-/
example (I : Ideal R) (f : R ⧸ I →ₗ[R] R ⧸ I) (surj : Function.Surjective f) :
    Function.Injective f :=
  OrzechProperty.injective_of_surjective_endomorphism f surj

include inj in
/--
For any subgroup H of `G`, the connecting hommorphism in the splitting module long exact sequence

    H¹(H,aug) ⟶ H²(H,M)

is an isomorphism.
-/
lemma TateTheorem_lemma_2 [FiniteClassFormation σ] [Finite H] :
    IsIso (δ (res_isShortExact σ φ) 1 2 rfl) := by
  cases nonempty_fintype H
  let e₁ : groupCohomology (aug R G ↓ φ) 1 ≅ .of R (R ⧸ Ideal.span {(Nat.card H : R)}) :=
    Rep.aug.H1_iso' R G inj
  let e₂' : (R ⧸ Ideal.span {(Nat.card H : R)}) ≃ₗ[R] groupCohomology (M ↓ φ) 2 :=
    .ofBijective (Submodule.liftQ _ (.toSpanSingleton _ _ (σ ↡ φ))
      (by rw [← FiniteClassFormation.hypothesis₂' σ inj])) <| by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, ← FiniteClassFormation.hypothesis₂' σ inj,
        Submodule.mkQ_map_self]
    · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_toSpanSingleton,
        FiniteClassFormation.hypothesis₂ σ inj]
  let e₂ : groupCohomology (M ↓ φ) 2 ≅ .of R (R ⧸ Ideal.span {(Nat.card H : R)}) :=
    e₂'.symm.toModuleIso
  apply (config := { allowSynthFailures := true }) @IsIso.of_isIso_comp_right (g := e₂.hom)
  apply (config := { allowSynthFailures := true }) IsIso.of_isIso_comp_left (f := e₁.inv)
  suffices Function.Surjective (e₁.inv ≫ δ (res_isShortExact σ φ) 1 2 rfl ≫ e₂.hom) by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨OrzechProperty.injective_of_surjective_endomorphism _ this, this⟩
  suffices Function.Surjective (δ (res_isShortExact σ φ) 1 2 rfl) from
    e₂.toLinearEquiv.surjective.comp (this.comp e₁.toLinearEquiv.symm.surjective)
  rw [← ModuleCat.epi_iff_surjective]
  let S := HomologicalComplex.HomologySequence.snakeInput
    (map_cochainsFunctor_shortExact <| res_isShortExact (R := R) σ φ) 1 2 rfl
  exact S.L₂'_exact.epi_f_iff.mpr (TateTheorem_lemma_1 _ inj)

include inj in
lemma TateTheorem_lemma_3 [FiniteClassFormation σ] [Finite H] : IsZero (H1 (split σ ↓ φ)) := by
  cases nonempty_fintype H
  let S := HomologicalComplex.HomologySequence.snakeInput
    (map_cochainsFunctor_shortExact <| res_isShortExact (R := R) σ φ) 1 2 rfl
  have := TateTheorem_lemma_2 σ inj
  have : Mono S.L₁'.f := S.L₀_exact.mono_g_iff.mpr
    (IsZero.eq_zero_of_src (FiniteClassFormation.isZero_H1 σ inj) _)
  apply Limits.IsZero.of_mono_eq_zero S.L₁'.f
  exact S.L₁'_exact.mono_g_iff.mp (inferInstanceAs (Mono (δ (res_isShortExact σ φ) 1 2 rfl)))

include inj in
lemma TateTheorem_lemma_4 [FiniteClassFormation σ] [IsAddTorsionFree R] :
    IsZero (H2 (split σ ↓ φ)) := by
  have H : IsZero (H2 (aug R G ↓ φ)) := by
    have := aug.cohomology_aug_succ_iso' R G inj 0
    refine .of_iso ?_ (asIso ((δ (aug.aug_isShortExact' R G φ) 1 2 rfl))).symm
    have : Finite H := .of_injective _ inj
    exact groupCohomology.H1_isZero_of_trivial (trivial R H R)
  let S := HomologicalComplex.HomologySequence.snakeInput
    (map_cochainsFunctor_shortExact <| res_isShortExact (R := R) σ φ) 1 2 rfl
  have : Epi S.L₃.f := S.L₃_exact.epi_f_iff.mpr (IsZero.eq_zero_of_tgt H _)
  exact Limits.IsZero.of_epi_eq_zero S.L₃.f (TateTheorem_lemma_1 _ inj)

/--
The splitting module has trivial cohomology.
-/
instance trivialCohomology [FiniteClassFormation σ] [IsAddTorsionFree R] :
    (split σ).TrivialCohomology := by
  apply trivialCohomology_of_even_of_odd (split σ) 0 0
  · intro H _ φ inj
    apply IsZero.of_iso (TateTheorem_lemma_4 σ inj)
    rfl
  · intro H _ φ inj
    let : Fintype H := Fintype.ofInjective φ inj
    apply IsZero.of_iso (TateTheorem_lemma_3 σ inj)
    rfl

lemma isIso_δ [FiniteClassFormation σ] [IsAddTorsionFree R] (n : ℤ) :
    IsIso (TateCohomology.δ (Rep.split.isShortExact σ) n) := by
  have : TrivialTateCohomology (split σ) := inferInstance
  exact TateCohomology.isIso_δ _ this _

def tateCohomologyIso [FiniteClassFormation σ] [IsAddTorsionFree R] (n : ℤ) :
    (tateCohomology n).obj (trivial R G R) ≅ (tateCohomology (n + 2)).obj M :=
  -- first go from H^n(trivial) to H^{n+1}(aug)
  have first_iso := Rep.aug.tateCohomology_auc_succ_iso R G n
  -- now go from H^{n+1}(aug) to H^{n+2}(M)
  have second_iso := Rep.split.isIso_δ σ (n + 1)
  -- map starts here
  (CategoryTheory.asIso (TateCohomology.δ (aug.aug_isShortExact R G) n)) ≪≫
  (CategoryTheory.asIso (TateCohomology.δ (Rep.split.isShortExact σ) (n + 1))) ≪≫
  eqToIso (by
    congr 2;
    ring)

def reciprocityIso (N : Rep ℤ G) (τ : H2 N) [FiniteClassFormation τ] :
    (tateCohomology 0).obj N ≅ .of ℤ (Additive (Abelianization G)) := calc
  (tateCohomology 0).obj N
    ≅ (tateCohomology (-2 + 2)).obj N := .refl _
  _ ≅ (tateCohomology (-2)).obj (trivial ℤ G ℤ) := (tateCohomologyIso τ (-2)).symm
  _ ≅ groupHomology (trivial ℤ G ℤ) 1 := (TateCohomology.isoGroupHomology _ 1 rfl).app _
  _ ≅ .of ℤ (Additive (Abelianization G)) :=
    groupHomology.H1TrivialAddEquiv.toIntLinearEquiv.toModuleIso

end Rep.split

end Split

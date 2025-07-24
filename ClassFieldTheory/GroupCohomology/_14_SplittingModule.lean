import Mathlib
import ClassFieldTheory.GroupCohomology._5_TrivialCohomology
import ClassFieldTheory.GroupCohomology._11_TrivialityCriterion
import ClassFieldTheory.GroupCohomology._12_augmentationModule

open
  CategoryTheory
  ConcreteCategory
  Limits
  Rep
  groupCohomology
  BigOperators

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]

noncomputable section Split
variable [Fintype G]
variable {M : Rep R G}

namespace Rep.split

set_option linter.unusedVariables false in
abbrev carrier (σ : H2 M) : Type := (aug R G) × M

variable (σ : H2 M)

lemma H2π_surjective : (H2π M : cocycles₂ M → H2 M).Surjective := by
  sorry

/--
`cocycle σ` is a 2-cocycle representing the cohomology class of `σ`.
-/
abbrev cocycle := (H2π_surjective σ).choose

/--
`cocycle σ` is a 2-cocycle representing the cohomology class of `σ`.
-/
lemma cocycle_spec : H2π M (cocycle σ) = σ := (H2π_surjective σ).choose_spec

def representation : Representation R G (carrier σ) where
  toFun g := {
    toFun v := {
      fst := (aug R G).ρ g v.fst
      snd := M.ρ g v.snd + ∑ x : G, aug.ι R G v.fst x • cocycle σ ⟨g, x⟩
    }
    map_add' := sorry
    map_smul' := sorry
  }
  map_one' := by
    ext : 1
    · simp
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
        rw [←Finset.sum_smul, aug.sum_coeff_ι, zero_smul]
    · ext v : 1
      simp
  map_mul' g₁ g₂ := by
    simp only [map_mul, Module.End.mul_apply, equalizer_as_kernel]
    ext v
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
      Function.comp_apply, map_zero, zero_add, Module.End.mul_apply, map_sum, map_smul]
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
      Function.comp_apply, map_zero, zero_add, Module.End.mul_apply, map_sum, map_smul]
      sorry
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

@[ext] lemma ext (vm vm' : split σ) (hv : vm.1 =vm'.1) (hm : vm.2 = vm'.2) : vm = vm' := by
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
def π : split σ ⟶ aug R G := by
  apply ofHom
  exact {
    val := LinearMap.fst R (aug R G) M
    property := sorry
  }

def shortExactSequence : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := split σ
  X₃ := aug R G
  f := ι σ
  g := π σ
  zero := sorry

/--
The sequence

`  0 ⟶ M ⟶ split σ ⟶ aug R G ⟶ 1  `

is a short exact sequence in `Rep R G`.
-/
lemma isShortExact : ShortComplex.ShortExact (shortExactSequence σ) := sorry

/--
The sequence

  0 ⟶ M ⟶ split σ ⟶ aug R G ⟶ 1

is a short exact sequence in `Rep R H` for every subgroup `H` of `G`.
-/
lemma res_isShortExact {H : Type} [Group H] (φ : H →* G) :
    ((shortExactSequence σ).map (res φ)).ShortExact := by
  /-
  This follows from `isShortExact` and `res_respectsShortExact`
  -/
  sorry

/--
The function from the group `G` to the splitting module of a 2-cocycle `σ`,
which takes `g : G` to ([1]-[g], σ (g,1)).

The coboundary of this function is equal to the image of `σ` in H²(G,split).
-/
noncomputable def τ (g : G) : split σ :=
  ⟨aug.ofSubOfOne R G g, M.ρ g (cocycle σ (1,1))⟩

open leftRegular Classical

/--
Given a 2-cocycle `σ`, the image of `σ` in the splitting module of `σ` is equal to the
coboundary of `τ σ`.
-/
lemma τ_property (g h : G) : (split σ).ρ g (τ σ h) - τ σ (g * h) + τ σ g  = ι σ (cocycle σ (g,h))
    := by
  rw [τ, apply, τ, τ, ι_apply]
  ext
  · simp only [aug.ofSubOfOne_spec, Finsupp.coe_sub, Pi.sub_apply, add_fst, sub_fst]
    sorry
  · simp [leftRegular.of, Finsupp.single_apply, sub_smul]
    sorry

/--
Given a 2-cocycle `σ : Z²(G,M)`, the image of `σ` in `Z²(G,split σ)` is a coboundary.
-/
lemma splits : ι σ ∘ cocycle σ ∈ coboundaries₂ (split σ) := by
  use τ σ
  ext : 1
  rw [d₁₂_hom_apply, Function.comp_apply, τ_property]

/--
The restriction of `σ` to a subgroup `H`.
-/
abbrev _root_.groupCohomology.H2res {H : Type} [Group H] (φ : H →* G) :
    H2 (M ↓ φ) :=
  map φ (𝟙 (M ↓ φ)) 2 σ

notation σ "↡" φ => H2res σ φ

/--
Given an element `σ : H²(G,M)`, the
-/
class FiniteClassFormation where
  hypothesis₁ {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) : IsZero (H1 (M ↓ φ))
  hypothesis₂ {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) :
    Submodule.span R {σ ↡ φ} = ⊤
  hypothesis₂' {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ) :
    (Submodule.span R {σ ↡ φ}).annihilator = Ideal.span {(Nat.card H : R)}

def H2Map₂ {A B : Rep R G} (f : A ⟶ B) : H2 A ⟶ H2 B := map (MonoidHom.id G) f 2

variable {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ)

include inj in
/--
If `σ` generates `H²(G,M)` then the map `H²(G,M) ⟶ H²(G,split σ)` is zero.
-/
lemma TateTheorem_lemma_1 [FiniteClassFormation σ] : H2Map₂ ((res φ).map (ι σ)) = 0 :=
  /-
  every element is a multiple of `σ`, and we have proved in `splits` that the image of `σ` is a
  coboundary.
  -/
  sorry

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
lemma TateTheorem_lemma_2 [FiniteClassFormation σ] :
    IsIso (δ (res_isShortExact σ φ) 1 2 rfl) :=
  /-
  We have a long exact sequence containing the section

      H¹(H,aug) ⟶ H²(H,M) ⟶ H²(H,split).

  We proved in `TateTheorem_lemma_1` that the second map is zero, so the connecting homomorphism
  is surjective.
  We are assuming that H²(G,M) ≅ R/|G|, and we have proved above that H¹(G,aug R G) ≅ R/|G|.
  We can therefore use `helper` to prove that the connecting homomorphism is also injective.
  -/
  sorry

include inj in
lemma TateTheorem_lemma_3 [FiniteClassFormation σ] :
    IsZero (H1 (split σ ↓ φ)) :=
  /-
  We therefore have a long exact sequence containing the section

    0 ⟶ H¹(H,split) ⟶ H¹(H,aug) ⟶ H²(H,M).

  the second map above is an isomorphism by `TateTheorem_lemma_2`.
  -/
  sorry

include inj in
lemma TateTheorem_lemma_4 [FiniteClassFormation σ] [NoZeroSMulDivisors ℕ R] :
    IsZero (H2 (split σ ↓ φ)) :=
  /-
  By assumption, `R` has no elements of finite additive order,
  so we have H²(G,aug) ≅ H¹(G,R) ≅ Hom(G,R) ≅ 0. This uses `groupCohomology.H1_isZero_of_trivial`

  We therefore have a long exact sequence containing

    `H²(G,M) ⟶ H²(G,split σ) ⟶ 0.`

  We have shown in `TateTheorem_lemma_1` that the map above is zero.
  -/
  sorry

/--
The splitting module is has trivial cohomology.
-/
lemma trivialCohomology [FiniteClassFormation σ] [NoZeroSMulDivisors ℕ R] :
    (split σ).TrivialCohomology := by
  apply trivialCohomology_of_even_of_odd (split σ) 0 0
  · intro H _ φ inj _
    apply IsZero.of_iso (TateTheorem_lemma_4 σ inj)
    rfl
  · intro H _ φ inj _
    apply IsZero.of_iso (TateTheorem_lemma_3 σ inj)
    rfl


def tateCohomology_iso [FiniteClassFormation σ] [NoZeroSMulDivisors ℕ R] (n : ℤ) :
  (tateCohomology n).obj (trivial R G R) ≅ (tateCohomology (n + 2)).obj M := sorry

def reciprocity_iso (N : Rep ℤ G) (τ : H2 N) [FiniteClassFormation τ] :
    (tateCohomology 0).obj N ≅ ModuleCat.of ℤ (Additive (Abelianization G)) := by
  symm
  apply Iso.trans (Y := (tateCohomology (-2)).obj (trivial ℤ G ℤ))
  · sorry -- current PR.
  · apply tateCohomology_iso τ

end Rep.split

end Split

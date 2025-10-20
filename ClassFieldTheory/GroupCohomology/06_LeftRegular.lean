import Mathlib
import ClassFieldTheory.GroupCohomology.«05_TrivialCohomology»
import ClassFieldTheory.Mathlib.RepresentationTheory.Invariants
import ClassFieldTheory.Mathlib.Algebra.Category.ModuleCat.Basic

section Group

variable {R G : Type} [Group G] [CommRing R]

open
  Classical
  Finsupp
  CategoryTheory
  ConcreteCategory
open Rep hiding of
open scoped CategoryTheory BigOperators

/-
# helper lemmas concerning the object `leftRegular R G` of `Rep R G`.
-/
namespace Rep.leftRegular

/--
`Rep.leftRegular.of g` is the group element `g : G` regarded as
as element of `Rep.leftRegular ℤ G`. Its type is `CoeSort.coe (Rep.leftRegular ℤ G)`.
-/
noncomputable def of (g : G) : leftRegular R G := single g 1

lemma of_def (g : G) : @of R G _ _ g = single g 1 := rfl

lemma of_apply (g h : G) : (of g) h = if (g = h) then (1 : R) else (0 : R) :=
  Finsupp.single_apply

lemma of_apply_eq_one (g : G) : (of g) g = (1 : R) := by
  rw [of_apply, if_pos rfl]

lemma eq_sum_smul_of (v : leftRegular R G) : v = ∑ x ∈ v.support, (v x) • (of x) := by
  change v = v.sum (fun x s ↦ s • of x)
  simp [of_def]

lemma ρ_apply (g : G) : (leftRegular R G).ρ g = lmapDomain R R (g * ·) := rfl

lemma ρ_apply₃_self_mul (g : G) (v : leftRegular R G) (x : G) :
    ((leftRegular R G).ρ g v) (g * x) = v x := by
  rw [ρ_apply, lmapDomain_apply]
  have : Function.Injective (g * ·)
  · intro x y hxy
    dsimp at hxy
    simpa using hxy
  exact mapDomain_apply this v x

lemma ρ_apply₃ (g : G) (v : leftRegular R G) (x : G) :
    ((leftRegular R G).ρ g v) x = v (g⁻¹ * x) := by
  convert ρ_apply₃_self_mul g v (g⁻¹ * x)
  rw [←mul_assoc, mul_inv_cancel, one_mul]

lemma ρ_apply_of (g x : G) : (leftRegular R G).ρ g (of x) = of (g * x) := by
  ext
  rw [ρ_apply₃, of_apply, of_apply, eq_inv_mul_iff_mul_eq]

lemma ρ_comp_lsingle (g x : G) : (leftRegular R G).ρ g ∘ₗ lsingle x = lsingle (g * x) := by
  ext; simp

lemma of_eq_ρ_of_one (g : G) : of g = (leftRegular R G).ρ g (of 1) := by
  rw [ρ_apply_of, mul_one]

lemma leftRegularHom_of {A : Rep R G} (v : A) (g : G) :
    (A.leftRegularHom v) (of g) = A.ρ g v :=
  leftRegularHom_hom_single g v 1 |>.trans <| one_smul _ _

/--
If `g` is in the centre of `G` then the unique morphism of the
left regular representation which takes `1` to `g` is (as a linear map) `(leftRegular R G).ρ g`.
-/
lemma leftRegularHom_eq_ρReg (g : G) (hg : g ∈ Subgroup.center G) :
    hom ((leftRegular R G).leftRegularHom (of g)).hom = (leftRegular R G).ρ g := by
  ext
  simp only [of_def, leftRegularHom_hom, of_ρ, Representation.ofMulAction_single, smul_eq_mul,
    ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, lsingle_apply, lift_apply,
    smul_single, mul_one, single_zero, sum_single_index]
  rw [hg.comm]


variable (R G)
/--The augmentation map from the left regular representation to the trivial module.-/
noncomputable
def ε : leftRegular R G ⟶ trivial R G R := leftRegularHom (trivial R G R) (1 : R)

variable {R G}
lemma ε_of_one : (ε R G) (of 1) = (1 : R) :=
  leftRegularHom_of 1 1

lemma ε_comp_ρ (g : G) : ModuleCat.ofHom ((leftRegular R G).ρ g) ≫ (ε R G).hom = (ε R G).hom :=
  (ε R G).comm g

lemma ε_comp_ρ_apply (g : G) (v : (leftRegular R G).V) :
  (ε R G) ((leftRegular R G).ρ g v) = (ε R G) v := by
  change ((ModuleCat.ofHom _) ≫ (ε R G).hom).hom v = _
  rw [ε_comp_ρ]
  rfl

@[simp]
lemma ε_of (g : G) : ε R G (of g) = (1 : R) := by
  have : of g = (leftRegular R G).ρ g (of 1)
  · rw [ρ_apply_of, mul_one]
  rw [this, ε_comp_ρ_apply, ε_of_one]

instance : AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
    (leftRegular R G) (trivial R G R) where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

instance : MulActionHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
    R (leftRegular R G) (trivial R G R) where
  map_smulₛₗ f := map_smul f.val

lemma ε_eq_sum' (v : leftRegular R G) : ε R G v = ∑ x ∈ v.support, v x := by
  nth_rw 1 [eq_sum_smul_of v, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_smul, ε_of, smul_eq_mul, mul_one]

lemma ε_eq_sum (v : leftRegular R G) [Fintype G] :
    ε R G v = ∑ g : G, v g := ε_eq_sum' v|>.trans <|
  (finsum_eq_sum_of_support_subset v (by simp)).symm.trans <| by
  simp [finsum_eq_sum_of_fintype]

/--
The left regular representation is nontrivial (i.e. non-zero) if and only if the coefficient
ring is trivial.
-/
lemma nontrivial_iff_nontrivial : Nontrivial (leftRegular R G) ↔ Nontrivial R :=
by
  simp only [nontrivial_iff]
  constructor
  · intro h
    contrapose! h
    intro v w
    ext
    apply h
  · intro ⟨x,y,hxy⟩
    use x • (of 1), y • (of 1)
    contrapose! hxy
    apply_fun fun v ↦ (v 1) at hxy
    simpa [of_def] using hxy

lemma ε_epi : Epi (ε R G) := CategoryTheory.ConcreteCategory.epi_of_surjective _ <| fun r ↦
  ⟨r • of 1, by erw [map_smul, ε_of_one, smul_eq_mul, mul_one]⟩

noncomputable section

variable (R G)

abbrev norm' [Fintype G] : (leftRegular R G).ρ.invariants :=
  ⟨∑ g : G, leftRegular.of g, fun g ↦ by
    simpa [leftRegular.of] using show ∑ x : G, leftRegular.of (g * x) = _ from
    Finset.sum_equiv (Equiv.mulLeft g) (by grind) <| fun _ _ ↦ rfl⟩

def norm [Fintype G] : groupCohomology.H0 (leftRegular R G) :=
  (groupCohomology.H0Iso (leftRegular R G)).toLinearEquiv.symm (norm' R G)

abbrev res_norm' [Fintype G] {H : Type} [Group H] (g : G) (φ : H →* G)
    (inj : φ.toFun.Injective) : (leftRegular R G ↓ φ).ρ.invariants :=
  letI : Fintype H := Fintype.ofInjective _ inj
  ⟨∑ h : H, leftRegular.of (φ h * g), fun h ↦ by
    simpa [leftRegular.of] using show ∑ x : H, leftRegular.of _ = _ by
      simpa [← mul_assoc, ← leftRegular.of_def] using Finset.sum_equiv (Equiv.mulLeft h) (by grind)
        (by simp)⟩

def res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G) (inj : φ.toFun.Injective) (g : G) :
    groupCohomology.H0 ((leftRegular R G) ↓ φ) :=
  (groupCohomology.H0Iso ((leftRegular R G) ↓ φ)).toLinearEquiv.symm <|
  leftRegular.res_norm' R G g φ inj

open RepresentationTheory.groupCohomology

lemma zeroι_norm [Fintype G] :
    zeroι _ (leftRegular.norm R G) = ∑ g : G, leftRegular.of g := by
  have := (groupCohomology.H0Iso (leftRegular R G)).toLinearEquiv.apply_symm_apply
    ⟨∑ g : G, MonoidAlgebra.of _ _ g,
    fun g ↦ by simpa using show ∑ x : G, MonoidAlgebra.of _ _ (g * x) = _ from
      Finset.sum_equiv (Equiv.mulLeft g) (by grind) <| fun _ _ ↦ rfl⟩
  exact congr($this)

lemma H0Iso_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) : (groupCohomology.H0Iso ((leftRegular R G) ↓ φ)).hom
    (res_norm R G φ inj g) = res_norm' R G g φ inj :=
  (groupCohomology.H0Iso _).toLinearEquiv.apply_symm_apply _

lemma zeroι_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) :
    letI : Fintype H := Fintype.ofInjective _ inj
    zeroι _ (res_norm R G φ inj g) = ∑ h : H, leftRegular.of (φ h * g) := by
  letI : Fintype H := Fintype.ofInjective _ inj
  dsimp [zeroι]
  erw [leftRegular.H0Iso_res_norm] -- `erw?` does nothing

lemma span_norm' [Fintype G] :
    Submodule.span R {norm' R G} = ⊤ := by
  ext ⟨x, hx⟩
  simp only [of_ρ, Submodule.mem_span_singleton, Subtype.ext_iff, SetLike.val_smul,
    Submodule.mem_top, iff_true]
  replace hx : ∃ a : R, ∀ g : G, x g = a := ⟨x 1, fun g ↦ by
    simpa using Finsupp.ext_iff.1 (hx g⁻¹) 1⟩
  exact ⟨hx.choose, Finsupp.ext_iff.2 fun g ↦ by simp [← hx.choose_spec g, leftRegular.of]⟩

lemma res_span_norm' [Fintype G] {H : Type} [Group H] (φ : H →* G) (inj : φ.toFun.Injective) :
    Submodule.span R {res_norm' R G g φ inj | g : G} = ⊤ := by
  ext x
  simp only [Action.res_obj_V, res_obj_ρ, of_ρ, Submodule.mem_top, iff_true]
  choose σ hσ using Quotient.mk_surjective (s := QuotientGroup.rightRel φ.range)
  classical
  letI := Fintype.ofInjective ⇑φ inj
  have : x = ∑ i, (show G →₀ _ from x.1) (σ i) • res_norm' R G (σ i) φ inj := by
    ext;
    simp only [Action.res_obj_V, res_obj_ρ, of_ρ, AddSubmonoidClass.coe_finset_sum,
      Submodule.coe_smul_of_tower, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Finsupp.ext_iff,
      coe_finset_sum, coe_smul, Finset.sum_apply, Pi.smul_apply, leftRegular.of_apply (R := R),
      Finset.sum_boole, smul_eq_mul]
    intro a
    rw [Finset.sum_eq_single (Quotient.mk _ a)]
    · have (i j : G) : QuotientGroup.rightRel φ.range i j → (show G →₀ R from x.1) i =
        (show G →₀ R from x.1) j := fun hij ↦ by
        obtain ⟨x, hx⟩ := x
        obtain ⟨k, hk⟩ := by simpa [QuotientGroup.rightRel_apply] using hij
        have := by simpa [Representation.ofMulAction_def, Finsupp.ext_iff] using hx k
        simpa [mapDomain, Finsupp.sum_fintype, Finsupp.single_apply, hk, mul_assoc,
          inv_mul_eq_one] using this j
      simp only [Action.res_obj_V, res_obj_ρ, of_ρ] at this
      rw [this a (σ ⟦a⟧) (by rw [← Quotient.eq, hσ])]
      suffices @Finset.card H {x | φ x * σ ⟦a⟧ = a} = 1 by simp [this]
      rw [Finset.card_eq_one]
      obtain ⟨⟨_, ⟨h, rfl⟩⟩, hhh⟩ := Quotient.eq.1 <| hσ ⟦a⟧
      use h⁻¹
      ext h'
      simp
      constructor
      · intro final
        simp only [← hhh] at final
        change _ * (_ * _) = _ at final
        simp only [← mul_assoc, mul_eq_right] at final
        rw [← φ.map_mul, ← φ.map_one] at final
        apply inj at final
        exact eq_inv_of_mul_eq_one_left final
      rintro rfl
      exact hhh.symm ▸ show _ * (_ * _) = _ by simp
    · intro b _ hab
      suffices Finset.card {x | φ x * σ b = a} = 0 by simp_all
      simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const]
      intro h eq
      apply_fun Quotient.mk (QuotientGroup.rightRel φ.range) at eq
      exact hab <| by nth_rw 1 [← hσ b]; simp [← eq, QuotientGroup.rightRel_apply]
    · simp
  exact this ▸ sum_mem fun i _ ↦ Submodule.smul_mem _ _ <| Submodule.subset_span ⟨σ i, rfl⟩

lemma span_norm [Fintype G] : Submodule.span R {leftRegular.norm R G} = ⊤ := by
  rw [leftRegular.norm, ← Set.image_singleton, ← Submodule.map_span, leftRegular.span_norm']
  simp

lemma res_span_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) :
    letI : Fintype H := Fintype.ofInjective _ inj
    Submodule.span R (Set.range (res_norm R G φ inj)) = ⊤ := by
  erw [Set.range_comp]
  rw [← Submodule.map_span]
  erw [leftRegular.res_span_norm']
  simp

def _root_.groupCohomology.H0trivial : groupCohomology.H0 (trivial R G R) ≅ ModuleCat.of R R :=
  LinearEquiv.toModuleIso <| LinearEquiv.symm <| Submodule.topEquiv.symm ≪≫ₗ LinearEquiv.ofEq _ _
  (by ext; simp) ≪≫ₗ (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (trivial R G R))).symm

@[elementwise]
lemma _root_.groupCohomology.map_comp_H0trivial {ρ : Rep R G} (f : ρ ⟶ trivial R G R) :
    groupCohomology.map (.id _) f 0 ≫ (groupCohomology.H0trivial R G).hom = zeroι _ ≫ f.hom := by
  ext x
  simp only [groupCohomology.H0trivial, of_ρ, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.ofEq_symm,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply, Submodule.topEquiv_apply,
    LinearEquiv.coe_ofEq_apply]
  rw [ModuleCat.Iso_hom, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    groupCohomology.map_id_comp_H0Iso_hom]
  simp [zeroι]

lemma groupCoh_map_res_norm [Fintype G] {H : Type} [Group H] (φ : H →* G)
    (inj : φ.toFun.Injective) (g : G) :
    letI : Fintype H := Fintype.ofInjective _ inj
    groupCohomology.map (.id _) ((res φ).map (ε R G)) 0 (res_norm R G φ inj g) =
      (groupCohomology.H0trivial R H).toLinearEquiv.symm (Fintype.card H : R) := by
  apply (groupCohomology.H0trivial R H).toLinearEquiv.eq_symm_apply.mpr
  erw [groupCohomology.map_comp_H0trivial_apply]
  rw [leftRegular.zeroι_res_norm]
  simp [ε, leftRegular.of]

end

end Rep.leftRegular

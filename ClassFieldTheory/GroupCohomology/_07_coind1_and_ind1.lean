import Mathlib
import ClassFieldTheory.GroupCohomology._03_inflation
import ClassFieldTheory.GroupCohomology._05_TrivialCohomology
import ClassFieldTheory.Mathlib.Algebra.Algebra.Equiv
import ClassFieldTheory.Mathlib.FieldTheory.Galois.NormalBasis

/-!
Let `G` be a group. We define two functors:

  `Rep.coind₁ G : ModuleCat R ⥤ Rep R G` and
  `Rep.ind₁ G   : ModuleCat R ⥤ Rep R G`.

For an `R`-module `A`, the representation `(coind₁ G).obj A` is the space of functions `f : G → A`,
with the action of `G` by right-translation. In other words `(g f) x = f (x g)` for `g : G`.

The space `(ind₁ G).obj A` is `G →₀ A` with the action of `G` by right-translation, i.e.
`g (single x v) = single (x * g⁻¹) v`.

Both `ind₁` and `coind₁` are defined as special cases of the functors `ind` and `coind` in Matlib.

We prove that `coind₁.obj A` has trivial cohomology and `ind₁.obj X` is has trivial homology.

We also define two functors

  `coind₁' : Rep R G ⥤ Rep R G` and
  `ind₁' : Rep R G ⥤ Rep R G`.

For a representation `M` of `G`, the representation `coind₁'.obj M` is the representation of `G`
on `G → M.V`, where the action of `G` is by `M.ρ` on `M.V` and by right-translation on `G`.

`ind₁'.obj M` is the representation of `G` on `G →₀ M.V`, where the action of `G` is by `M.ρ` on
`M.V` and by right-translation on `G`.

We define the canonical monomorphism `coind₁'_ι : M ⟶ coind₁'.obj M` which takes a vector `v` to
the constant function on `G` with value `v`.

We define the canonical epimorphism `ind₁'_π : ind₁'.obj M ⟶ M` which takes a finitely supported
function to the sum of its values.

We prove that `ind₁'.obj M` is isomorphic to `(ind₁ G).obj M.V`, and therefore has trivial homology.
Similarly we show that `coind₁'.obj M` is isomorphic to `(coind₁ G).obj M.V` and therefore has
trivial cohomology. In the case that `G` is a finite group, we show that all four of these
repressentations have trivial Tate cohomology.

## Implementation notes

`ind₁`/`coind₁` are defined as the base change of finsupp/pi quotiented out by the trivial
relation.
This is because they are abbrevs of the general construction from mathlib.

Instead of redefining them as `G →₀ A`/`G → A` with the `G`-action on the domain, which would break
the defeq with the general construction, we provide `ind₁AsFinsupp`/`coind₁AsPi`, a version of
`ind₁`/`coind₁` that's actually defined as `G →₀ A`/`G → A`.

`ind₁AsFinsupp`/`coind₁AsPi` are not bundled as functors because they should only be used for
pointwise computations.
-/

open
  Finsupp
  Representation
  Rep
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable (R G : Type) [CommRing R] [Group G]

namespace Representation

variable (V W : Type) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

abbrev coind₁V := coindV (⊥ : Subgroup G).subtype (trivial R _ V)

instance : FunLike (coind₁V R G V) G V where
  coe f := f.val
  coe_injective' := Subtype.val_injective

instance : Coe (G → V) (coind₁V R G V) where
  coe f := ⟨f,by
    intro ⟨g, hg⟩ x
    rw [Subgroup.mem_bot] at hg
    simp [hg]
  ⟩

/--
The representation of `G` on the space `G → V` by right-translation on `G`.
(`V` is an `R`-module with no action of `G`).
-/
abbrev coind₁ := coind (⊥ : Subgroup G).subtype (trivial R _ V)

@[simp] lemma coind₁_apply₃ (f : coind₁V R G V) (g x : G) : coind₁ R G V g f x = f (x * g) := rfl

abbrev Ind₁V := IndV (⊥ : Subgroup G).subtype (trivial R _ V)
abbrev Ind₁V.mk := IndV.mk (⊥ : Subgroup G).subtype (trivial R _ V)
/--
The induced representation of a group `G` on `G →₀ V`, where the action of `G` is by
left-translation on `G`; no action of `G` on `V` is assumed.
-/
abbrev ind₁ := ind (⊥ : Subgroup G).subtype (trivial R _ V)

lemma ind₁_apply (g x : G) : (ind₁ R G V) g ∘ₗ Ind₁V.mk R G V x = Ind₁V.mk R G V (x * g⁻¹) := by
  ext; simp

variable {R G V} (ρ : Representation R G V)

/--
Given a representation `ρ` of `G` on `V`, `coind₁' ρ` is the representation of `G`
on `G → V`, where the action of `G` is `(g f) x = ρ g (f (x * g))`.
-/
@[simps] def coind₁' : Representation R G (G → V) where
  toFun g := {
    toFun f x := ρ g (f (x * g))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
  }
  map_one' := by ext; simp
  map_mul' g₁ g₂ := by ext; simp [mul_assoc]

@[simp] lemma coind₁'_apply₃ (g x : G) (f : G → V) : coind₁' ρ g f x = ρ g (f (x * g)) := rfl

/--
The linear bijection from `G → V` to `G → V`, which gives intertwines the
representations `coind₁' ρ` and `coind₁ R G V`.
-/
@[simps] def coind₁'_lequiv_coind₁ : (G → V) ≃ₗ[R] coind₁V R G V where
  toFun f       := fun x ↦ ρ x (f x)
  map_add' _ _  := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun f x    := ρ x⁻¹ (f x)
  left_inv f    := by ext; apply inv_self_apply
  right_inv _   := by ext; simp; rfl

lemma coind₁'_lequiv_coind₁_comm (g : G) :
    coind₁'_lequiv_coind₁ ρ ∘ₗ coind₁' ρ g = coind₁ R G V g ∘ₗ coind₁'_lequiv_coind₁ ρ := by
  ext; simp

/--
The linear map from `V` to `G → V` taking a vector `v : V` to the comstant function
with value `V`. If `ρ` is a representation of `G` on `V`, then this map intertwines
`ρ` and `ρ.coind₁'`.
-/
@[simps] def coind₁'_ι : V →ₗ[R] (G → V) where
  toFun     := Function.const G
  map_add'  := by simp
  map_smul' := by simp

/--
The map `coind₁'_ι` intertwines a representation `ρ` of `G` on `V` with the
representation `ρ.coind₁'` of `G` on `G → V`.
-/
lemma coind₁'_ι_comm (g : G) : coind₁' ρ g ∘ₗ coind₁'_ι = coind₁'_ι ∘ₗ ρ g := by ext; simp

variable {W X : Type} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]

/--
`ind₁' ρ` is the representation of `G` on `G →₀ V`, where the action is defined by
`ρ.ind₁' g f x = ρ g (f (x * g))`.
-/
@[simps] def ind₁' : Representation R G (G →₀ V) where
  toFun g := lmapDomain _ _ (fun x ↦ x * g⁻¹) ∘ₗ mapRange.linearMap (ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

lemma ind₁'_apply₂ (f : G →₀ V) (g x : G) : ρ.ind₁' g f x = ρ g (f (x * g)) := by
  dsimp only [ind₁'_apply, LinearMap.coe_comp, Function.comp_apply, mapRange.linearMap_apply,
    lmapDomain_apply]
  have : x = x * g * g⁻¹ := eq_mul_inv_of_mul_eq rfl
  rw [this, mapDomain_apply (mul_left_injective g⁻¹)]
  simp

private abbrev ind₁'_map (f : V →ₗ[R] W) : (G →₀ V) →ₗ[R] (G →₀ W) := mapRange.linearMap f

omit [Group G] in
private lemma ind₁'_map_comp_lsingle (f : V →ₗ[R] W) (x : G) :
    (ind₁'_map f) ∘ₗ (lsingle x) = (lsingle x) ∘ₗ f  := by
  ext; simp

@[simp] lemma ind₁'_comp_lsingle (g x : G) : ρ.ind₁' g ∘ₗ lsingle x = lsingle (x * g⁻¹) ∘ₗ ρ g := by
  ext; simp

lemma ind₁'_map_comm {ρ' : Representation R G W} {f : V →ₗ[R] W}
    (hf : ∀ g : G, f ∘ₗ ρ g = ρ' g ∘ₗ f) (g : G) :
    ind₁'_map f ∘ₗ ρ.ind₁' g = ρ'.ind₁' g ∘ₗ ind₁'_map f := by
  ext : 1
  rw [LinearMap.comp_assoc, ind₁'_comp_lsingle, ←LinearMap.comp_assoc, ind₁'_map_comp_lsingle,
    LinearMap.comp_assoc, hf, LinearMap.comp_assoc, ind₁'_map_comp_lsingle,
    ←LinearMap.comp_assoc, ←LinearMap.comp_assoc, ind₁'_comp_lsingle]

@[simps] def ind₁'_π : (G →₀ V) →ₗ[R] V where
  toFun f := f.sum (fun _ ↦ (1 : V →ₗ[R] V))
  map_add' _ _ :=  sum_add_index' (congrFun rfl) fun _ _ ↦ congrFun rfl
  map_smul' _ _ := by simp

omit [Group G] in
@[simp] lemma ind₁'_π_comp_lsingle (x : G) :
    ind₁'_π ∘ₗ lsingle x = LinearMap.id (R := R) (M := V) := by
  ext
  simp

lemma ind₁'_π_comm (g : G) : ind₁'_π ∘ₗ ind₁' ρ g = ρ g ∘ₗ ind₁'_π := by
  ext; simp

@[simps] def ind₁'_lmap : (G →₀ V) →ₗ[R] Ind₁V R G V where
  toFun f:= f.sum (fun g v ↦ Ind₁V.mk R G V g (ρ g v))
  map_add' _ _ := by
    rw [sum_add_index']
    · simp
    · intros
      simp only [map_add]
  map_smul' _ _ := by
    rw [sum_smul_index']
    · simp only [map_smul, RingHom.id_apply, smul_sum]
    · intro
      simp only [map_zero]

def ind₁'_invlmap_aux : (G →₀ R) →ₗ[R] V →ₗ[R] G →₀ V where
  toFun f := {
    toFun v := f.sum (fun g r ↦ Finsupp.single g (r • (ρ g⁻¹ v)))
    map_add' v1 v2 := by simp
    map_smul' r v := by simp [Finsupp.smul_sum, smul_smul, mul_comm]}
  map_add' f1 f2 := by
    ext v g
    simp only [LinearMap.coe_mk, AddHom.coe_mk, sum_apply, LinearMap.add_apply, coe_add, coe_sum,
      Pi.add_apply]
    rw [Finsupp.sum_add_index' (f := f1) (g := f2) (by simp) (by simp [add_smul]),
      Finsupp.sum_apply', Finsupp.sum_apply']
  map_smul' r f := by
    ext : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
    simp [smul_smul]

def ind₁'_invlmap : Ind₁V R G V →ₗ[R] (G →₀ V) :=
  (TensorProduct.lift (ind₁'_invlmap_aux ρ)).comp ((Coinvariants.ker _).quotEquivOfEqBot (by
    simpa [Coinvariants.ker, sub_eq_zero]
     using fun a ↦ by exact LinearMap.congr_fun TensorProduct.map_id a)).toLinearMap

/--
The linear automorphism of `G →₀ V`, which gives an isomorphism
between `ind₁' ρ` and `ind₁ R G V`.
-/
@[simps!] def ind₁'_lequiv : (G →₀ V) ≃ₗ[R] Ind₁V R G V where
  toLinearMap := ind₁'_lmap ρ
  invFun := ind₁'_invlmap ρ
  left_inv f := by
    rw [LinearMap.toFun_eq_coe]
    induction f using Finsupp.induction_linear
    · simp
    · rename_i f g h1 h2
      rw [map_add, map_add, h1, h2]
    · rename_i g v
      simp [ind₁'_invlmap, Submodule.quotEquivOfEqBot, Coinvariants.mk]
      change (TensorProduct.lift ρ.ind₁'_invlmap_aux)
        (LinearMap.id (R := R) ((fun₀ | g => (1 : R)) ⊗ₜ[R] (ρ g) v)) = fun₀ | g => v
      simp [ind₁'_invlmap_aux]
  right_inv f := by
    rw [LinearMap.toFun_eq_coe]
    induction' f using Submodule.Quotient.induction_on with f
    induction' f using TensorProduct.induction_on
    · simp
    · rename_i x y
      simp only [ind₁'_invlmap, Submodule.quotEquivOfEqBot,
        LinearEquiv.ofLinear_toLinearMap, LinearMap.coe_comp, Function.comp_apply]
      change ρ.ind₁'_lmap ((TensorProduct.lift ρ.ind₁'_invlmap_aux)
        (LinearMap.id (R := R) (x ⊗ₜ[R] y))) = Submodule.Quotient.mk (x ⊗ₜ[R] y)
      simp only [LinearMap.id_coe, id_eq, TensorProduct.lift.tmul]
      induction x using Finsupp.induction_linear
      · simp
      · rename_i f g h1 h2
        rw [map_add, LinearMap.add_apply, map_add, h1, h2, TensorProduct.add_tmul]
        rfl
      · rename_i g r
        simp [ind₁'_invlmap_aux, Coinvariants.mk]
        rw [← map_smul, ← Submodule.mkQ_apply]
        congr
        rw [TensorProduct.smul_tmul', Finsupp.smul_single, smul_eq_mul, mul_one]
    · rename_i f g h1 h2
      rw [← Submodule.mkQ_apply, map_add, map_add, map_add,
        Submodule.mkQ_apply, Submodule.mkQ_apply, h1, h2]

@[simp] lemma ind₁'_lequiv_comp_lsingle (x : G) :
    ρ.ind₁'_lequiv ∘ₗ lsingle x = Ind₁V.mk R G V x ∘ₗ ρ x := by ext; simp

lemma ind₁'_lequiv_comm (g : G) :
    ind₁'_lequiv ρ ∘ₗ ind₁' ρ g = ind₁ R G V g ∘ₗ ind₁'_lequiv ρ := by
  ext x : 1
  rw [LinearMap.comp_assoc, ind₁'_comp_lsingle,
    ←LinearMap.comp_assoc, ind₁'_lequiv_comp_lsingle, LinearMap.comp_assoc, map_mul]
  change _ ∘ₗ (_ * ρ g) = _
  rw [mul_assoc, ←map_mul, inv_mul_cancel, map_one, mul_one]
  nth_rw 2 [LinearMap.comp_assoc]
  rw [ind₁'_lequiv_comp_lsingle, ←LinearMap.comp_assoc, ind₁_apply]

def ind₁'_lequiv_coind₁' [Finite G] : (G →₀ V) ≃ₗ[R] (G → V) :=
  linearEquivFunOnFinite R V G

omit [Group G] in
lemma ind₁'_lequiv_coind₁'_apply [Finite G] (x y : G) (v : V) :
  ind₁'_lequiv_coind₁' (R := R) (single x v) y = (single x v y) := rfl

lemma ind₁'_lequiv_coind₁'_comm [Finite G] (g : G) :
    ind₁'_lequiv_coind₁'.toLinearMap ∘ₗ ρ.ind₁' g = ρ.coind₁' g ∘ₗ ind₁'_lequiv_coind₁'.toLinearMap
    := by
  ext x : 1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ind₁'_comp_lsingle]
  ext v y : 2
  simp [ind₁'_lequiv_coind₁'_apply]
  by_cases h : x * g⁻¹ = y
  · rw [h, single_eq_same, ←h, mul_assoc, inv_mul_cancel, mul_one, single_eq_same]
  · rw [single_eq_of_ne, single_eq_of_ne, map_zero]
    · contrapose! h
      rw [h, mul_inv_cancel_right]
    · exact h

lemma ind₁'_lequiv_coind₁'_comm' [Finite G] (g : G) :
    ind₁'_lequiv_coind₁'.symm.toLinearMap ∘ₗ ρ.coind₁' g
    = ρ.ind₁' g ∘ₗ ind₁'_lequiv_coind₁'.symm.toLinearMap := by
  ext f : 1
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  symm
  change (ind₁'_lequiv_coind₁'.toLinearMap ∘ₗ (ρ.ind₁' g)) _ = (ρ.coind₁' g) f
  rw [ind₁'_lequiv_coind₁'_comm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

lemma coind₁'_ι_app_injective : Function.Injective (@coind₁'_ι R G _ V _ _) := by
  intro _ _ h
  change Function.const _ _ = Function.const _ _ at h
  simpa using h

end Representation

namespace Rep

variable {R} (M : Rep R G) (A : ModuleCat R)

abbrev coind₁ : ModuleCat R ⥤ Rep R G :=
  trivialFunctor R (⊥ : Subgroup G) ⋙ coindFunctor R (⊥ : Subgroup G).subtype

/--
Coinduced representations have trivial cohomology.
-/
instance coind₁_trivialCohomology (A : ModuleCat R) : ((coind₁ G).obj A).TrivialCohomology :=
  /-
  For any subgroup `S` of `G`, the restriction to `S` of `(coind₁ G).obj A` is isomorphic to
  a direct sum of representations of the form `(coind₁ S).obj A`, one copy for each coset of `S`.
  It remains to show that `Hⁿ(S,(coind₁ S).obj A) ≅ 0`. By Shapiro's lemma, we have
  `Hⁿ(S,(coind₁ S).obj A) ≅ Hⁿ(Unit,A) ≅ 0`.
  -/
  sorry

variable {G}

def coind₁_quotientToInvariants_iso_aux1 {Q : Type} [Group Q] (φ : G →* Q) :
    (invariants (MonoidHom.comp ((coind₁ G).obj A).ρ φ.ker.subtype)) ≃ₗ[R]
    (coindV (⊥ : Subgroup (G ⧸ φ.ker)).subtype
    ((trivialFunctor R (⊥ : Subgroup (G ⧸ φ.ker))).obj A).ρ) where
  toFun x := ⟨Quotient.lift x.1.1 (fun a b hab ↦ by
    nth_rw 1 [← x.2 ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩]
    simp), by simp [coindV, trivialFunctor]⟩
  map_add' x y := by
    ext x
    induction x using QuotientGroup.induction_on
    simp
  map_smul' r x := by
    ext x
    induction x using QuotientGroup.induction_on
    simp
  invFun x := ⟨⟨x.1.comp QuotientGroup.mk, by simp [coindV, trivialFunctor]⟩, fun a ↦ by
    simpa [← Subtype.val_inj] using funext (by simp)⟩
  left_inv := by simpa [Function.LeftInverse] using fun _ _ _ ↦ funext (by simp)
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse, trivialFunctor_obj_V,
      Functor.comp_obj, coindFunctor_obj, of_ρ, Subtype.forall, Subtype.mk.injEq]
    intro _ _
    ext x
    induction x using QuotientGroup.induction_on
    simp

def coind₁_quotientToInvariants_iso_aux2 {H : Type} [Group H] (φ : G ≃* H) :
    (coindV (⊥ : Subgroup G).subtype
    ((trivialFunctor R (⊥ : Subgroup G)).obj A).ρ) ≃ₗ[R]
    ↥(coindV (⊥ : Subgroup H).subtype ((trivialFunctor R (⊥ : Subgroup H)).obj A).ρ) where
  toFun x := ⟨x.1.comp φ.symm, by
    simp [coindV, trivialFunctor]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨y.1.comp φ, by simp [coindV, trivialFunctor]⟩
  left_inv := by simpa [Function.LeftInverse] using fun a ha ↦ by simp [Function.comp_assoc]
  right_inv := by
    simpa [Function.RightInverse, Function.LeftInverse] using
      fun a ha ↦ by simp [Function.comp_assoc]

def coind₁_quotientToInvariants_iso {Q : Type} [Group Q] {φ : G →* Q}
    (surj : Function.Surjective φ) :
    (((coind₁ G).obj A) ↑ surj) ≅ (coind₁ Q).obj A := by
  refine Action.mkIso (LinearEquiv.toModuleIso ((coind₁_quotientToInvariants_iso_aux1 A φ).trans
    (coind₁_quotientToInvariants_iso_aux2 A (QuotientGroup.quotientKerEquivOfSurjective φ surj))))
    (fun q ↦ ?_)
  simp only [Functor.comp_obj, coindFunctor_obj, quotientToInvariantsFunctor'_obj, Action.res_obj_V,
    trivialFunctor_obj_V, of_ρ, Action.res_obj_ρ, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    Function.comp_apply, LinearEquiv.toModuleIso_hom, coind_apply]
  ext x q'
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.trans_apply, ModuleCat.endRingEquiv_symm_apply_hom _ _,
    LinearMap.restrict_apply, LinearMap.funLeft_apply, coind₁_quotientToInvariants_iso_aux1,
    coind₁_quotientToInvariants_iso_aux2, trivialFunctor_obj_V, Functor.comp_obj, coindFunctor_obj,
    of_ρ, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, map_mul]
  let r := (QuotientGroup.quotientKerEquivOfSurjective φ surj).symm q
  let r' := (QuotientGroup.quotientKerEquivOfSurjective φ surj).symm q'
  let s := Classical.choose (QuotientGroup.mk_surjective r)
  let s' := Classical.choose (QuotientGroup.mk_surjective r')
  have h1 : QuotientGroup.mk s = (QuotientGroup.quotientKerEquivOfSurjective φ surj).symm q :=
    Classical.choose_spec (QuotientGroup.mk_surjective r)
  have h2 : QuotientGroup.mk s' = (QuotientGroup.quotientKerEquivOfSurjective φ surj).symm q' :=
    Classical.choose_spec (QuotientGroup.mk_surjective r')
  simp [← h1, ← h2, ← QuotientGroup.mk_mul]

/--
The `H`-invariants of `(coind₁ G).obj A` form an representation of `G ⧸ H` with trivial cohomology.
-/
instance coind₁_quotientToInvariants_trivialCohomology (A : ModuleCat R) {Q : Type} [Group Q]
    {φ : G →* Q} (surj : Function.Surjective φ) :
    ((coind₁ G ⋙ quotientToInvariantsFunctor' surj).obj A).TrivialCohomology :=
  .of_iso (Rep.coind₁_quotientToInvariants_iso A surj)

/--
The functor which takes a representation `ρ` of `G` on `V` to the
coinduced representation on `G → V`, where the action of `G` is by `ρ` in `V` and by
right translation on `G`.
-/
@[simps obj]
def coind₁' : Rep R G ⥤ Rep R G where
  obj M := of M.ρ.coind₁'
  map φ := {
    hom := ofHom ((ModuleCat.Hom.hom φ.hom).compLeft G)
    comm g := by
      ext
      change (Action.ρ _ g ≫ φ.hom) _ = _
      rw [φ.comm]
      rfl
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The inclusion of a representation `M` of `G` in the coinduced representation `coind₁'.obj M`.
This map takes an element `m : M` to the constant function with value `M`.
-/
@[simps] def coind₁'_ι : 𝟭 (Rep R G) ⟶ coind₁' where
  app M := {
    hom    := ofHom Representation.coind₁'_ι
    comm _ := by ext : 1; exact M.ρ.coind₁'_ι_comm _
  }
  naturality _ _ _ := by simpa using by rfl

instance : Mono (coind₁'_ι.app M) := by
  refine (mono_iff_injective (coind₁'_ι.app M)).mpr ?_
  intro x y eq
  change Function.const G x 1 = Function.const G y 1
  exact congrFun eq 1

lemma LinearEquiv.symm_apply {R S M N : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module S N] {σ : R →+* S} {σ' : S →+* R}
    {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ} (e : M ≃ₛₗ[σ] N) (n : N) :
  e.symm n = e.invFun n := rfl

@[simps] def coind₁'_obj_iso_coind₁ : coind₁'.obj M ≅ (coind₁ G).obj M.V where
  hom := {
    hom := ofHom (by
      apply M.ρ.coind₁'_lequiv_coind₁.toLinearMap
    )
    comm g := by
      ext : 1
      exact M.ρ.coind₁'_lequiv_coind₁_comm g
  }
  inv := {
    hom := ofHom M.ρ.coind₁'_lequiv_coind₁.symm.toLinearMap
    comm g := by
      ext f
      simp only [Functor.comp_obj, coindFunctor_obj, trivialFunctor_obj_V,
        RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp,
        MonoidHom.coe_coe, RingHom.coe_coe, Function.comp_apply, coind_apply, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom, LinearMap.coe_comp, ρ_hom]
      rw [ModuleCat.endRingEquiv_symm_apply_hom, LinearMap.restrict_apply]
      simp only [coind₁', Representation.coind₁', coind₁'_lequiv_coind₁, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply, of_ρ, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, mul_inv_rev, map_mul, Module.End.mul_apply, self_inv_apply]
      congr
  }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

instance coind₁'_trivialCohomology : (coind₁'.obj M).TrivialCohomology :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

instance coind₁'_quotientToInvariants_trivialCohomology {Q : Type} [Group Q] {φ : G →* Q}
    (surj : Function.Surjective φ) : ((coind₁'.obj M) ↑ surj).TrivialCohomology := by
  have iso := (quotientToInvariantsFunctor' surj).mapIso (coind₁'_obj_iso_coind₁ M)
  have _ : ((quotientToInvariantsFunctor' surj).obj ((coind₁ G).obj M.V)).TrivialCohomology
  · exact coind₁_quotientToInvariants_trivialCohomology M.V surj
  exact .of_iso iso

variable (G)

/--
The functor taking an `R`-module `A` to the induced representation of `G` on `G →₀ A`,
where the action of `G` is by left-translation.
-/
def ind₁ : ModuleCat R ⥤ Rep R G :=
  trivialFunctor R (⊥ : Subgroup G) ⋙ indFunctor R (⊥ : Subgroup G).subtype

instance ind₁_trivialHomology (A : ModuleCat R) : TrivialHomology ((ind₁ G).obj A) :=
  /-
  Let `S` be a subgroup of `G`.
  The restriction to `S` of `(ind₁ G).obj A` is isomorphic (after choosing coset representatives)
  to `(ind₁ S).obj (G/S →₀ A)`. By Shapiro's lemma, this has trivial homology.
  -/
  sorry

@[simp] lemma ind₁_obj_ρ (A : ModuleCat R) : ((ind₁ G).obj A).ρ = Representation.ind₁ R G A := rfl

variable {G}

/--
The functor taking a representation `M` of `G` to the induced representation on
the space `G →₀ M`. The action of `G` on `G →₀ M.V` is by left-translation on `G` and
by `M.ρ` on `M.V`.
-/
@[simps! obj]
def ind₁' : Rep R G ⥤ Rep R G where
  obj M := of M.ρ.ind₁'
  map f := {
    hom := ofHom (Representation.ind₁'_map f.hom.hom)
    comm g := by
      ext : 1
      apply ind₁'_map_comm
      intro g
      simpa [ConcreteCategory.ext_iff] using f.comm g
  }
  map_id _ := by
    ext : 2
    exact mapRange.linearMap_id
  map_comp _ _ := by
    ext : 2
    exact mapRange.linearMap_comp _ _

/--
The natural projection `ind₁'.obj M ⟶ M`, which takes `f : G →₀ M.V` to the sum of the
values of `f`.
-/
def ind₁'_π : ind₁' ⟶ 𝟭 (Rep R G) where
  app M := ofHom (C := Rep R G) {
    val := Representation.ind₁'_π
    property g := by
      rw [←LinearMap.coe_comp, ←LinearMap.coe_comp, ←DFunLike.ext'_iff]
      apply ind₁'_π_comm
  }
  naturality _ _ x := by
    ext z
    change Representation.ind₁'_π ((ind₁'.map x).hom.hom z) =
      x.hom.hom (Representation.ind₁'_π z)
    simp [ind₁', sum_mapRange_index]
    exact (map_finsuppSum x.hom.hom z _).symm

instance : Epi (ind₁'_π.app M) := by
  refine (epi_iff_surjective (ind₁'_π.app M)).2 fun m ↦ ⟨single 1 m, ?_⟩
  change Representation.ind₁'_π _ = _
  simp only [Functor.id_obj, ind₁'_π_apply, Module.End.one_apply, sum_single_index]

lemma ind₁'_obj_ρ_apply (g : G) : (ind₁'.obj M).ρ g = M.ρ.ind₁' g := rfl

def ind₁'_obj_iso_ind₁ : ind₁'.obj M ≅ (ind₁ G).obj M.V :=
  Action.mkIso (LinearEquiv.toModuleIso M.ρ.ind₁'_lequiv) (fun g ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.congr_fun (ind₁'_lequiv_comm M.ρ g) x))

instance ind₁'_trivialHomology : TrivialHomology (ind₁'.obj M) :=
  let _ := (ind₁_trivialHomology G M.V)
  .of_iso (ind₁'_obj_iso_ind₁ M)

variable (G) in
/-- A version of `ind₁` that's actually defined as `G →₀ A` with some action. -/
@[simps! V] def ind₁AsFinsupp : Rep R G := ind₁'.obj <| (trivialFunctor R G).obj A

variable (G) in
/-- A version of `coind₁` that's actually defined as `G → A` with some action. -/
@[simps! V] def coind₁AsPi : Rep R G := coind₁'.obj <| (trivialFunctor R G).obj A

@[simp]
lemma ind₁AsFinsupp_ρ (g : G) : (ind₁AsFinsupp G A).ρ g = lmapDomain _ _ (fun x ↦ x * g⁻¹) := by
  simp [ind₁AsFinsupp, trivialFunctor]

-- TODO: Replace with `coind₁AsPi_ρ`. Currently can't be proved first for obscure reasons.
@[simp]
lemma coind₁AsPi_ρ_apply (g : G) (f : G → A) (x : G) : (coind₁AsPi G A).ρ g f x = f (x * g) := by
  simp [coind₁AsPi, coind₁', trivialFunctor]

@[simp]
lemma coind₁AsPi_ρ (g : G) :
    (coind₁AsPi G A).ρ g = (LinearEquiv.piCongrLeft R (fun _ ↦ A) <| (Equiv.mulRight g).symm).toLinearMap := by
  simp only [coind₁AsPi_V]
  ext f x
  erw [coind₁AsPi_ρ_apply]
  simp [LinearEquiv.piCongrLeft]

/-- `ind₁AsFinsupp` is isomorphic to `ind₁` pointwise. -/
def ind₁AsFinsuppIso : ind₁AsFinsupp G A ≅ (ind₁ G).obj A := ind₁'_obj_iso_ind₁ _

/-- `coind₁AsPi` is isomorphic to `coind₁` pointwise. -/
def coind₁AsPiIso : coind₁AsPi G A ≅ (coind₁ G).obj (.of R A) := coind₁'_obj_iso_coind₁ _

section FiniteGroup

variable [DecidableEq G] (A : ModuleCat R)
set_option linter.unusedSectionVars false

-- Hack:
instance : DecidableRel ⇑(QuotientGroup.rightRel (⊥ : Subgroup G)) :=
  Classical.decRel _

abbrev ind₁_obj_iso_coind₁_obj [Finite G] : (ind₁ G).obj A ≅ (coind₁ G).obj A :=
  indCoindIso _

def ind₁'_iso_coind₁' [Finite G] : ind₁' (R := R) (G := G) ≅ coind₁' where
  hom := {
    app M := {
      hom := ofHom ind₁'_lequiv_coind₁'.toLinearMap
      comm g := by
        ext : 1
        apply ind₁'_lequiv_coind₁'_comm
    }
  }
  inv := {
    app M := {
      hom := ofHom ind₁'_lequiv_coind₁'.symm.toLinearMap
      comm g := by
        ext : 1
        apply ind₁'_lequiv_coind₁'_comm'
    }
    naturality _ _ _ := by
      ext : 3
      change ind₁'_lequiv_coind₁'.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      rfl
  }

lemma ind₁'_iso_coind₁'_app_apply [Finite G] (f : G →₀ M.V) (x : G) :
    (ind₁'_iso_coind₁'.app M).hom f x = f x := by
  rfl

instance ind₁_trivialCohomology [Finite G] : TrivialCohomology ((ind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A)

instance ind₁'_trivialCohomology [Finite G] : TrivialCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_obj_iso_ind₁ M)

instance coind₁_trivialHomology [Finite G] : TrivialHomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance coind₁'_trivialHomology [Finite G] : TrivialHomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

instance ind₁_trivialtateCohomology [Finite G] : TrivialTateCohomology ((ind₁ G).obj A) := sorry

instance coind₁_trivialTate [Finite G] : TrivialTateCohomology ((coind₁ G).obj A) :=
  .of_iso (ind₁_obj_iso_coind₁_obj A).symm

instance coind₁'_trivialTate [Finite G] : TrivialTateCohomology (coind₁'.obj M) :=
  .of_iso (coind₁'_obj_iso_coind₁ M)

instance ind₁'_trivialTate [Finite G] : TrivialTateCohomology (ind₁'.obj M) :=
  .of_iso (ind₁'_iso_coind₁'.app M)

end FiniteGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- For a finite Galois extension `L/K`, the isomorphism between `ind₁` of `K`
and `L` in the category of `(L ≃ₐ[K] L)`-representations. -/
noncomputable def iso_ind₁ :
    (Rep.ind₁ (L ≃ₐ[K] L)).obj (.of K K) ≅ .of (AlgEquiv.toLinearMapHom K L) := by
  refine (Rep.ind₁AsFinsuppIso (G := (L ≃ₐ[K] L)) (.of K K)).symm ≪≫
    Action.mkIso (LinearEquiv.toModuleIso
      ((IsGalois.normalBasis K L).reindex (Equiv.inv (L ≃ₐ[K] L))).repr.symm) ?_
  intro x
  ext f
  simp only [Rep.ind₁AsFinsupp_V, Rep.trivialFunctor_obj_V, LinearEquiv.toModuleIso_hom,
    Basis.coe_repr_symm, Basis.coe_reindex, Equiv.inv_symm, Equiv.inv_apply, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    AlgEquiv.toLinearMapHom_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ _ (fun i => by exact zero_smul K _),
    Finsupp.sum_fintype _ _ (fun i => by exact zero_smul K _)]
  -- For strange reasons, the simp lemma `ind₁AsFinsupp_ρ` doesn't work here, so
  -- we unfold instead.
  unfold Rep.ind₁AsFinsupp
  simp only [Rep.ind₁'_obj, Rep.trivialFunctor_obj_V, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, RingHom.coe_coe,
    Function.comp_apply, Representation.ind₁'_apply, map_sum, map_smul]
  unfold ModuleCat.endRingEquiv
  simp only [RingEquiv.symm_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, ModuleCat.ofHom_comp,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.lmapDomain_apply]
  apply Fintype.sum_equiv (Equiv.mulRight x)
  intro y
  rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun _ _ => rfl), Finsupp.mapRange_apply]
  simp only [Equiv.coe_mulRight, mul_inv_rev]
  rw [IsGalois.normalBasis_apply y⁻¹, IsGalois.normalBasis_apply (x⁻¹ * y⁻¹)]
  simp only [AlgEquiv.mul_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_inv]
  congr 1
  change Finsupp.mapDomain (Equiv.mulRight x).symm _ _ = _
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]
  simp [Equiv.mulRight_symm, inv_inv, Equiv.coe_mulRight]
  rw [AlgEquiv.apply_symm_apply]

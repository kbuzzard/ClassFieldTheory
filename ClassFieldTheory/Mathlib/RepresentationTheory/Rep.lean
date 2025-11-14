import ClassFieldTheory.Mathlib.Data.Finsupp.Single
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Rep

open CategoryTheory Limits ConcreteCategory

noncomputable section

namespace Rep
universe u
variable {R G H : Type u} [CommRing R] [Group G] {A B : Rep R G}

-- TODO: Rename `of_ρ` to `ρ_of`
@[simp] lemma of_ρ' (M : Rep R G) : of M.ρ = M := rfl

lemma ρ_apply (g : G) : (leftRegular R G).ρ g = Finsupp.lmapDomain R R (g * ·) := rfl

@[simp] lemma ρ_mul_eq_comp (M : Rep R G) (x y : G) :
    Action.ρ M (x * y) = Action.ρ M y ≫ Action.ρ M x := map_mul (Action.ρ M) x y

-- TODO : add in mathlib, see GroupCohomology.IndCoind.TrivialCohomology
--attribute [simps obj_ρ] trivialFunctor

@[simps]
def mkIso (M₁ M₂ : Rep R G) (f : M₁.V ≅ M₂.V)
    (hf : ∀ g : G, ∀ m : M₁, f.hom (M₁.ρ g m) = M₂.ρ g (f.hom m) := by aesop) : M₁ ≅ M₂ where
  hom.hom := f.hom
  inv.hom := f.inv
  inv.comm g := by rw [f.comp_inv_eq, Category.assoc, eq_comm, f.inv_comp_eq]; aesop

instance richards : LinearMapClass (Action.HomSubtype _ _ A B) R A B where
  map_add f := map_add f.val
  map_smulₛₗ f := map_smul f.val

-- This hack instance will be removed after the relevant PR is merged.
instance [MulAction G H] :
    LinearMapClass (Action.HomSubtype _ _ A (ofMulAction R G H)) R A (ofMulAction R G H) := richards

@[simp] lemma coe_hom (f : A ⟶ B) : ⇑f.hom = f := rfl
@[simp] lemma hom_apply (f : A ⟶ B) (x : A) : f.hom x = f x := rfl

example (A B : Rep R G) (f : A ⟶ B ) (a b : A) (c : R) : f (a + c • b) = f a + c • f b := by simp

@[simp] lemma zero_apply (v : A) : (0 : A ⟶ B) v = 0 := rfl
@[simp] lemma add_apply (f₁ f₂ : A ⟶ B) (v : A) : (f₁ + f₂) v = f₁ v + f₂ v := rfl

@[simp]
lemma sub_apply (f₁ f₂ : A ⟶ B) (v : A) : (f₁ - f₂) v = f₁ v - f₂ v := by
  rw [← hom_apply, Action.sub_hom, ← ModuleCat.Hom.hom, ModuleCat.hom_sub, LinearMap.sub_apply,
    hom_apply, hom_apply]

@[simp] lemma smul_apply (c : R) (f : A ⟶ B) (v : A) : (c • f) v = c • (f v) := rfl

lemma comp_apply {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) (v : A.V) : (f ≫ g) v = g (f v) := rfl

lemma leftRegularHomEquiv_symm_comp (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f.hom.hom a) := by
  rw [LinearEquiv.eq_symm_apply, leftRegularHomEquiv_apply, hom_apply, Rep.comp_apply]
  congr!
  exact A.leftRegularHomEquiv.right_inv a

/--
If `f : M₁ ⟶ M₂` is a morphism in `Rep R G` and `f m = 0`, then
there exists `k : kernel f` such that `kernel.ι _ k = m`.
-/
lemma exists_kernelι_eq {M₁ M₂ : Rep R G} (f : M₁ ⟶ M₂) (m : M₁) (hm : f.hom.hom m = 0) :
    ∃ k : kernel f (C := Rep R G), (kernel.ι f).hom.hom k = m := by
  let g : leftRegular R G ⟶ M₁ := (leftRegularHomEquiv M₁).symm m
  have : g ≫ f = 0 := by rw [leftRegularHomEquiv_symm_comp]; ext1; rw [hm, map_zero]
  let lift : leftRegular R G ⟶ kernel f := kernel.lift f g this
  use leftRegularHomEquiv (kernel f) lift
  rw [leftRegularHomEquiv_apply]
  change (lift ≫ kernel.ι f) (Finsupp.single 1 1) = m
  rw [kernel.lift_ι]
  convert (leftRegularHomEquiv_apply M₁ g).symm
  change m = M₁.leftRegularHomEquiv (M₁.leftRegularHomEquiv.symm m)
  rw [LinearEquiv.apply_symm_apply]

@[simp] lemma forget₂_map (f : A ⟶ B) : (forget₂ (Rep R G) (ModuleCat R)).map f = f.hom := rfl

end Rep

lemma _root_.Representation.norm_ofIsTrivial (R M G : Type*) [Group G] [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype G] (ρ : Representation R G M) [ρ.IsTrivial] : ρ.norm = Nat.card G := by
  ext; simp [Representation.norm]

theorem _root_.range_eq_span {R : Type*} [CommSemiring R] (n : ℕ) :
    LinearMap.range (n : R →ₗ[R] R) = Ideal.span {(n : R)} := by
  ext x; simp [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_right, eq_comm]

open Finsupp

namespace Rep.leftRegular
universe u
variable {R G : Type u} [CommRing R] [Group G]

/--
`Rep.leftRegular.of g` is the group element `g : G` regarded as
as element of `Rep.leftRegular ℤ G`. Its type is `CoeSort.coe (Rep.leftRegular ℤ G)`.
-/
noncomputable def of (g : G) : leftRegular R G := single g 1

lemma of_def (g : G) : @of R G _ _ g = single g 1 := rfl

lemma of_apply [DecidableEq G] (g h : G) : (of g) h = if g = h then (1 : R) else (0 : R) :=
  Finsupp.single_apply

lemma of_apply_eq_one (g : G) : (of g) g = (1 : R) := by classical rw [of_apply, if_pos rfl]

lemma eq_sum_smul_of (v : leftRegular R G) : v = ∑ x ∈ v.support, (v x) • (of x) := by
  change v = v.sum fun x s ↦ s • of x
  simp [of_def]

lemma ρ_apply (g : G) : (leftRegular R G).ρ g = lmapDomain R R (g * ·) := rfl

lemma ρ_apply₃_self_mul (g : G) (v : leftRegular R G) (x : G) :
    (leftRegular R G).ρ g v (g * x) = v x := mapDomain_apply (mul_right_injective _) v x

lemma ρ_apply₃ (g : G) (v : leftRegular R G) (x : G) : (leftRegular R G).ρ g v x = v (g⁻¹ * x) := by
  convert ρ_apply₃_self_mul g v (g⁻¹ * x)
  rw [← mul_assoc, mul_inv_cancel, one_mul]

lemma ρ_apply_of (g x : G) : (leftRegular R G).ρ g (of x) = of (g * x) := by
  classical ext; rw [ρ_apply₃, of_apply, of_apply, eq_inv_mul_iff_mul_eq]

lemma ρ_comp_lsingle (g x : G) : (leftRegular R G).ρ g ∘ₗ lsingle x = lsingle (g * x) := by
  ext; simp

lemma of_eq_ρ_of_one (g : G) : of g = (leftRegular R G).ρ g (of 1) := by rw [ρ_apply_of, mul_one]

lemma leftRegularHom_of {A : Rep R G} (v : A) (g : G) : (A.leftRegularHom v) (of g) = A.ρ g v :=
  leftRegularHom_hom_single g v 1 |>.trans <| one_smul _ _

/-- If `g` is in the centre of `G` then the unique morphism of the left regular representation
which takes `1` to `g` is (as a linear map) `(leftRegular R G).ρ g`. -/
lemma leftRegularHom_eq_ρReg (g : G) (hg : g ∈ Subgroup.center G) :
    ((leftRegular R G).leftRegularHom (of g)).hom.hom = (leftRegular R G).ρ g := by
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
lemma ε_of_one : (ε R G) (of 1) = (1 : R) := leftRegularHom_of 1 1

lemma ε_comp_ρ (g : G) : ModuleCat.ofHom ((leftRegular R G).ρ g) ≫ (ε R G).hom = (ε R G).hom :=
  (ε R G).comm g

lemma ε_comp_ρ_apply (g : G) (v : (leftRegular R G).V) :
    (ε R G).hom.hom ((leftRegular R G).ρ g v) = ε R G v := by
  change ((ModuleCat.ofHom _) ≫ (ε R G).hom).hom v = _
  rw [ε_comp_ρ]
  rfl

@[simp]
lemma ε_of (g : G) : (ε R G).hom.hom (of g) = (1 : R) := by
  have : of g = (leftRegular R G).ρ g (of 1) := by rw [ρ_apply_of, mul_one]
  rw [this, ε_comp_ρ_apply, ε_of_one]

instance :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
      (leftRegular R G) (trivial R G R) where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

instance :
    MulActionHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
      R (leftRegular R G) (trivial R G R) where
  map_smulₛₗ f := map_smul f.val

lemma ε_eq_sum' (v : leftRegular R G) : (ε R G).hom.hom v = ∑ x ∈ v.support, v x := by
  nth_rw 1 [eq_sum_smul_of v, map_sum]
  congr!
  rw [map_smul, ε_of, smul_eq_mul, mul_one]

lemma ε_eq_sum (v : leftRegular R G) [Fintype G] : (ε R G).hom.hom v = ∑ g : G, v g := by
  refine ε_eq_sum' v|>.trans <| (finsum_eq_sum_of_support_subset v (by simp)).symm.trans ?_
  simp [finsum_eq_sum_of_fintype]

/--
The left regular representation is nontrivial (i.e. non-zero) if and only if the coefficient
ring is trivial.
-/
lemma nontrivial_iff_nontrivial : Nontrivial (leftRegular R G) ↔ Nontrivial R := by
  simp [Finsupp.nontrivial_iff]; infer_instance

lemma ε_epi : Epi (ε R G) := epi_of_surjective _ fun r ↦
  ⟨r • of 1, by erw [map_smul, ε_of_one, smul_eq_mul, mul_one]⟩

end Rep.leftRegular

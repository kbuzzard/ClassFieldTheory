import Mathlib
import ClassFieldTheory.GroupCohomology.«05_TrivialCohomology»

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

end Rep.leftRegular

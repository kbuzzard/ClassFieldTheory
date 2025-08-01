import ClassFieldTheory.Mathlib.CategoryTheory.Action.Limits
import Mathlib.RepresentationTheory.Rep

open CategoryTheory Limits

namespace Rep
variable {R G : Type} [CommRing R] [Group G] {A B : Rep R G}

-- TODO : add in mathlib, see GroupCohomology.IndCoind.TrivialCohomology
--attribute [simps obj_ρ] trivialFunctor

@[simps]
def mkIso (M₁ M₂ : Rep R G) (f : M₁.V ≅ M₂.V)
    (hf : ∀ g : G, ∀ m : M₁, f.hom (M₁.ρ g m) = M₂.ρ g (f.hom m) := by aesop) : M₁ ≅ M₂ where
  hom.hom := f.hom
  inv.hom := f.inv
  inv.comm g := by rw [f.comp_inv_eq, Category.assoc, eq_comm, f.inv_comp_eq]; aesop


instance mine₁: MulActionHomClass (Action.HomSubtype _ _ A B) R A B where
  map_smulₛₗ f := map_smul f.val

instance mine₂ : AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A B) A B where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

/-
This hack (the next two instances) will be removed after the relevant PR is merged.
-/
instance (H : Type) [MulAction G H] :
    MulActionHomClass (Action.HomSubtype _ _ A (ofMulAction R G H)) R A (ofMulAction R G H) := mine₁

instance (H : Type) [MulAction G H] :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A (ofMulAction R G H)) A
      (ofMulAction R G H) := mine₂

lemma hom_apply (f : A ⟶ B) (x : A) : f.hom x = f x := rfl

example (A B : Rep R G) (f : A ⟶ B ) (a b : A) (c : R) : f (a + c • b) = f a + c • f b := by simp

@[simp]
lemma zero_apply (v : A) : (0 : A ⟶ B) v = 0 := rfl
  --without this lemma, the following rewrites are needed:
  --rw [← hom_apply, Action.zero_hom, ← ModuleCat.Hom.hom, ModuleCat.hom_zero, LinearMap.zero_apply]

@[simp]
lemma add_apply (f₁ f₂ : A ⟶ B) (v : A) : (f₁ + f₂) v = f₁ v + f₂ v := rfl
  -- rw [← hom_apply, ← ModuleCat.Hom.hom, Action.add_hom, ModuleCat.hom_add, LinearMap.add_apply,
  --   hom_apply, hom_apply]

@[simp]
lemma sub_apply (f₁ f₂ : A ⟶ B) (v : A) : (f₁ - f₂) v = f₁ v - f₂ v := by
  rw [← hom_apply, Action.sub_hom, ← ModuleCat.Hom.hom, ModuleCat.hom_sub, LinearMap.sub_apply,
    hom_apply, hom_apply]

@[simp]
lemma smul_apply (c : R) (f : A ⟶ B) (v : A) : (c • f) v = c • (f v) := rfl
  -- rw [← hom_apply, Action.smul_hom, ← ModuleCat.Hom.hom, ModuleCat.hom_smul,
  --   LinearMap.smul_apply, hom_apply]

lemma comp_apply {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) (v : A.V) : (f ≫ g) v = g (f v) := rfl
  -- rw [← hom_apply, ← ModuleCat.Hom.hom, Action.comp_hom, ModuleCat.hom_comp,
  --   LinearMap.comp_apply, hom_apply, hom_apply]

lemma leftRegularHomEquiv_symm_comp (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f a) := by
  rw [LinearEquiv.eq_symm_apply, leftRegularHomEquiv_apply, hom_apply, Rep.comp_apply]
  congr
  exact A.leftRegularHomEquiv.right_inv a

/--
If `f : M₁ ⟶ M₂` is a morphism in `Rep R G` and `f m = 0`, then
there exists `k : kernel f` such that `kernel.ι _ k = m`.
-/
lemma exists_kernelι_eq {M₁ M₂ : Rep R G} (f : M₁ ⟶ M₂) (m : M₁) (hm : f m = 0) :
    ∃ k : kernel f (C := Rep R G), kernel.ι f k = m := by
  let g : leftRegular R G ⟶ M₁ := (leftRegularHomEquiv M₁).symm m
  have : g ≫ f = 0 := by rw [leftRegularHomEquiv_symm_comp, hm, map_zero]
  let lift : leftRegular R G ⟶ kernel f := kernel.lift f g this
  use leftRegularHomEquiv (kernel f) lift
  rw [leftRegularHomEquiv_apply]
  change (lift ≫ kernel.ι f) (Finsupp.single 1 1) = m
  rw [kernel.lift_ι]
  convert (leftRegularHomEquiv_apply M₁ g).symm
  change m = M₁.leftRegularHomEquiv (M₁.leftRegularHomEquiv.symm m)
  rw [LinearEquiv.apply_symm_apply]

end Rep

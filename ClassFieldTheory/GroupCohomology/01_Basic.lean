import Mathlib

variable {R G : Type} [Group G] [CommRing R]

open Rep
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology

section Rep
-- # General lemmas for the category `Rep R G`.

instance mine₁ (A B : Rep R G) : MulActionHomClass (Action.HomSubtype _ _ A B) R A B where
  map_smulₛₗ f := map_smul f.val

instance mine₂ (A B : Rep R G) :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A B) A B where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

/-
This hack (the next two instances) will be removed after the relevant PR is merged.
-/
instance (A : Rep R G) (H : Type) [MulAction G H] :
    MulActionHomClass (Action.HomSubtype _ _ A (ofMulAction R G H)) R A (ofMulAction R G H) :=
  mine₁ _ _
instance (A : Rep R G) (H : Type) [MulAction G H] :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A (ofMulAction R G H))
    A (ofMulAction R G H) := mine₂ A (ofMulAction R G H)

lemma Rep.hom_apply {A B : Rep R G} (f : A ⟶ B) (x : A) : f.hom x = f x := by
  rfl

example (A B : Rep R G) (f : A ⟶ B ) (a b : A) (c : R) : f (a + c • b) = f a + c • f b := by
  simp

-- #check Action.zero_hom
-- #check Action.add_hom
-- #check Action.smul_hom
@[simp]
lemma Action.sub_hom.{u} {V : Type (u + 1)} [LargeCategory V] {G : Type u} [Monoid G]
    [CategoryTheory.Preadditive V] {X Y : Action V G} (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom
    := by
  rw [eq_sub_iff_add_eq, ←Action.add_hom, sub_add_cancel]

@[simp]
lemma Rep.zero_apply {A B : Rep R G} (v : A) : (0 : A ⟶ B) v = 0 :=
  rfl
  --without this lemma, the following rewrites are needed:
  --rw [←hom_apply, Action.zero_hom, ←ModuleCat.Hom.hom, ModuleCat.hom_zero, LinearMap.zero_apply]

@[simp]
lemma Rep.add_apply {A B : Rep R G} (f₁ f₂ : A ⟶ B) (v : A) : (f₁ + f₂) v = f₁ v + f₂ v :=
  rfl
  -- rw [←hom_apply, ←ModuleCat.Hom.hom, Action.add_hom, ModuleCat.hom_add, LinearMap.add_apply,
  --   hom_apply, hom_apply]

@[simp]
lemma Rep.sub_apply {A B : Rep R G} (f₁ f₂ : A ⟶ B) (v : A) : (f₁ - f₂) v = f₁ v - f₂ v := by
  rw [←Rep.hom_apply, Action.sub_hom, ←ModuleCat.Hom.hom, ModuleCat.hom_sub, LinearMap.sub_apply,
    hom_apply, hom_apply]

@[simp]
lemma Rep.smul_apply {A B : Rep R G} (c : R) (f : A ⟶ B) (v : A) : (c • f) v = c • (f v) :=
  rfl
  -- rw [←hom_apply, Action.smul_hom, ←ModuleCat.Hom.hom, ModuleCat.hom_smul, LinearMap.smul_apply,
  --   hom_apply]

lemma Rep.comp_apply {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) (v : A.V) : (f ≫ g) v = g (f v)
  :=
  rfl
  -- rw [←hom_apply, ←ModuleCat.Hom.hom, Action.comp_hom, ModuleCat.hom_comp, LinearMap.comp_apply,
  --   hom_apply, hom_apply]

lemma Rep.leftRegularHomEquiv_symm_comp {A B : Rep R G} (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f a) := by
  rw [LinearEquiv.eq_symm_apply, leftRegularHomEquiv_apply, hom_apply, Rep.comp_apply]
  congr
  exact A.leftRegularHomEquiv.right_inv a

/--
If `f : M₁ ⟶ M₂` is a morphism in `Rep R G` and `f m = 0`, then
there exists `k : kernel f` such that `kernel.ι _ k = m`.
-/
lemma Rep.exists_kernelι_eq {M₁ M₂ : Rep R G} (f : M₁ ⟶ M₂) (m : M₁) (hm : f m = 0) :
    ∃ k : kernel f (C := Rep R G), kernel.ι f k = m := by
  let g : leftRegular R G ⟶ M₁ := (leftRegularHomEquiv M₁).symm m
  have : g ≫ f = 0
  · rw [leftRegularHomEquiv_symm_comp, hm, map_zero]
  let lift : leftRegular R G ⟶ kernel f := kernel.lift f g this
  use leftRegularHomEquiv (kernel f) lift
  rw [leftRegularHomEquiv_apply]
  change (lift ≫ kernel.ι f) (Finsupp.single 1 1) = m
  rw [kernel.lift_ι]
  convert (leftRegularHomEquiv_apply M₁ g).symm
  change m = M₁.leftRegularHomEquiv (M₁.leftRegularHomEquiv.symm m)
  rw [LinearEquiv.apply_symm_apply]


end Rep

/--
If `M` is a trivial representation of a finite group `G` and `M` is torsion-free
then `H¹(G,M) = 0`.
-/
lemma groupCohomology.H1_isZero_of_trivial (M : Rep R G) [NoZeroSMulDivisors ℕ M]
    [M.IsTrivial] [Finite G] : IsZero (H1 M) := by
  /-
  Since `M` is a trivial representation, we can identify `H¹(G,M)` with `Hom(G,M)`,
  which is zero if `G` is finite and `M` is torsion-free.

  This uses `groupCohomology.H1LequivOfIsTrivial`.
  -/
  refine IsZero.of_iso ?_ (groupCohomology.H1IsoOfIsTrivial M)
  have (f : (ModuleCat.of R (Additive G →+ ↑M.V))) : f = 0
  · ext g
    have : IsOfFinAddOrder (Additive.ofMul g)
    · exact isOfFinAddOrder_of_finite (Additive.ofMul g)
    obtain ⟨n, hpos, hn⟩ := IsOfFinAddOrder.exists_nsmul_eq_zero this
    have : n • f (Additive.ofMul g) = 0
    · simp [← AddMonoidHom.map_nsmul, hn]
    aesop
  have : Subsingleton (ModuleCat.of R (Additive G →+ ↑M.V))
  · exact subsingleton_of_forall_eq 0 this
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Additive G →+ ↑M.V))

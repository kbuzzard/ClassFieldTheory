module

public import Mathlib.Data.Finsupp.Single
-- public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Rep.Iso

@[expose] public noncomputable section

open CategoryTheory Limits ConcreteCategory

namespace Rep

universe w u v v'

variable {R : Type u} {G : Type v} {H : Type v'} [Ring R] [Monoid G] {A B : Rep.{w} R G}

-- TODO: Rename `of_ρ` to `ρ_of`
@[simp] lemma of_ρ' (M : Rep R G) : of M.ρ = M := rfl

lemma ρ_apply (g : G) : (leftRegular R G).ρ g = Finsupp.lmapDomain R R (g * ·) := rfl

lemma leftRegularHomEquiv_symm_comp {R : Type u} [CommRing R] {A B : Rep R G} (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f.hom a) := by
  ext g
  simp [leftRegularHomEquiv, homLinearEquiv, homEquiv, hom_comm_apply]

/--
If `f : M₁ ⟶ M₂` is a morphism in `Rep R G` and `f m = 0`, then
there exists `k : kernel f` such that `kernel.ι _ k = m`.
-/
lemma exists_kernelι_eq {R : Type u} [CommRing R] {M₁ M₂ : Rep.{max u v} R G} (f : M₁ ⟶ M₂)
    (m : M₁) (hm : f.hom m = 0) :
    ∃ k : kernel f (C := Rep R G), (kernel.ι f).hom k = m := by
  let g : leftRegular R G ⟶ M₁ := (leftRegularHomEquiv M₁).symm m
  have : g ≫ f = 0 := by rw [leftRegularHomEquiv_symm_comp]; ext1; rw [hm, map_zero]
  use leftRegularHomEquiv (kernel f) (kernel.lift f g this)
  simp [homEquiv, kernel.lift_ι_apply, g]

-- @[simp] lemma forget₂_map (f : A ⟶ B) : (forget₂ (Rep R G) (ModuleCat R)).map f = f.hom := rfl

end Rep

lemma _root_.Representation.norm_ofIsTrivial (R M G : Type*) [Group G] [Semiring R] [AddCommGroup M]
    [Module R M] [Fintype G] (ρ : Representation R G M) [ρ.IsTrivial] : ρ.norm = Nat.card G := by
  ext; simp [Representation.norm]

theorem _root_.range_eq_span {R : Type*} [CommSemiring R] (n : ℕ) :
    LinearMap.range (n : R →ₗ[R] R) = Ideal.span {(n : R)} := by
  ext x; simp [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_right, eq_comm]

open Finsupp

namespace Rep.leftRegular
universe u v


/-- If `g` is in the centre of `G` then the unique morphism of the left regular representation
which takes `1` to `g` is (as a linear map) `(leftRegular R G).ρ g`. -/
lemma leftRegularHom_eq_ρReg {R : Type u} {G : Type v} [Ring R] [Monoid G] (g : G)
    (hg : g ∈ Submonoid.center G) :
    ((leftRegular R G).leftRegularHom (.single g 1)).hom.toLinearMap = (leftRegular R G).ρ g := by
  ext
  simp [Submonoid.mem_center_iff.1 hg]

variable {R G : Type u} [Ring R] [Monoid G]
/-- The augmentation map from the left regular representation to the trivial module. -/
noncomputable abbrev ε (R G : Type u) [Ring R] [Monoid G] :
  leftRegular R G ⟶ trivial R G R := leftRegularHom (trivial R G R) (1 : R)

lemma ε_of_one : (ε R G) (.single 1 1) = (1 : R) := by simp

lemma ε_comp_ρ (g : G) : (ε R G).hom.toLinearMap ∘ₗ (leftRegular R G).ρ g =
    (ε R G).hom.toLinearMap := by
  ext; simp

open Representation.IntertwiningMap in
lemma ε_comp_ρ_apply (g : G) (v : G →₀ R) :
    (ε R G).hom ((leftRegular R G).ρ g v) = ε R G v := by
  rw [← toLinearMap_apply, ← LinearMap.comp_apply, ε_comp_ρ, toLinearMap_apply]

@[simp]
lemma ε_of (g : G) : (ε R G).hom (.single g 1) = (1 : R) := by simp

-- instance :
--     AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
--       (leftRegular R G) (trivial R G R) where
--   map_add f := map_add f.val
--   map_zero f := map_zero f.val

-- instance :
--     MulActionHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
--       R (leftRegular R G) (trivial R G R) where
  -- map_smulₛₗ f := map_smul f.val

lemma ε_eq_sum' (v : leftRegular R G) : (ε R G).hom v = ∑ x ∈ v.support, v x := by
  simp [Finsupp.sum]

lemma ε_eq_sum (v : leftRegular R G) [Fintype G] : (ε R G).hom v = ∑ g : G, v g := by
  refine ε_eq_sum' v|>.trans <| (finsum_eq_sum_of_support_subset v (by simp)).symm.trans ?_
  simp [finsum_eq_sum_of_fintype]

/--
The left regular representation is nontrivial (i.e. non-zero) if and only if the coefficient
ring is trivial.
-/
lemma nontrivial_iff_nontrivial : Nontrivial (leftRegular R G) ↔ Nontrivial R := by
  simp only [Finsupp.nontrivial_iff, and_iff_right_iff_imp]; infer_instance

lemma ε_epi : Epi (ε R G) := epi_of_surjective _ fun r ↦ ⟨r • .single 1 1, by simp⟩

end Rep.leftRegular

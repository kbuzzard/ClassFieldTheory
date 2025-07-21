import Mathlib
open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [Finite G] [DecidableEq G]

noncomputable section

namespace Representation
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

def norm : A →ₗ[R] A :=
  let _ := Fintype.ofFinite G
  ∑ g : G, ρ g

omit [DecidableEq G] in
lemma norm_comm (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := LinearMap.ext fun a ↦ by
  simp only [norm, LinearMap.coe_comp, coeFn_sum, Function.comp_apply, Finset.sum_apply, map_sum]
  simp_rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
  exact Finset.sum_equiv (Equiv.mulLeft g) (by simp) <| by simp

omit [DecidableEq G] in
lemma norm_comm' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := LinearMap.ext fun a ↦ by
  simp only [norm, LinearMap.coe_comp, coeFn_sum, Function.comp_apply, Finset.sum_apply]
  simp_rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
  exact Finset.sum_equiv (Equiv.mulRight g) (by simp) <| by simp

end Representation

namespace groupCohomology

open groupHomology

def _root_.Rep.norm (M : Rep R G) : M.V ⟶ M.V := ModuleCat.ofHom M.ρ.norm

/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
@[reducible]
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv

lemma TateNorm.def (M : Rep R G) :
    TateNorm M = (chainsIso₀ M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv := rfl

omit [DecidableEq G] in
@[simp]
lemma norm_comp_d_eq_zero (M : Rep R G) : M.norm ≫ (d₀₁ M) = 0 := by
  ext : 1
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, Rep.norm, ModuleCat.hom_ofHom]
  ext : 1
  simp only [LinearMap.comp_apply, zero_apply]
  rw [← LinearMap.mem_ker, d₀₁_ker_eq_invariants]
  simp only [Representation.mem_invariants]
  intro g
  rw [← LinearMap.comp_apply, Representation.norm_comm]

lemma TateNorm_comp_d (M : Rep R G) : TateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp only [ChainComplex.of_x, CochainComplex.of_x, TateNorm.def, Category.assoc, eq_d₀₁_comp_inv,
    Preadditive.IsIso.comp_left_eq_zero]
  simp [← Category.assoc]

omit [DecidableEq G] in
@[simp]
lemma comp_eq_zero' (M : Rep R G) : (groupHomology.d₁₀ M) ≫ M.norm = 0 := by
  ext1
  simp
  ext g m
  simp
  rw [d₁₀_single]
  simp [Rep.norm]
  rw [← LinearMap.comp_apply, Representation.norm_comm']
  simp

lemma d_comp_TateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ TateNorm M = 0 := by
  simp only [ChainComplex.of_x, CochainComplex.of_x, ← Category.assoc,
    Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq]

def TateComplex.ConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := TateNorm M
  comp_d₀ := d_comp_TateNorm M
  d₀_comp := TateNorm_comp_d M

def TateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (TateComplex.ConnectData M)

lemma TateComplex_d_neg_one (M : Rep R G) : (TateComplex M).d (-1) 0 = TateNorm M := rfl

lemma TateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (TateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma TateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (TateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map φ := {
    f
    | Int.ofNat i => ((cochainsFunctor R G).map φ).f ↑i
    | Int.negSucc i => (chainsMap (MonoidHom.id G) φ).f i
    comm' := fun i j ↦ by
      rintro rfl
      cases i
      · expose_names
        ext : 1
        simp only [TateComplex, TateComplex.ConnectData, Int.ofNat_eq_coe,
          CochainComplex.ConnectData.cochainComplex_X, CochainComplex.ConnectData.X_ofNat,
          CochainComplex.of_x, cochainsFunctor_obj, cochainsFunctor_map,
          CochainComplex.ConnectData.cochainComplex_d, ModuleCat.hom_comp,
          cochainsMap_id_f_hom_eq_compLeft]
        erw [CochainComplex.ConnectData.d_ofNat, CochainComplex.ConnectData.d_ofNat]
        simp only [CochainComplex.of_d]
        have : Nat.cast a + 1 = Int.ofNat (a + 1) := by norm_cast
        suffices ModuleCat.Hom.hom (inhomogeneousCochains.d Y a) ∘ₗ
          (ModuleCat.Hom.hom φ.hom).compLeft (Fin a → G) =
          ((cochainsMap (MonoidHom.id G) φ).f (a + 1)).hom ∘ₗ (inhomogeneousCochains.d X a).hom by
          rw [this]
          congr
        simp only [CochainComplex.of_x, cochainsMap_id_f_hom_eq_compLeft]
        apply LinearMap.ext
        intro v
        simp only [LinearMap.coe_comp, Function.comp_apply]
        ext i
        simp only [inhomogeneousCochains.d_hom_apply, compLeft_apply, Function.comp_apply, map_add,
          map_sum, map_smul, add_left_inj]
        exact Rep.hom_comm_apply _ _ _ |>.symm
      · expose_names
        if ha : a = 0 then
        subst ha
        simp [TateComplex, TateComplex.ConnectData]
        ext : 1
        simp only [ModuleCat.hom_comp, chainsMap_id_f_hom_eq_mapRange,
          cochainsMap_id_f_hom_eq_compLeft]
        apply LinearMap.ext
        intro v
        simp at v
        ext i
        simp at i
        simp [cochainsIso₀, chainsIso₀]

        sorry else
        sorry
  }
  map_id := sorry
  map_comp := sorry

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

instance TateComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ n (n + 1) rfl

def TateCohomology.iso_groupCohomology (n : ℕ) (M : Rep R G) :
    TateCohomology (n + 1) ≅ groupCohomology.functor R G (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology.iso_groupHomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (-n - 2)).obj M ≅ groupHomology M (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology_zero_iso (M : Rep R G) : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
  sorry

def TateCohomology_neg_one_iso (M : Rep R G) : (TateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
    (Submodule.span R (⋃ g : G, range (1 - M.ρ g))).submoduleOf (ker M.ρ.norm)) :=
  sorry

def TateCohomology_zero_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  sorry

def TateCohomology_neg_one_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (TateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)):=
  sorry

end groupCohomology
end

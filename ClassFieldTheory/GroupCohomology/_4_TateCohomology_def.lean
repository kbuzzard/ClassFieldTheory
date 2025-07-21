import Mathlib

open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

universe u v w

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G] [DecidableEq G]

noncomputable section

namespace Representation
variable {A : Type w} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

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

def _root_.groupHomology.zeroChainsIso (M : Rep.{u} R G) : (inhomogeneousChains M).X 0 ≅ M.V :=
  LinearEquiv.toModuleIso (Finsupp.LinearEquiv.finsuppUnique R (↑M.V) (Fin 0 → G))

def _root_.groupHomology.oneChainsIso (M : Rep R G) : (inhomogeneousChains M).X 1 ≅
    ModuleCat.of R (G →₀ M.V) :=
  LinearEquiv.toModuleIso <| Finsupp.mapDomain.linearEquiv _ _ <| Equiv.funUnique (Fin 1) G

def _root_.Rep.norm (M : Rep R G) : M.V ⟶ M.V := ModuleCat.ofHom M.ρ.norm

/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
@[reducible]
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv

omit [DecidableEq G] in
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

omit [DecidableEq G] in
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

omit [DecidableEq G] in
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

omit [DecidableEq G] in
lemma TateComplex_d_neg_one (M : Rep R G) : (TateComplex M).d (-1) 0 = TateNorm M := rfl

omit [DecidableEq G] in
lemma TateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (TateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

omit [DecidableEq G] in
lemma TateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (TateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

omit [DecidableEq G] in
lemma TateComplex.norm_comm (A B : Rep R G) (φ : A ⟶ B) :
    φ.hom ≫ B.norm = A.norm ≫ φ.hom := by
  ext1
  simp
  ext1 a
  simp
  conv_rhs =>
    simp [Rep.norm, Representation.norm];
    enter [2]; intro x; rw [Rep.hom_comm_apply]
  simp [Rep.norm, Representation.norm]

def TateComplex.norm' : End (forget₂ (Rep R G) (ModuleCat R)) where
  app M := M.norm
  naturality := TateComplex.norm_comm

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
        simp only [ModuleCat.hom_comp,
          cochainsMap_id_f_hom_eq_compLeft]
        apply LinearMap.ext
        intro v
        ext i
        simp [cochainsIso₀]
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
        erw [TateComplex.norm_comm]
        simp
        else
        simp
        have : Int.negSucc a + 1 = Int.negSucc (a - 1) := by
          simp [Int.negSucc_eq]
          conv_rhs => enter [2]; rw [Nat.cast_sub (by omega), neg_sub]
          rw [add_comm]; ring
        rw [this]
        simp [TateComplex]}
  map_comp f g := by
    ext _ _
    simp
    split
    · change _ = (ModuleCat.Hom.hom ((cochainsMap (MonoidHom.id G) g).f _) ∘ₗ
        (ModuleCat.Hom.hom ((cochainsMap (MonoidHom.id G) f).f _))) _
      exact congrFun rfl _
    · change _ = (ModuleCat.Hom.hom ((chainsMap (MonoidHom.id G) g).f _) ∘ₗ
        (ModuleCat.Hom.hom ((chainsMap (MonoidHom.id G) f).f _))) _
      refine congrFun ?_ _
      rw [← ModuleCat.hom_comp, chainsMap_id_comp]
      rfl

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

-- #synth groupCohomology
/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) := by

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

def TateCohomology.iso_groupCohomology (n : ℕ)  :
    TateCohomology.{u} (n + 1) ≅ groupCohomology.functor.{u} R G (n + 1) where
  hom := {
    app M := (CochainComplex.ConnectData.homologyIsoPos (TateComplex.ConnectData M) n
      (Int.ofNat n + 1) (by norm_num)).hom
    naturality {X Y} := by
      -- aesop
      sorry
  }
  inv := {
    app M := (CochainComplex.ConnectData.homologyIsoPos (TateComplex.ConnectData M) n
      (Int.ofNat n + 1) (by norm_num)).inv
    naturality := sorry
  }
  -- simp [groupCohomology.functor]

  -- -- sorry
  -- -- convert Iso.refl _
  -- -- sorry

def TateCohomology.iso_groupHomology (n : ℕ) :
    (TateCohomology (-n - 2)) ≅ groupHomology.functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ CochainComplex.ConnectData.homologyIsoNeg
    (TateComplex.ConnectData M) _ _ (by norm_num; rw [add_comm]; rfl)) <| fun {X Y} f ↦ by
    ext m
    simp



    sorry

-- def TateCohomology.isoGroupCohomology (n : ℕ) (M : Rep R G) :
--     (TateCohomology (n + 1)).obj M ≅ groupCohomology M (n + 1) := (isoGroupCohomology' n).app M

-- def TateCohomology.isoGroupHomology (n : ℕ) (M : Rep R G) :
--     (TateCohomology (-n - 2)).obj M ≅ groupHomology M (n + 1) :=  (isoGroupHomology' n).app M

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

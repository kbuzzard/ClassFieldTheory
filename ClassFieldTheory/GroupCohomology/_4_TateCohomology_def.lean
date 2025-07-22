import Mathlib
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

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

-- section ConnectData

-- variable {C : Type u} [Category.{v, u} C] [HasZeroMorphisms C]
--   {K : ChainComplex.{v, u} C ℕ} {L : CochainComplex C ℕ}

-- def ConnectDataFunctor (h : CochainComplex.ConnectData K L) :
--     Rep R G ⥤ CochainComplex.{v} (ModuleCat R) ℤ where
--   obj M := by
--     -- refine (CochainComplex.ConnectData.cochainComplex (C := C) (K := K) _)
--     sorry
--   map := sorry
--   map_id := sorry
--   map_comp := sorry

-- end ConnectData

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
lemma d₀₁_norm_eq_zero {M : Rep R G} (x : M.V) : d₀₁ M (M.norm x) = 0 :=
  congr($(norm_comp_d_eq_zero M) x)

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
@[simp]
lemma TateComplex_X (a : ℤ) (M : Rep R G) : (TateComplex M).X a =
  CochainComplex.ConnectData.X (inhomogeneousChains M) (inhomogeneousCochains M) a := rfl

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

section ConnectData

variable {C : Type u} [Category.{v, u} C] [HasZeroMorphisms C]
  {K : ChainComplex C ℕ} {L : CochainComplex C ℕ} (h : CochainComplex.ConnectData K L)
  {K' : ChainComplex C ℕ} {L' : CochainComplex C ℕ} (h' : CochainComplex.ConnectData K' L')
  (fK : K ⟶ K') (fL : L ⟶ L') (f_comm : fK.f 0 ≫ h'.d₀ = h.d₀ ≫ fL.f 0)

@[simps]
def _root_.CochainComplex.ConnectData.map : h.cochainComplex ⟶ h'.cochainComplex where
  f
    | Int.ofNat n => fL.f _
    | Int.negSucc n => fK.f _
  comm' := fun i j ↦ by
    rintro rfl
    obtain i | (_ | i) := i
    · exact fL.comm _ _
    · simpa
    · exact fK.comm _ _

open CochainComplex.ConnectData in
lemma _root_.CochainComplex.ConnectData.map_id : h.map h (𝟙 K) (𝟙 L) (by simp) = 𝟙 _ := by
  ext m
  obtain m | (_ | m) := m
  · simp
  · simp only [Int.reduceNegSucc, cochainComplex_X, Int.reduceNeg, X_negOne, map_f,
      HomologicalComplex.id_f]; rfl
  · simp

open HomologicalComplex in
lemma _root_.CochainComplex.ConnectData.homologyMap_map_eq_pos (n : ℕ) (m : ℤ) (hmn : m = n + 1)
    [HasHomology h.cochainComplex m] [HasHomology L (n + 1)]
    [HasHomology h'.cochainComplex m] [HasHomology L' (n + 1)] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoPos n m hmn).hom ≫ homologyMap fL (n + 1) ≫ (h'.homologyIsoPos n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [CochainComplex.ConnectData.homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = ↑(n + 1) := hmn
  simp [CochainComplex.ConnectData.map, -Int.natCast_add]

open HomologicalComplex in
lemma _root_.CochainComplex.ConnectData.homologyMap_map_eq_neg (n : ℕ) (m : ℤ) (hmn : m = -↑(n + 2))
    [HasHomology h.cochainComplex m] [HasHomology K (n + 1)]
    [HasHomology h'.cochainComplex m] [HasHomology K' (n + 1)] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoNeg n m hmn).hom ≫ homologyMap fK (n + 1) ≫ (h'.homologyIsoNeg n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [CochainComplex.ConnectData.homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  obtain rfl : m = .negSucc (n + 1) := hmn
  simp [CochainComplex.ConnectData.map, -Int.natCast_add]

-- open HomologicalComplex in
-- lemma _root_.CochainComplex.ConnectData.zero_iso :
--     homologyMap (h.cochainComplex)

end ConnectData

@[reducible]
def TateComplex.map {X Y : Rep R G} (φ : X ⟶ Y) : (TateComplex X ⟶ TateComplex Y) :=
  CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsFunctor R G |>.map φ)
    <| by
      simp
      ext1
      ext g1 x g2
      simp [TateComplex.ConnectData, cochainsIso₀, chainsIso₀]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
      erw [TateComplex.norm_comm]
      simp

omit [DecidableEq G] in
@[simp]
lemma TateComplex.map_zero {X Y : Rep R G} : TateComplex.map (X := X) (Y := Y) 0 = 0 := by
  aesop_cat

@[simps]
def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map := TateComplex.map

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

section Exact

instance : (TateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero X Y := by simp

def TateComplex.eval_nonneg (n : ℕ) :
    TateComplexFunctor ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n ≅
    cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n :=
  NatIso.ofComponents
    (fun M ↦ by
      simp only [Functor.comp_obj, TateComplexFunctor_obj, HomologicalComplex.eval_obj,
        CochainComplex.of_x, cochainsFunctor_obj]
      exact Iso.refl (ModuleCat.of R ((Fin n → G) → ↑M.V)))
    (by simp only [Functor.comp_obj, TateComplexFunctor_obj, TateComplex,
      HomologicalComplex.eval_obj, CochainComplex.ConnectData.cochainComplex_X,
      CochainComplex.ConnectData.X_ofNat, CochainComplex.of_x, cochainsFunctor_obj,
      Functor.comp_map, TateComplexFunctor_map, HomologicalComplex.eval_map,
      CochainComplex.ConnectData.map_f, cochainsFunctor_map, id_eq, Iso.refl_hom, Category.comp_id,
      Category.id_comp, implies_true])

def TateComplex.eval_neg (n : ℕ) :
    TateComplexFunctor ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (.negSucc n) ≅
    chainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n :=
  NatIso.ofComponents
  (fun M ↦ by
    simp only [Functor.comp_obj, TateComplexFunctor_obj, HomologicalComplex.eval_obj,
      ChainComplex.of_x, chainsFunctor_obj]
    exact Iso.refl (ModuleCat.of R ((Fin n → G) →₀ ↑M.V)))
  (by simp [TateComplex])

omit [Finite G] [DecidableEq G] in
open ShortComplex in
lemma _root_.groupCohomology.map_cochainsFunctor_eval_shortExact
    (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact
    (X.map (cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)) :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (C := ModuleCat R) (X.map (cochainsFunctor R G))).mp
      (map_cochainsFunctor_shortExact hX) n

omit [Finite G] [DecidableEq G] in
open ShortComplex in
lemma _root_.groupHomology.map_chainsFunctor_eval_shortExact
    (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact
    (X.map (chainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)) :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (C := ModuleCat R) (X.map (chainsFunctor R G))).mp
      (map_chainsFunctor_shortExact hX) n


/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) where
  preservesFiniteLimits J _ _ := HomologicalComplex.preservesLimitsOfShape_of_eval _ <| fun i ↦ by

    --simp [TateComplexFunctor]
    sorry

instance TateComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

omit [DecidableEq G] in
lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

end Exact

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ n (n + 1) rfl

def TateCohomology.iso_groupCohomology (n : ℕ)  :
    TateCohomology.{u} (n + 1) ≅ groupCohomology.functor.{u} R G (n + 1) :=
  NatIso.ofComponents
  (fun M ↦ (TateComplex.ConnectData M).homologyIsoPos _ _ (by norm_num)) <| fun {X Y} f ↦ by
  simp only [TateCohomology, TateComplexFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, functor_obj, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, functor_map]
  rw [CochainComplex.ConnectData.homologyMap_map_eq_pos (m := n + 1) (n := n) (hmn := rfl)]
  simp

def TateCohomology.iso_groupHomology (n : ℕ) :
    (TateCohomology (-n - 2)) ≅ groupHomology.functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ CochainComplex.ConnectData.homologyIsoNeg
    (TateComplex.ConnectData M) _ _ (by norm_num; rw [add_comm]; rfl)) <| fun {X Y} f ↦ by
    simp only [TateCohomology, TateComplexFunctor, Functor.comp_obj,
      HomologicalComplex.homologyFunctor_obj, groupHomology.functor_obj, Functor.comp_map,
      HomologicalComplex.homologyFunctor_map, groupHomology.functor_map]
    rw [CochainComplex.ConnectData.homologyMap_map_eq_neg (m := _) (n := n) (hmn := by omega)]
    simp

namespace TateCohomology.zeroIso

variable (M : Rep R G)

@[simps] def sc : ShortComplex (ModuleCat R) where
  X₁ := M.V
  X₂ := M.V
  X₃ := ModuleCat.of R (G → M.V)
  f := M.norm
  g := groupCohomology.d₀₁ M
  zero := norm_comp_d_eq_zero M

@[simps!] def isoShortComplexH0 :
    (TateComplex M).sc 0 ≅ sc M :=
  (TateComplex M).isoSc' (.negSucc 0) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      (by simp [TateComplex_d_neg_one])
      (comp_d₀₁_eq M)

end TateCohomology.zeroIso

def TateCohomology.zeroIso (M : Rep R G) : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := calc
  (TateCohomology 0).obj M
    ≅ (zeroIso.sc M).homology := ShortComplex.homologyMapIso (zeroIso.isoShortComplexH0 M)
  _ ≅ ModuleCat.of R (ker (groupCohomology.d₀₁ M).hom ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := by
    refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (d₀₁_ker_eq_invariants M)) ?_).toModuleIso
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩; exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩; exact ⟨⟨M.norm y, d₀₁_norm_eq_zero y⟩, ⟨_, rfl⟩, rfl⟩

namespace TateCohomology.negOneIso

variable (M : Rep R G)

@[simps] def sc : ShortComplex (ModuleCat R) :=
  .mk (groupHomology.d₁₀ M) M.norm (comp_eq_zero' M)

@[simps!] def isoShortComplexHneg1 :
    (TateComplex M).sc (-1) ≅ sc M :=
  (TateComplex M).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₁ M) (chainsIso₀ M) (cochainsIso₀ M)
      (groupHomology.comp_d₁₀_eq M)
      (by simp [sc, TateComplex, TateComplex.ConnectData])

end TateCohomology.negOneIso

def TateCohomology.negOneIso (M : Rep R G) : (TateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
    (Submodule.span R (⋃ g : G, range (1 - M.ρ g))).submoduleOf (ker M.ρ.norm)) := calc
  (TateCohomology (-1)).obj M
    ≅ (negOneIso.sc M).homology := ShortComplex.homologyMapIso (negOneIso.isoShortComplexHneg1 M)
  _ ≅ ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ _ := by
    refine (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ rfl) ?_).toModuleIso
    refine Submodule.ext fun ⟨m, hm⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨(y : G →₀ M.V), rfl⟩, hy⟩;
      simp [Submodule.submoduleOf, ShortComplex.moduleCatToCycles, Subtype.ext_iff] at hy ⊢
      clear hm
      rw [← Finsupp.sum_single y] at hy
      rw [← hy]
      erw [map_sum]
      refine Submodule.sum_mem _ <| fun g hi ↦ ?_
      rw [d₁₀_single]
      refine Submodule.subset_span <| by simp; exact ⟨g⁻¹, -(y g), by simp; abel⟩
    · rintro h
      simp [Submodule.submoduleOf] at h ⊢
      simp [Subtype.ext_iff]
      refine Submodule.span_induction ?_ ?_ ?_ ?_ h
      · rintro x ⟨y', ⟨g, hg⟩, hy'2⟩
        simp [ShortComplex.moduleCatToCycles]
        change ∃ (y : G →₀ M.V), (d₁₀ M).hom y = _
        simp at hg
        rw [hg.symm] at hy'2
        obtain ⟨z, hz⟩ := hy'2
        use Finsupp.single g⁻¹ (-z)
        rw [d₁₀_single, inv_inv, sub_neg_eq_add, hz.symm, add_comm, LinearMap.sub_apply]
        simp [sub_eq_add_neg]
      · exact ⟨0, by simp; erw [map_zero]⟩
      · rintro x y hx hy ⟨z1, hz1⟩ ⟨z2, hz2⟩
        exact ⟨z1 + z2, by erw [map_add, ← hz1, ← hz2]; rfl⟩
      · rintro r m hm ⟨y, hy⟩
        exact ⟨r • y, by erw [map_smul, ← hy]; rfl⟩

def TateCohomology_zero_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  haveI eq1 : M.ρ.invariants = ⊤ := Representation.invariants_eq_top M.ρ
  TateCohomology.zeroIso M ≪≫
  (LinearEquiv.toModuleIso <| Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ eq1|>.trans
    Submodule.topEquiv) <| by
  refine Submodule.ext fun x ↦ ⟨fun ⟨⟨m, hm1⟩, hm2, hm3⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rw [eq1] at hm1
    simp at hm2 hm3
    rw [hm3.symm]
    obtain ⟨k, hk⟩ := hm2
    exact ⟨k, by simpa [Fintype.card_eq_nat_card, Representation.norm] using hk⟩
  · simp [← hk, Submodule.submoduleOf, Representation.norm, Fintype.card_eq_nat_card])

def TateCohomology_neg_one_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (TateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)):=
  haveI eq1 : LinearMap.ker M.ρ.norm = LinearMap.ker (Nat.card G : M.V →ₗ[R] M.V) := by
    ext m ; simp [Representation.norm, Fintype.card_eq_nat_card]
  TateCohomology.negOneIso M ≪≫
  (LinearEquiv.toModuleIso (eq1 ▸ Submodule.quotEquivOfEqBot _ (by
  ext m; simp [Submodule.submoduleOf, ← Module.End.one_eq_id])))

end groupCohomology
end

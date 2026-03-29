module

public import ClassFieldTheory.Cohomology.Functors.Restriction
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import
  ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public
  import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
public import Mathlib.Algebra.Homology.Embedding.Connect

@[expose] public noncomputable section

open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

universe u v w

variable {R G H : Type u} [CommRing R] [Group G] [Fintype G] [Group H] [Fintype H]

namespace groupCohomology

/-- This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`. -/
def tateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv

-- FIXME: `@[simps!] def tateNorm` produces a lemma mentioning `ModuleCat.Hom.hom'`!
-- We are missing `initialize_simps_projections ModuleCat (hom' → hom)`
@[simp] lemma tateNorm_hom_apply (M : Rep R G) (x : (Fin 0 → G) →₀ ↑M.V) (y : Fin 0 → G) :
    (tateNorm M).hom x y = (cochainsIso₀ M).inv.hom (M.ρ.norm <| (chainsIso₀ M).hom.hom x) y := rfl

set_option backward.isDefEq.respectTransparency false in
lemma tateNorm_eq (M : Rep R G) :
    tateNorm M = ModuleCat.ofHom (Finsupp.lsum R fun _ ↦ LinearMap.pi fun _ ↦ M.ρ.norm) := by
  ext
  simp only [CochainComplex.of_x, tateNorm, ChainComplex.of_x, chainsIso₀,
    LinearEquiv.toModuleIso_hom, Rep.norm, cochainsIso₀, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, hom_ofHom, coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_symm_apply, Function.comp_apply, Finsupp.lsingle_apply,
    Finsupp.LinearEquiv.finsuppUnique_apply, AddEquiv.funUnique_symm_apply,
    Finsupp.lsum_comp_lsingle, pi_apply]
  congr
  simp only [Finsupp.single_apply, ite_eq_left_iff]
  exact fun h ↦ False.elim <| h <| Unique.eq_default _

@[reassoc (attr := simp), elementwise]
lemma norm_comp_d_eq_zero (M : Rep R G) : M.norm.toModuleCatHom ≫ d₀₁ M = 0 := by
  ext1
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, Rep.norm, ModuleCat.hom_ofHom]
  ext1
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [← LinearMap.mem_ker, d₀₁_ker_eq_invariants]
  intro g
  simp

set_option backward.isDefEq.respectTransparency false in
lemma tateNorm_comp_d (M : Rep R G) : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp [tateNorm]

@[simp]
lemma comp_eq_zero (M : Rep R G) : d₁₀ M ≫ M.norm.toModuleCatHom = 0 := by
  ext
  simp [d₁₀_single M, Rep.norm, ← LinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in
lemma d_comp_tateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ tateNorm M = 0 := by
  simp only [ChainComplex.of_x, CochainComplex.of_x, tateNorm, ← Category.assoc]
  simp [← comp_d₁₀_eq]

/-- The Tate norm connecting complexes of inhomogeneous chains and cochains. -/
@[simps]
def tateComplexConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := tateNorm M
  comp_d₀ := d_comp_tateNorm _
  d₀_comp := tateNorm_comp_d _

/-- The Tate complex defined by connecting inhomogeneous chains and cochains with the Tate norm. -/
@[simps! X]
def tateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

lemma tateComplex_d_neg_one (M : Rep R G) : (tateComplex M).d (-1) 0 = tateNorm M := by rfl

lemma tateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (tateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma tateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (tateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

@[reassoc]
lemma tateComplex.norm_comm {A B : Rep R G} (φ : A ⟶ B) : φ ≫ B.norm = A.norm ≫ φ := by
  ext
  simp [Rep.norm_comm]

@[reassoc]
lemma tateComplex.norm_hom_comm {A B : Rep R G} (φ : A ⟶ B) :
    φ.toModuleCatHom ≫ B.norm.toModuleCatHom = A.norm.toModuleCatHom ≫ φ.toModuleCatHom := by
  rw [← ModuleCat.ofHom_comp, ← Representation.IntertwiningMap.comp_toLinearMap,
    ← Rep.hom_comp, A.norm_comm φ]
  simp

def tateComplex.normNatEnd : End (forget₂ (Rep R G) (ModuleCat R)) where
  app M := M.norm.toModuleCatHom
  naturality _ _ := tateComplex.norm_hom_comm

set_option backward.isDefEq.respectTransparency false in
/-- The chain map on the Tate complex induced by a morphism of representations. -/
@[reducible]
def tateComplex.map {X Y : Rep R G} (φ : X ⟶ Y) : tateComplex X ⟶ tateComplex Y := by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsFunctor R G |>.map φ) ?_
  ext
  simp [tateComplexConnectData_d₀, tateNorm_eq, Representation.norm, hom_comm_apply]

@[simp]
lemma tateComplex.map_zero {X Y : Rep R G} : tateComplex.map (X := X) (Y := Y) 0 = 0 := by aesop_cat

set_option backward.isDefEq.respectTransparency false in
/-- The functor taking a representation of `G` to its Tate complex. -/
@[simps]
def tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := tateComplex M
  map := tateComplex.map

/-- The functor taking a representation of `G` to its `n`-th Tate cohomology group. -/
def tateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  tateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

namespace TateCohomology

section Exact

set_option backward.isDefEq.respectTransparency false in
instance : (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero X Y := by simp

/-- The natural isomorphism between the `n`-th index of the Tate complex and inhomogeneous
  `n`-cochains for `0 ≤ n`. -/
def tateComplex.eval_nonneg (n : ℕ) :
    tateComplexFunctor ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n ≅
    cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n :=
  .refl _

/-- The natural isomorphism between the `n`-th index of the Tate complex and inhomogeneous
  `n`-chains for `n < 0`. -/
def tateComplex.eval_neg (n : ℕ) :
    tateComplexFunctor ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (.negSucc n) ≅
    chainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n :=
  .refl _

instance : (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero X Y := by
    ext
    simp_rw [tateComplexFunctor]
    aesop_cat

lemma map_tateComplexFunctor_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact) :
    (S.map tateComplexFunctor).ShortExact := by
  simp_rw [HomologicalComplex.shortExact_iff_degreewise_shortExact, ← ShortComplex.map_comp]
  rintro (_ | _)
  · exact .map_of_natIso _ (tateComplex.eval_nonneg _).symm <|
      map_cochainsFunctor_eval_shortExact _ hS
  · exact .map_of_natIso _ (tateComplex.eval_neg _).symm <| map_chainsFunctor_eval_shortExact _ hS

instance : (tateComplexFunctor (R := R) (G := G)).Additive where

/-
The next two statements say that `tateComplexFunctor` is an exact functor.
-/
instance preservesFiniteLimits_tateComplexFunctor :
    PreservesFiniteLimits (tateComplexFunctor (R := R) (G := G)) :=
  (((tateComplexFunctor (R := R) (G := G)).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ map_tateComplexFunctor_shortExact).1

instance preservesFiniteColimits_tateComplexFunctor :
    PreservesFiniteColimits (tateComplexFunctor (R := R) (G := G)) :=
  (((tateComplexFunctor (R := R) (G := G)).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ map_tateComplexFunctor_shortExact).2

end Exact

/-- The connecting homomorphism in group cohomology induced by a short exact sequence
  of `G`-modules. -/
noncomputable abbrev δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (tateCohomology n).obj S.X₃ ⟶ (tateCohomology (n + 1)).obj S.X₁ :=
  (map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

lemma map_δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (tateCohomology n).map S.g ≫ δ hS n = 0 :=
  (map_tateComplexFunctor_shortExact hS).comp_δ _ _ _

lemma δ_map {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    δ hS n ≫ (tateCohomology (n + 1)).map S.f = 0 :=
  (map_tateComplexFunctor_shortExact hS).δ_comp _ _ _

lemma exact₃ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk _ _ (map_δ hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₃ ..

lemma exact₁ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk _ _ (δ_map hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₁ ..

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the `n`-th Tate cohomology and `n`-th group cohomology for `n : ℕ`
non-zero. -/
def isoGroupCohomology (n : ℕ) [NeZero n] :
    tateCohomology.{u} n ≅ groupCohomology.functor.{u} R G n :=
  NatIso.ofComponents (fun M ↦ (tateComplexConnectData M).homologyIsoPos _ _ rfl) fun {X Y} f ↦ by
    simp [tateCohomology, CochainComplex.ConnectData.homologyMap_map_of_eq_succ (n := n)]

set_option backward.isDefEq.respectTransparency false in

/-- The isomorphism between the `-n-1`-th Tate cohomology and `n`-th group homology for `n : ℕ`
non-zero. -/
def isoGroupHomology (m : ℤ) (n : ℕ) (hmn : m = -↑(n + 1)) [NeZero n] :
    tateCohomology m ≅ groupHomology.functor R G n :=
  NatIso.ofComponents (fun M ↦ (tateComplexConnectData M).homologyIsoNeg _ _ hmn) fun {X Y} f ↦ by
    simp [tateCohomology, CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ (hmn := hmn)]

set_option backward.isDefEq.respectTransparency false in
noncomputable abbrev cochainsMap {M : Rep R G} {N : Rep R H} (e : G ≃* H) (φ : M ⟶ N ↓ e) :
    (tateComplexConnectData M).cochainComplex ⟶ (tateComplexConnectData N).cochainComplex := by
  refine CochainComplex.ConnectData.map (tateComplexConnectData M) (tateComplexConnectData N)
    (groupHomology.chainsMap e φ)
    (groupCohomology.cochainsMap e.symm.toMonoidHom (Rep.ofHom ⟨φ.hom.toLinearMap, fun h ↦ by
      simp [φ.hom.2]⟩)) ?_
  ext f0 (m : M)
  simpa [tateNorm_eq, cochainsMap_f, map_zero, Finsupp.sum_single_index, compLeft_apply,
    funLeft_apply, Representation.norm, hom_comm_apply φ _ m] using
    Finset.sum_equiv e.symm (by simp) (by simp)

lemma cochainsMap_comp {Q : Type u} [Group Q] [Fintype Q] {M : Rep R G} {N : Rep R H} {P : Rep R Q}
    (e1 : G ≃* H) (e2 : H ≃* Q) (φ : M ⟶ N ↓ e1) (ψ : N ⟶ P ↓ e2) :
    cochainsMap (e1.trans e2) (φ ≫ (resFunctor e1.toMonoidHom|>.map ψ)) =
      cochainsMap e1 φ ≫ cochainsMap e2 ψ := by
  rw [CochainComplex.ConnectData.map_comp_map]
  unfold cochainsMap
  simp only [MulEquiv.coe_monoidHom_trans, MulEquiv.toMonoidHom_eq_coe,
    Representation.IntertwiningMap.coe_eq_toLinearMap, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap]
  congr
  simp [← chainsMap_comp]

lemma cochinasMap_id {M : Rep R G} : cochainsMap (MulEquiv.refl G) (𝟙 M) = 𝟙 _ := by
  rw [← CochainComplex.ConnectData.map_id]
  unfold cochainsMap
  congr
  simp [← chainsMap_id]

noncomputable abbrev map {M : Rep R G} {N : Rep R H} (e : G ≃* H) (φ : M ⟶ N ↓ e) (n : ℤ) :
    (tateCohomology n).obj M ⟶ (tateCohomology n).obj N :=
  HomologicalComplex.homologyMap (cochainsMap e φ) _

set_option backward.isDefEq.respectTransparency false in
lemma map_comp {Q : Type u} [Group Q] [Fintype Q] {M : Rep R G} {N : Rep R H} {P : Rep R Q}
    (e1 : G ≃* H) (e2 : H ≃* Q) (φ : M ⟶ N ↓ e1) (ψ : N ⟶ P ↓ e2) (n : ℤ) :
    map (e1.trans e2) (φ ≫ (resFunctor e1.toMonoidHom|>.map ψ)) n =
      map e1 φ n ≫ map e2 ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

lemma map_id {M : Rep R G} (n : ℤ) :
    map (MulEquiv.refl G) (𝟙 M) n = 𝟙 ((tateCohomology n).obj M) := by
  unfold map
  simp [cochinasMap_id, tateCohomology, tateComplex]

lemma map_congr {M : Rep R G} {N : Rep R H} {e1 e2 : G ≃* H} (he : e1 = e2) {φ : M ⟶ N ↓ e1}
    {ψ : M ⟶ N ↓ e2} (h : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℤ) :
    map e1 φ n = map e2 ψ n := by
  subst he
  congr
  simp [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff, h]

set_option backward.isDefEq.respectTransparency false in
noncomputable def res_iso {M : Rep R G} (e : G ≃* H) {N : Rep R H} (e' : M.V ≃ₗ[R] N.V)
    (he' : ∀ (g : G), e' ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ e') (n : ℤ) :
    (tateCohomology n).obj M ≅ (tateCohomology n).obj N where
  hom := map e (Rep.ofHom ⟨e', by simp [he']⟩) n
  inv := map e.symm (Rep.ofHom ⟨e'.symm, e.surjective.forall.mpr <| fun g ↦ by
      apply_fun (fun f ↦ e'.toLinearMap ∘ₗ f ∘ₗ e'.toLinearMap) using fun _ _ h ↦
        e'.eq_comp_toLinearMap_iff _ _|>.1 <| e'.comp_toLinearMap_eq_iff _ _|>.1 h
      simp [LinearMap.comp_assoc, he']⟩) n
  hom_inv_id := by
    rw [← map_comp, ← map_id]
    exact map_congr e.self_trans_symm (by simp) n
  inv_hom_id := by
    rw [← map_comp, ← map_id]
    exact map_congr e.symm_trans_self (by simp) n

variable (M : Rep R G)

namespace zeroIso

/-- The concrete short complex computing `0`-th Tate cohomology. -/
@[simps] def sc : ShortComplex (ModuleCat R) :=
  .mk M.norm.toModuleCatHom (d₀₁ M) (norm_comp_d_eq_zero M)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the concrete short complex computing `0`-th Tate cohomology
  and the corresponding parts of the Tate complex. -/
@[simps!] def isoShortComplexH0 :
    (tateComplex M).sc 0 ≅ sc M :=
  (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (by exact chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      (by simp [tateComplex_d_neg_one, tateNorm]) (comp_d₀₁_eq M)

end zeroIso

/-- A concrete description of `0`-th Tate cohomology
  as the quotient of invariants by the image of the norm. -/
def zeroIso (M : Rep R G) : (tateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := calc
  (tateCohomology 0).obj M
    ≅ (zeroIso.sc M).homology := ShortComplex.homologyMapIso (zeroIso.isoShortComplexH0 M)
  _ ≅ ModuleCat.of R (LinearMap.ker (groupCohomology.d₀₁ M).hom ⧸ _) :=
    ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := by
    refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (d₀₁_ker_eq_invariants M)) ?_).toModuleIso
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩; exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩; exact ⟨⟨M.norm.hom y, norm_comp_d_eq_zero_apply _ y⟩, ⟨_, rfl⟩, rfl⟩

namespace negOneIso

variable (M : Rep R G)

/-- The concrete short complex computing `-1`-st Tate cohomology. -/
@[simps] def sc : ShortComplex (ModuleCat R) :=
  .mk (d₁₀ M) M.norm.toModuleCatHom (comp_eq_zero M)

/-- The isomorphism between the concrete short complex computing `-1`-st Tate cohomology
and the corresponding parts of the Tate complex. -/
@[simps!] def isoShortComplexHneg1 :
    (tateComplex M).sc (-1) ≅ sc M :=
  (tateComplex M).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₁ M) (chainsIso₀ M) (cochainsIso₀ M)
      (groupHomology.comp_d₁₀_eq M)
      (by simp [sc, tateComplex, tateNorm])

end negOneIso

set_option backward.isDefEq.respectTransparency false in
/-- A concrete description of the `-1`-st Tate cohomology group
as the quotient of the kernel of the norm by the kernel of the coinvariants. -/
def negOneIso (M : Rep R G) :
    (tateCohomology (-1)).obj M ≅
      ModuleCat.of R (ker M.ρ.norm ⧸
        (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) := calc
  (tateCohomology (-1)).obj M
    ≅ (negOneIso.sc M).homology := ShortComplex.homologyMapIso (negOneIso.isoShortComplexHneg1 M)
  _ ≅ ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ _ := by
    refine (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ rfl) ?_).toModuleIso
    apply Submodule.map_injective_of_injective (f := (LinearMap.ker _).subtype)
      Subtype.val_injective
    rw [← range_d₁₀_eq_coinvariantsKer, Submodule.submoduleOf, Submodule.map_comap_eq_of_le,
      ← Submodule.map_comp, ← LinearMap.range_comp]
    · rfl
    · simpa [LinearMap.range_le_iff_comap, ← ker_comp, -comp_eq_zero] using
        congr(($(comp_eq_zero M)).hom)

variable [M.ρ.IsTrivial] {n : ℤ} {N : ℕ}

/-- A concrete description of the `0`-th Tate cohomology of a trivial representation. -/
def zeroIsoOfIsTrivial :
    (tateCohomology 0).obj M ≅ .of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  haveI eq1 : M.ρ.invariants = ⊤ := Representation.invariants_eq_top M.ρ
  TateCohomology.zeroIso M ≪≫
  (LinearEquiv.toModuleIso <| Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ eq1 |>.trans
    Submodule.topEquiv) <| by
  refine Submodule.ext fun x ↦ ⟨fun ⟨⟨m, hm1⟩, hm2, hm3⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rw [eq1] at hm1
    simp only [SetLike.mem_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Submodule.topEquiv_apply, LinearEquiv.coe_ofEq_apply] at hm2 hm3
    rw [hm3.symm]
    obtain ⟨k, hk⟩ := hm2
    exact ⟨k, by simpa [Representation.norm] using hk⟩
  · simp [← hk, Submodule.submoduleOf, Representation.norm])

/-- A concrete description of the `-1`-st Tate cohomology of a trivial representation. -/
def negOneIsoOfIsTrivial :
    (tateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)) :=
  TateCohomology.negOneIso M ≪≫
  (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ (by
  ext m; simp [Submodule.submoduleOf, ← Module.End.one_eq_id, Representation.Coinvariants.ker]) ≪≫ₗ
  LinearEquiv.ofEq _ _ (by ext m; simp [Representation.norm])))

variable {G : Type} [Group G] [Fintype G]

/-- The zeroth Tate cohomology of a trivial representation of a finite group of order `N` is `ℤ/Nℤ`.
-/
def zeroTrivialInt (hG : Nat.card G = N) :
    (tateCohomology 0).obj (trivial ℤ G ℤ) ≅ .of ℤ (ZMod N) := by
  refine zeroIsoOfIsTrivial _ ≪≫ ((QuotientAddGroup.quotientAddEquivOfEq ?_).trans <|
    Int.quotientZMultiplesEquivZMod N).toIntLinearEquiv.toModuleIso
  ext
  simp [AddSubgroup.mem_zmultiples_iff, ← hG, mul_comm]

/-- A trivial torsion-free representation of a finite group of order `N` has trivial -1-st Tate
cohomology. -/
lemma isZero_neg_one_trivial_of_isAddTorsionFree {M : Type} [AddCommGroup M] [IsAddTorsionFree M] :
    IsZero ((tateCohomology (-1)).obj <| trivial ℤ G M) :=
  .of_iso (by simp [subsingleton_iff]) <| negOneIsoOfIsTrivial _

end groupCohomology.TateCohomology
end

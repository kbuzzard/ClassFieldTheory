module

public import ClassFieldTheory.Cohomology.Functors.Restriction
public import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

@[expose] public noncomputable section

open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

universe u v w

-- TODO: upstream
lemma Submodule.mem_submoduleOf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} {x : q} : x ∈ p.submoduleOf q ↔ (x : M) ∈ p :=
  Iff.rfl

variable {R G H : Type u} [CommRing R] [Group G] [Fintype G] [Group H] [Fintype H]

namespace TateCohomology

/-- The Tate norm composed with `cochainsIso₀` is `chainsIso₀` composed with the norm map. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma _root_.Rep.tateNorm_comp_cochainsIso₀_hom (M : Rep R G) :
    M.tateNorm ≫ (cochainsIso₀ M).hom = (chainsIso₀ M).hom ≫ M.norm.asHom.toModuleCatHom := by
  simp [Rep.tateNorm]

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
  simp only [MulEquiv.toMonoidHom_trans, MulEquiv.toMonoidHom_eq_coe, Rep.hom_comp,
    Representation.IntertwiningMap.comp_toLinearMap]
  congr
  simp [← chainsMap_comp]

lemma cochinasMap_id {M : Rep R G} : cochainsMap (MulEquiv.refl G) (𝟙 M) = 𝟙 _ := by
  rw [← CochainComplex.ConnectData.map_id]
  unfold cochainsMap
  congr
  simp [← chainsMap_id]

noncomputable abbrev map {M : Rep R G} {N : Rep R H} (e : G ≃* H) (φ : M ⟶ N ↓ e) (n : ℤ) :
    tateCohomology M n ⟶ tateCohomology N n :=
  HomologicalComplex.homologyMap (cochainsMap e φ) _

attribute [local implicit_reducible] tateCohomologyFunctor tateComplexFunctor
  HomologicalComplex.homologyFunctor in
lemma map_comp {Q : Type u} [Group Q] [Fintype Q] {M : Rep R G} {N : Rep R H} {P : Rep R Q}
    (e1 : G ≃* H) (e2 : H ≃* Q) (φ : M ⟶ N ↓ e1) (ψ : N ⟶ P ↓ e2) (n : ℤ) :
    map (e1.trans e2) (φ ≫ (resFunctor e1.toMonoidHom|>.map ψ)) n =
      map e1 φ n ≫ map e2 ψ n := by
  unfold map
  rw [cochainsMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ _

attribute [local implicit_reducible] tateCohomologyFunctor tateComplexFunctor
  HomologicalComplex.homologyFunctor in
lemma map_id {M : Rep R G} (n : ℤ) :
    map (MulEquiv.refl G) (𝟙 M) n = 𝟙 (tateCohomology M n) := by
  unfold map
  rw [cochinasMap_id]
  exact HomologicalComplex.homologyMap_id _ _

lemma map_congr {M : Rep R G} {N : Rep R H} {e1 e2 : G ≃* H} (he : e1 = e2) {φ : M ⟶ N ↓ e1}
    {ψ : M ⟶ N ↓ e2} (h : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : ℤ) :
    map e1 φ n = map e2 ψ n := by
  subst he
  congr
  simp [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff, h]

noncomputable def res_iso {M : Rep R G} (e : G ≃* H) {N : Rep R H} (e' : M.V ≃ₗ[R] N.V)
    (he' : ∀ (g : G), e' ∘ₗ M.ρ g = N.ρ (e g) ∘ₗ e') (n : ℤ) :
    tateCohomology M n ≅ tateCohomology N n where
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
  .mk M.norm.asHom.toModuleCatHom (d₀₁ M) (norm_comp_d_eq_zero M)

attribute [local implicit_reducible] CochainComplex.ConnectData.cochainComplex
  CochainComplex.ConnectData.X CochainComplex.ConnectData.d tateComplexConnectData sc in
/-- The isomorphism between the concrete short complex computing `0`-th Tate cohomology
  and the corresponding parts of the Tate complex. -/
@[simps!] def isoShortComplexH0 :
    (tateComplex M).sc 0 ≅ sc M :=
  (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (by exact chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      (Rep.tateNorm_comp_cochainsIso₀_hom M).symm (comp_d₀₁_eq M)

end zeroIso

/-- A concrete description of `0`-th Tate cohomology
  as the quotient of invariants by the image of the norm. -/
def zeroIso (M : Rep R G) : tateCohomology M 0 ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := calc
  tateCohomology M 0
    ≅ (zeroIso.sc M).homology := ShortComplex.homologyMapIso (zeroIso.isoShortComplexH0 M)
  _ ≅ ModuleCat.of R (LinearMap.ker (groupCohomology.d₀₁ M).hom ⧸ _) :=
    ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := by
    refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (d₀₁_ker_eq_invariants M)) ?_).toModuleIso
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩; exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩; exact ⟨⟨M.norm.asHom.hom y, norm_comp_d_eq_zero_apply _ y⟩, ⟨_, rfl⟩, rfl⟩

namespace negOneIso

variable (M : Rep R G)

/-- The concrete short complex computing `-1`-st Tate cohomology. -/
@[simps] def sc : ShortComplex (ModuleCat R) :=
  .mk (d₁₀ M) M.norm.asHom.toModuleCatHom (comp_eq_zero M)

/-- The isomorphism between the concrete short complex computing `-1`-st Tate cohomology
and the corresponding parts of the Tate complex. -/
@[simps!] def isoShortComplexHneg1 :
    (tateComplex M).sc (-1) ≅ sc M :=
  (tateComplex M).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₁ M) (chainsIso₀ M) (cochainsIso₀ M)
      (groupHomology.comp_d₁₀_eq M)
      (Rep.tateNorm_comp_cochainsIso₀_hom M).symm

end negOneIso

attribute [local implicit_reducible] negOneIso.sc Rep.norm in
/-- A concrete description of the `-1`-st Tate cohomology group
as the quotient of the kernel of the norm by the kernel of the coinvariants. -/
def negOneIso (M : Rep R G) :
    tateCohomology M (-1) ≅
      ModuleCat.of R (ker M.ρ.norm ⧸
        (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) := calc
  tateCohomology M (-1)
    ≅ (negOneIso.sc M).homology := ShortComplex.homologyMapIso (negOneIso.isoShortComplexHneg1 M)
  _ ≅ ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ _ := by
    refine (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ rfl) ?_).toModuleIso
    rw [← range_d₁₀_eq_coinvariantsKer]
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ?_
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_submoduleOf]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      exact ⟨y, by simpa [Subtype.ext_iff] using hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, by simp [Subtype.ext_iff]⟩

variable [M.ρ.IsTrivial] {n : ℤ} {N : ℕ}

/-- A concrete description of the `0`-th Tate cohomology of a trivial representation. -/
def zeroIsoOfIsTrivial :
    tateCohomology M 0 ≅ .of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
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
    exact ⟨k, by simpa [Representation.norm, Representation.isTrivial_apply] using hk⟩
  · simp [← hk, Submodule.submoduleOf, Representation.norm, Representation.isTrivial_apply])

/-- A concrete description of the `-1`-st Tate cohomology of a trivial representation. -/
def negOneIsoOfIsTrivial :
    tateCohomology M (-1) ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)) :=
  TateCohomology.negOneIso M ≪≫
  (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ (by
  ext m; simp [Submodule.submoduleOf, Representation.Coinvariants.ker,
    Representation.isTrivial_apply]) ≪≫ₗ
  LinearEquiv.ofEq _ _ (by ext m; simp [Representation.norm, Representation.isTrivial_apply])))

variable {G : Type} [Group G] [Fintype G]

/-- The zeroth Tate cohomology of a trivial representation of a finite group of order `N` is `ℤ/Nℤ`.
-/
def zeroTrivialInt (hG : Nat.card G = N) :
    tateCohomology (trivial ℤ G ℤ) 0 ≅ .of ℤ (ZMod N) := by
  refine zeroIsoOfIsTrivial _ ≪≫ ((QuotientAddGroup.quotientAddEquivOfEq ?_).trans <|
    Int.quotientZMultiplesEquivZMod N).toIntLinearEquiv.toModuleIso
  ext
  simp [AddSubgroup.mem_zmultiples_iff, ← hG, mul_comm]

/-- A trivial torsion-free representation of a finite group of order `N` has trivial -1-st Tate
cohomology. -/
lemma isZero_neg_one_trivial_of_isAddTorsionFree {M : Type} [AddCommGroup M] [IsAddTorsionFree M] :
    IsZero (tateCohomology (trivial ℤ G M) (-1)) :=
  .of_iso (by simp [subsingleton_iff]) <| negOneIsoOfIsTrivial _

end TateCohomology

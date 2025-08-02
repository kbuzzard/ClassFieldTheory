import ClassFieldTheory.Mathlib.Algebra.Homology.Embedding.Connect
import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.Basic
import ClassFieldTheory.Mathlib.Algebra.Homology.ShortComplex.ShortExact
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
variable {G : Type u} [Group G] [Finite G]

noncomputable section

namespace Representation
variable {A : Type w} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

/-- The linear endomorphism of `A : Representation R G` for a finite group `G`
  defined as `a ↦ ∑ g : G, g • a`. -/
def norm : A →ₗ[R] A :=
  let _ := Fintype.ofFinite G
  ∑ g : G, ρ g

lemma norm_comm (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := LinearMap.ext fun a ↦ by
  simp only [norm, LinearMap.coe_comp, coeFn_sum, Function.comp_apply, Finset.sum_apply, map_sum]
  simp_rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
  exact Finset.sum_equiv (Equiv.mulLeft g) (by simp) <| by simp

@[simp]
lemma norm_comm_apply (g : G) (a : A) :
    ρ g (ρ.norm a) = ρ.norm a := by
  rw [← LinearMap.comp_apply, norm_comm ρ g]

lemma norm_comm' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := LinearMap.ext fun a ↦ by
  simp only [norm, LinearMap.coe_comp, coeFn_sum, Function.comp_apply, Finset.sum_apply]
  simp_rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
  exact Finset.sum_equiv (Equiv.mulRight g) (by simp) <| by simp

@[simp]
lemma norm_comm_apply' (g : G) (a : A) :
    ρ.norm (ρ g a) = ρ.norm a := by
  rw [← LinearMap.comp_apply, norm_comm' ρ g]

end Representation

namespace groupCohomology

/-- The linear endomorphism of `M.V` defined as `m ↦ ∑ g : G, M.ρ g m`. It's the bundled version
  of `Representation.norm`. -/
def _root_.Rep.norm (M : Rep R G) : M.V ⟶ M.V := ModuleCat.ofHom M.ρ.norm

variable [Fintype G] (A : Rep R G) in
/-- Given a representation `A` of a finite group `G`, this is the representation morphism `A ⟶ A`
defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
@[simps]
def norm : A ⟶ A where
  hom := ModuleCat.ofHom <| Representation.norm A.ρ
  comm g := by ext; simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ρ_hom, LinearMap.coe_comp,
    Function.comp_apply]; rw [← LinearMap.comp_apply, Representation.norm_comm' A.ρ g,
    ← LinearMap.comp_apply, Representation.norm_comm A.ρ g]

@[reassoc, elementwise]
lemma norm_comm {A B : Rep R G} (f : A ⟶ B) :
    f ≫ norm B = norm A ≫ f := by
  ext
  simp [Representation.norm, hom_comm_apply]

/-- This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`. -/
def tateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv

lemma tateNorm_eq (M : Rep R G) :
    (ModuleCat.ofHom <| Finsupp.lsum R <| fun _ ↦ LinearMap.pi fun _ ↦ M.norm.hom) =
    tateNorm M := by
  ext
  simp only [Rep.norm, ModuleCat.hom_ofHom, Finsupp.lsum_comp_lsingle, pi_apply, ChainComplex.of_x,
    CochainComplex.of_x, chainsIso₀, LinearEquiv.toModuleIso_hom, cochainsIso₀,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_symm_apply, Function.comp_apply, Finsupp.lsingle_apply,
    Finsupp.LinearEquiv.finsuppUnique_apply, uniqueElim_const, tateNorm]
  congr
  simp only [Finsupp.single_apply, left_eq_ite_iff]
  exact fun h ↦ False.elim <| h <| Unique.eq_default _

@[reassoc (attr := simp), elementwise]
lemma norm_comp_d_eq_zero (M : Rep R G) : M.norm ≫ d₀₁ M = 0 := by
  ext1
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, Rep.norm, ModuleCat.hom_ofHom]
  ext1
  simp only [LinearMap.comp_apply, zero_apply]
  rw [← LinearMap.mem_ker, d₀₁_ker_eq_invariants]
  simp only [Representation.mem_invariants]
  intro g
  rw [← LinearMap.comp_apply, Representation.norm_comm]

lemma tateNorm_comp_d (M : Rep R G) : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp [tateNorm]

@[simp]
lemma comp_eq_zero (M : Rep R G) : d₁₀ M ≫ M.norm = 0 := by
  ext
  simp [d₁₀_single M, Rep.norm, ← LinearMap.comp_apply, Representation.norm_comm']

lemma d_comp_tateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ tateNorm M = 0 := by
  simp only [ChainComplex.of_x, CochainComplex.of_x, tateNorm, ← Category.assoc,
    Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq]

/-- The Tate norm connecting complexes of inhomogeneous chains and cochains. -/
@[simps]
def tateComplexConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := ModuleCat.ofHom <| Finsupp.lsum R <| fun _ ↦ LinearMap.pi fun _ ↦ M.norm.hom
  comp_d₀ := tateNorm_eq M ▸ d_comp_tateNorm _
  d₀_comp := tateNorm_eq M ▸ tateNorm_comp_d _

/-- The Tate complex defined by connecting inhomogeneous chains and cochains with the Tate norm. -/
@[simps! X]
def tateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

lemma tateComplex_d_neg_one (M : Rep R G) : (tateComplex M).d (-1) 0 = tateNorm M := by
  rw [← tateNorm_eq]
  rfl

lemma tateComplexConnecDate_d₀_eq (M : Rep R G) :
    (tateComplexConnectData M).d₀ = tateNorm M := by rw [← tateNorm_eq]; rfl

lemma tateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (tateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma tateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (tateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

@[reassoc]
lemma tateComplex.norm_comm {A B : Rep R G} (φ : A ⟶ B) : φ.hom ≫ B.norm = A.norm ≫ φ.hom := by
  ext
  simp [Rep.norm, Representation.norm, Rep.hom_comm_apply]

def tateComplex.normNatEnd : End (forget₂ (Rep R G) (ModuleCat R)) where
  app M := M.norm
  naturality _ _ := tateComplex.norm_comm

/-- The chain map on the Tate complex induced by a morphism of representations. -/
@[reducible]
def tateComplex.map {X Y : Rep R G} (φ : X ⟶ Y) : (tateComplex X ⟶ tateComplex Y) :=
  CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsFunctor R G |>.map φ) <| by
    simp [tateComplexConnectData_d₀, tateNorm_eq, tateNorm, tateComplex.norm_comm_assoc (B := Y)]
    rfl

@[simp]
lemma tateComplex.map_zero {X Y : Rep R G} : tateComplex.map (X := X) (Y := Y) 0 = 0 := by aesop_cat

/-- The functor taking a representation of `G` to its Tate complex. -/
@[simps]
def tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := tateComplex M
  map := tateComplex.map

/-- The functor taking a representation of `G` to its `n`-th Tate cohomology group. -/
def tateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  tateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

section Exact

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

omit [Finite G] in
open ShortComplex in
lemma _root_.groupCohomology.map_cochainsFunctor_eval_shortExact
    (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact
    (X.map (cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)) :=
  (map_cochainsFunctor_shortExact hX).map_of_exact
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)

omit [Finite G] in
open ShortComplex in
lemma _root_.groupHomology.map_chainsFunctor_eval_shortExact
    (n : ℕ) {X : ShortComplex (Rep R G)} (hX : ShortExact X) :
    ShortExact
    (X.map (chainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)) :=
  (map_chainsFunctor_shortExact hX).map_of_exact
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)

lemma tateCohomology.map_tateComplexFunctor_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map tateComplexFunctor).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  rw [← ShortComplex.map_comp]
  cases i
  · apply ShortComplex.shortExact_map_of_natIso _ (tateComplex.eval_nonneg _).symm
    exact map_cochainsFunctor_eval_shortExact _ hS
  apply ShortComplex.shortExact_map_of_natIso _ (tateComplex.eval_neg _).symm
  exact map_chainsFunctor_eval_shortExact _ hS

instance : (tateComplexFunctor (R := R) (G := G)).Additive where

/-
The next two statements say that `tateComplexFunctor` is an exact functor.
-/
instance preservesFiniteLimits_tateComplexFunctor :
    PreservesFiniteLimits (tateComplexFunctor (R := R) (G := G)) :=
  (((tateComplexFunctor (R := R) (G := G)).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ tateCohomology.map_tateComplexFunctor_shortExact).1

instance preservesFiniteColimits_tateComplexFunctor :
    PreservesFiniteColimits (tateComplexFunctor (R := R) (G := G)) :=
  (((tateComplexFunctor (R := R) (G := G)).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ tateCohomology.map_tateComplexFunctor_shortExact).2

end Exact

/-- The connecting homomorphism in group cohomology induced by a short exact sequence
  of `G`-modules. -/
noncomputable abbrev tateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (tateCohomology n).obj S.X₃ ⟶ (tateCohomology (n + 1)).obj S.X₁ :=
  (tateCohomology.map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

/-- The isomorphism between `n+1`-th Tate cohomology and `n+1`-th group cohomology for `n : ℕ`. -/
def tateCohomology.isoGroupCohomology (n : ℕ)  :
    tateCohomology.{u} (n + 1) ≅ groupCohomology.functor.{u} R G (n + 1) :=
  NatIso.ofComponents
  (fun M ↦ (tateComplexConnectData M).homologyIsoPos _ _ (by norm_num)) fun {X Y} f ↦ by
  simp only [tateCohomology, tateComplexFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, functor_obj, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, functor_map]
  rw [CochainComplex.ConnectData.homologyMap_map_eq_pos (m := n + 1) (n := n) (hmn := rfl)]
  simp

/-- The isomorphism between `-n-2`-th Tate cohomology and `n+1`-th group homology for `n : ℕ`. -/
def tateCohomology.isoGroupHomology (n : ℕ) :
    (tateCohomology (-n - 2)) ≅ groupHomology.functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ CochainComplex.ConnectData.homologyIsoNeg
    (tateComplexConnectData M) _ _ (by grind)) fun {X Y} f ↦ by
    simp only [tateCohomology, tateComplexFunctor, Functor.comp_obj,
      HomologicalComplex.homologyFunctor_obj, groupHomology.functor_obj, Functor.comp_map,
      HomologicalComplex.homologyFunctor_map, groupHomology.functor_map]
    rw [CochainComplex.ConnectData.homologyMap_map_eq_neg (m := _) (n := n) (hmn := by omega)]
    simp

namespace tateCohomology.zeroIso

variable (M : Rep R G)

/-- The concrete short complex computing `0`-th Tate cohomology.-/
@[simps] private def sc : ShortComplex (ModuleCat R) :=
    .mk M.norm (d₀₁ M) (norm_comp_d_eq_zero M)

/-- The isomorphism between the concrete short complex computing `0`-th Tate cohomology
  and the corresponding parts of the Tate complex. -/
@[simps!] private def isoShortComplexH0 :
    (tateComplex M).sc 0 ≅ sc M :=
  (tateComplex M).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (by exact chainsIso₀ M) (cochainsIso₀ M) (cochainsIso₁ M)
      (by simp [tateComplex_d_neg_one, tateNorm]) (comp_d₀₁_eq M)

end tateCohomology.zeroIso

/-- A concrete description of `0`-th Tate cohomology
  as the quotient of invariants by the image of the norm.-/
def tateCohomology.zeroIso (M : Rep R G) : (tateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := calc
  (tateCohomology 0).obj M
    ≅ (zeroIso.sc M).homology := ShortComplex.homologyMapIso (zeroIso.isoShortComplexH0 M)
  _ ≅ ModuleCat.of R (ker (groupCohomology.d₀₁ M).hom ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) := by
    refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (d₀₁_ker_eq_invariants M)) ?_).toModuleIso
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩; exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩; exact ⟨⟨M.norm y, norm_comp_d_eq_zero_apply _ y⟩, ⟨_, rfl⟩, rfl⟩

namespace tateCohomology.negOneIso

variable (M : Rep R G)

/-- The concrete short complex computing `-1`-th Tate cohomology.-/
@[simps] private def sc : ShortComplex (ModuleCat R) :=
  .mk (d₁₀ M) M.norm (comp_eq_zero M)

/-- The isomorphism between the concrete short complex computing `-1`-th Tate cohomology
  and the corresponding parts of the Tate complex. -/
@[simps!] private def isoShortComplexHneg1 :
    (tateComplex M).sc (-1) ≅ sc M :=
  (tateComplex M).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₁ M) (chainsIso₀ M) (cochainsIso₀ M)
      (groupHomology.comp_d₁₀_eq M)
      (by simp [sc, tateComplex, tateNorm_eq, tateNorm])

end tateCohomology.negOneIso

/-- A concrete description of `0`-th Tate cohomology
  as the quotient of the kernel of the norm by the kernel of the coinvariants.-/
def tateCohomology.negOneIso (M : Rep R G) : (tateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) := calc
  (tateCohomology (-1)).obj M
    ≅ (negOneIso.sc M).homology := ShortComplex.homologyMapIso (negOneIso.isoShortComplexHneg1 M)
  _ ≅ ModuleCat.of R (LinearMap.ker M.ρ.norm ⧸ _) := ShortComplex.moduleCatHomologyIso _
  _ ≅ _ := by
    refine (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ rfl) ?_).toModuleIso
    apply Submodule.map_injective_of_injective (f := (ker _).subtype) Subtype.val_injective
    rw [← range_d₁₀_eq_coinvariantsKer, Submodule.submoduleOf, Submodule.map_comap_eq_of_le,
      ← Submodule.map_coe_toLinearMap (F := _ ≃ₗ[R] _), ← Submodule.map_comp,
      ← LinearMap.range_comp]
    · rfl
    · simpa [LinearMap.range_le_iff_comap, ← ker_comp, -comp_eq_zero] using
        congr(($(comp_eq_zero M)).hom)

/-- A concrete description of the `0`-th Tate cohomology of a trivial representation. -/
def tateCohomology.zeroIsoOfIsTrivial (M : Rep R G) [M.ρ.IsTrivial] : (tateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  haveI eq1 : M.ρ.invariants = ⊤ := Representation.invariants_eq_top M.ρ
  tateCohomology.zeroIso M ≪≫
  (LinearEquiv.toModuleIso <| Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ eq1 |>.trans
    Submodule.topEquiv) <| by
  refine Submodule.ext fun x ↦ ⟨fun ⟨⟨m, hm1⟩, hm2, hm3⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rw [eq1] at hm1
    simp at hm2 hm3
    rw [hm3.symm]
    obtain ⟨k, hk⟩ := hm2
    exact ⟨k, by simpa [Fintype.card_eq_nat_card, Representation.norm] using hk⟩
  · simp [← hk, Submodule.submoduleOf, Representation.norm, Fintype.card_eq_nat_card])

/-- A concrete description of the `-1`-th Tate cohomology of a trivial representation. -/
def tateCohomology.negOneIsoOfIsTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (tateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)) :=
  tateCohomology.negOneIso M ≪≫
  (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ (by
  ext m; simp [Submodule.submoduleOf, ← Module.End.one_eq_id, Representation.Coinvariants.ker]) ≪≫ₗ
  LinearEquiv.ofEq _ _ (by ext m; simp [Representation.norm, Fintype.card_eq_nat_card])))

end groupCohomology
end

import ClassFieldTheory.GroupCohomology.«06_LeftRegular»
import ClassFieldTheory.GroupCohomology.«07_coind1_and_ind1»
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»
import ClassFieldTheory.Mathlib.Algebra.Homology.ImageToKernel
import ClassFieldTheory.Mathlib.CategoryTheory.Abelian.Exact
import ClassFieldTheory.Mathlib.ModuleCatExact
import ClassFieldTheory.Mathlib.CategoryTheory.Abelian.Images

/-!
Let `M : Rep R G`, where `G` is a finite cyclic group.
We construct an exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

Using this sequence, we construct an isomorphism

  `dimensionShift.up.obj M ≅ dimensionShift.down.obj M`.

Using this, construct isomorphisms

  `Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)`.

-/

open
  Finsupp
  Rep
  leftRegular
  dimensionShift
  CategoryTheory
  Abelian
  ConcreteCategory
  Limits
  BigOperators
  groupCohomology

-- TODO: add universes
variable {R : Type} [CommRing R]
variable (G : Type) [Group G] [instCyclic : IsCyclic G]
variable (M : Rep R G)

noncomputable section

namespace IsCyclic
/--
`gen G` is a generator of the cyclic group `G`.
-/
def gen : G := IsCyclic.exists_generator.choose

variable {G} in
lemma gen_generate (x : G) : x ∈ Subgroup.zpowers (gen G) :=
  IsCyclic.exists_generator.choose_spec x

theorem unique_gen_zpow_zmod [Fintype G] (x : G) :
    ∃! n : ZMod (Fintype.card G), x = gen G ^ n.val :=
  IsCyclic.unique_zpow_zmod gen_generate x

theorem unique_gen_pow [Fintype G] (x : G) :
    ∃! n < Fintype.card G, x = gen G ^ n := by
  obtain ⟨k, hk, hk_unique⟩ := unique_gen_zpow_zmod G x
  refine ⟨k.val, ⟨⟨ZMod.val_lt _, hk⟩, ?_⟩⟩
  intro y ⟨hy_lt, hy⟩
  rw [← hk_unique y]
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy_lt]
  · simp [hy]

end IsCyclic

open IsCyclic

variable {G} [Fintype G] (M : Rep R G)

@[simp] lemma ofHom_sub (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ - f₂) : A ⟶ B) = ofHom f₁ - ofHom f₂ := rfl

@[simp] lemma ofHom_add (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ + f₂) : A ⟶ B) = ofHom f₁ + ofHom f₂ := rfl

@[simp] lemma ofHom_zero (A B : ModuleCat R) :
  (ofHom 0 : A ⟶ B) = 0 := rfl

@[simp] lemma ofHom_one (A : ModuleCat R) :
  (ofHom 1 : A ⟶ A) = 𝟙 A := rfl

omit [IsCyclic G] [Fintype G] in
@[simp] lemma Rep.ρ_mul_eq_comp (M : Rep R G) (x y : G) :
    Action.ρ M (x * y) = (Action.ρ M y) ≫ (Action.ρ M x) := map_mul (Action.ρ M) x y

namespace Representation

variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

omit [Fintype G] --[DecidableEq G]

@[simps] def map₁ : (G → A) →ₗ[R] (G → A) where
  toFun f x := f x - f ((gen G)⁻¹ * x)
  map_add' _ _ := by
    ext; simp [add_sub_add_comm]
  map_smul' _ _ := by
    ext; simp [← smul_sub]

lemma map₁_comm (g : G) :
    map₁ ∘ₗ ρ.coind₁' g = ρ.coind₁' g ∘ₗ map₁  := by
  apply LinearMap.ext
  intro
  apply funext
  intro
  simp [mul_assoc]

lemma map₁_comp_coind_ι :
    map₁ (R := R) (G := G) (A := A) ∘ₗ coind₁'_ι = 0 := by
  ext; simp

lemma map₁_ker :
    LinearMap.ker (map₁ (R := R) (G := G) (A := A)) = LinearMap.range coind₁'_ι := by
  ext f
  constructor
  · intro hf
    rw [LinearMap.mem_ker] at hf
    simp only [coind₁'_ι, LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk, ] at hf ⊢
    use f (gen G)⁻¹
    ext x
    obtain ⟨n, hx⟩ : x ∈ Subgroup.zpowers (gen G) := IsCyclic.exists_generator.choose_spec x
    dsimp at hx
    rw [Function.const_apply, ← hx]
    dsimp [map₁] at hf
    induction n generalizing x with
    | zero =>
        rw [zpow_zero]
        have := congr_fun hf 1
        simp only [mul_one, Pi.zero_apply] at this
        rw [sub_eq_zero] at this
        exact this.symm
    | succ n hn =>
      have := congr_fun hf ((gen G ^ ((n : ℤ) + 1)))
      simp only [Pi.zero_apply, sub_eq_zero] at this
      rw [this, hn _ rfl]
      group
    | pred n hn =>
      have := congr_fun hf ((gen G ^ (- (n : ℤ))))
      simp only [Pi.zero_apply, sub_eq_zero] at this
      rw [zpow_sub_one (gen G) _, hn _ rfl, this]
      group
  · rintro ⟨_, rfl⟩
    exact LinearMap.congr_fun map₁_comp_coind_ι _

@[simps!] def map₂ : (G →₀ A) →ₗ[R] (G →₀ A) :=
  LinearMap.id - lmapDomain _ _ (fun x ↦ gen G * x)

omit [Fintype G] in
lemma map₂_apply (f : G →₀ A) (x : G) :
    Representation.map₂ (R := R) f x = f x - f ((gen G)⁻¹ * x) := by
  simp [Representation.map₂]
  convert Finsupp.mapDomain_apply ?_ _ ((gen G)⁻¹ * x)
  · simp
  · intro x y h
    simpa using h

omit [Fintype G] in
@[simp] lemma map₂_comp_lsingle (x : G) :
    map₂ (R := R) (G := G) (A := A) ∘ₗ lsingle x = lsingle x - lsingle (gen G * x) := by
  ext
  simp [map₂, LinearMap.sub_comp]

lemma map₂_comm (g : G) :
    map₂ ∘ₗ ρ.ind₁' g = ρ.ind₁' g ∘ₗ map₂ := by
  ext x : 1
  rw [LinearMap.comp_assoc, ind₁'_comp_lsingle, LinearMap.comp_assoc, map₂_comp_lsingle,
    LinearMap.comp_sub, ind₁'_comp_lsingle, ←LinearMap.comp_assoc, map₂_comp_lsingle,
    LinearMap.sub_comp, ind₁'_comp_lsingle, mul_assoc]

lemma ind₁'_π_comp_map₂ :
    ind₁'_π ∘ₗ map₂ (R := R) (G := G) (A := A) = 0 := by
  ext : 1
  rw [LinearMap.comp_assoc, map₂_comp_lsingle, LinearMap.comp_sub,
    LinearMap.zero_comp, sub_eq_zero, ind₁'_π_comp_lsingle, ind₁'_π_comp_lsingle]

lemma map₂_range [Fintype G] [DecidableEq G] :
    LinearMap.range (map₂ (R := R) (G := G) (A := A)) = LinearMap.ker ind₁'_π := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    have := ind₁'_π_comp_map₂ (R := R) (G := G) (A := A)
    apply_fun (· y) at this
    exact this
  · intro hw_ker
    let f : G → A := fun g ↦ ∑ i ∈ Finset.Icc 0 (unique_gen_pow G g).choose, w (gen G ^ i)
    have hf_apply (k : ℤ) : f (gen G ^ k) = ∑ i ∈ Finset.Icc 0 (k.natMod (Fintype.card G)),
        w (gen G ^ i) := by
      simp only [f]
      congr
      rw [((unique_gen_pow G (gen G ^ k)).choose_spec.right (k.natMod (Fintype.card G))
        ⟨?_, ?_⟩).symm]
      · exact  Int.natMod_lt Fintype.card_ne_zero
      · simp [← zpow_natCast, Int.natMod, Int.ofNat_toNat, Int.emod_nonneg]
    have hf_apply_of_lt (k : ℕ) (hk : k < Fintype.card G) :
        f (gen G ^ k) = ∑ i ∈ Finset.Icc 0 k, w (gen G ^ i) := by
      convert hf_apply k
      · simp
      · zify
        rw [Int.natMod, Int.toNat_of_nonneg, Int.emod_eq_of_lt]
        · positivity
        · exact_mod_cast hk
        · apply Int.emod_nonneg
          simp
    use equivFunOnFinite.symm f
    ext g
    rw [map₂_apply]
    change f g - f ((gen G)⁻¹ * g) = w g
    obtain ⟨k, ⟨hk_lt, rfl⟩, hk_unique⟩ := unique_gen_pow G g
    by_cases hk : k = 0
    · rw [hk, hf_apply_of_lt, pow_zero, mul_one]
      · have : (gen G)⁻¹ = gen G ^ (Fintype.card G - 1 : ℕ) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel Fintype.card_pos,
            pow_card_eq_one]
        rw [this, hf_apply_of_lt]
        · simp only [Finset.Icc_self, Finset.sum_singleton, pow_zero, sub_eq_self]
          calc
          _ = ∑ i ∈ Finset.Ico 0 (Fintype.card G), w (gen G ^ i) := by
            congr
            apply Finset.Icc_sub_one_right_eq_Ico_of_not_isMin
            rw [isMin_iff_forall_not_lt]
            push_neg
            use 0, Fintype.card_pos
          _ = ∑ x ∈ (Finset.Ico 0 (Fintype.card G)).image (gen G ^ ·), w x := by
            rw [Finset.sum_image]
            intro x hx y hy h
            simp only [Nat.Ico_zero_eq_range, Finset.coe_range, Set.mem_Iio] at hx hy h
            simp only at hk_unique
            have := (unique_gen_pow G (gen G ^ x)).choose_spec.right
            rw [this x, this y]
            · simp only [hy, h, and_self]
            · simp only [hx, and_self]
          _ = ∑ x ∈ (Finset.univ : Finset G), w x := by
            congr
            rw [Finset.eq_univ_iff_forall]
            intro x
            simp only [Nat.Ico_zero_eq_range, Finset.mem_image, Finset.mem_range]
            obtain ⟨a, ha, ha'⟩ := unique_gen_pow G x
            use a, ha.left, ha.right.symm
          _ = 0 := by
            simpa [Finsupp.sum_fintype] using hw_ker
        · simpa using Fintype.card_pos
      · exact Fintype.card_pos
    · rw [← zpow_neg_one, hf_apply_of_lt, ← zpow_natCast, ← zpow_add, neg_add_eq_sub,
        show (k : ℤ) - 1 = (k - 1 : ℕ) by omega, zpow_natCast, hf_apply_of_lt]
      · nth_rw 1 [show k = k - 1 + 1 by omega]
        rw [Finset.sum_Icc_succ_top, add_sub_cancel_left, zpow_natCast,
          Nat.sub_add_cancel (by omega)]
        omega
      all_goals omega

end Representation

namespace Rep

/--
The map `coind₁'.obj M ⟶ coind₁' M` which takes a function `f : G → M.V` to
`x ↦ f x - f ((gen G)⁻¹ * x)`.
-/
def map₁ : coind₁' (R := R) (G := G) ⟶ coind₁' where
  app M := {
    hom := ofHom Representation.map₁
    comm _ := by
      ext : 1
      exact Representation.map₁_comm _ _
  }
  naturality _ _ _ := by
    ext v
    dsimp only [Representation.map₁, coind₁']
    ext x
    simp

omit [Fintype G] in
lemma coind_ι_gg_map₁_app : coind₁'_ι.app M ≫ map₁.app M = 0 := by
  ext : 2
  exact Representation.map₁_comp_coind_ι

omit [Fintype G] in
lemma coind_ι_gg_map₁ : coind₁'_ι ≫ map₁ (R := R) (G := G) = 0 := by
  ext : 2
  exact coind_ι_gg_map₁_app _

def map₂ : ind₁' (R := R) (G := G) ⟶ ind₁' where
  app M := {
    hom := ofHom Representation.map₂
    comm g := by
      ext : 1
      exact Representation.map₂_comm _ _
  }
  naturality X Y f:= by
    ext (w : G →₀ X.V)
    simp only [Action.comp_hom, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply]
    change (_ : G →₀ _) = _
    ext g
    simp [ind₁', Representation.map₂_apply, -Representation.map₂_apply_toFun]

omit [Fintype G] in
lemma map₂_app_gg_ind₁'_π_app :  map₂.app M ≫ ind₁'_π.app M = 0 := by
  ext : 2
  exact Representation.ind₁'_π_comp_map₂

omit [Fintype G] in
lemma map₂_gg_ind₁'_π : map₂ (R := R) (G := G) ≫ ind₁'_π = 0 := by
  ext : 2
  exact map₂_app_gg_ind₁'_π_app _

/--
Let `M` be a representation of a finite cyclic group `G`.
Then the following square commutes

  ` coind₁'.obj M -------> coind₁'.obj M `
  `      |                      |        `
  `      |                      |        `
  `      ↓                      ↓        `
  `   ind₁'.obj M ------->   ind₁'.obj M `

The vertical maps are the canonical isomorphism `ind₁'_iso_coind₁`
and the horizontal maps are `map₁` and `map₂`.
-/
lemma map₁_comp_ind₁'_iso_coind₁' :
    map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv = (ind₁'_iso_coind₁'.app M).inv ≫ map₂.app M := by
  ext x
  simp [coind₁', ind₁'] at x ⊢
  ext d
  simp only [ind₁'_iso_coind₁', Representation.ind₁'_lequiv_coind₁', linearEquivFunOnFinite,
    Equiv.invFun_as_coe, ModuleCat.hom_ofHom, map₁, Representation.map₁, LinearMap.coe_mk,
    AddHom.coe_mk, LinearEquiv.coe_coe, LinearEquiv.coe_symm_mk, equivFunOnFinite_symm_apply_toFun,
    map₂, Representation.map₂_apply]

/-- The first short complex in the periodicity sequence. -/
@[simps] def periodSeq₁ : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := coind₁'.obj M
  X₃ := ind₁'.obj M
  f := coind₁'_ι.app M
  g := map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv
  zero := by simp [reassoc_of% coind_ι_gg_map₁_app]

/-- The second short complex in the periodicity sequence. -/
@[simps] def periodSeq₂ : ShortComplex (Rep R G) where
  X₁ := coind₁'.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv
  g := ind₁'_π.app M
  zero := by
    rw [ Category.assoc, reassoc_of% map₁_comp_ind₁'_iso_coind₁']; simp [map₂_app_gg_ind₁'_π_app]

/-- The first short complex in the periodicity sequence as a functor. -/
@[simps] def periodSeq₁Functor : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := periodSeq₁
  map {M N} f := ShortComplex.homMk f (coind₁'.map f) (ind₁'.map f) (by cat_disch) (by cat_disch)

/-- The second short complex in the periodicity sequence as a functor. -/
@[simps] def periodSeq₂Functor : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := periodSeq₂
  map {M N} f := ShortComplex.homMk (coind₁'.map f) (ind₁'.map f) f (by cat_disch) (by cat_disch)

lemma exact_periodSeq₁ : (periodSeq₁ M).Exact := by
  -- `S` is `ShortComplex (Rep R G)` here, but `Rep R G` is equivalent to `ModuleCat R[G]`.
  -- This step transfers our task to exactness in `ModuleCat R[G]`.
  apply Functor.reflects_exact_of_faithful equivalenceModuleMonoidAlgebra.functor
  -- A sequence of `R`-modules is exact if `LinearMap.range _ = LinearMap.ker _`
  -- In fact, `range ≤ ker` in complexes, so we just need `ker ≤ range`.
  apply ShortComplex.Exact.moduleCat_of_ker_le_range
  simp [equivalenceModuleMonoidAlgebra, toModuleMonoidAlgebra,
    toModuleMonoidAlgebraMap, ModuleCat.hom_ofHom]
  -- Now, we get `w` with `w ∈ ker`.
  intro (w : G → M.V) hw
  simp only [LinearMap.mem_range, LinearMap.coe_mk]
  change w ∈ LinearMap.range Representation.coind₁'_ι
  simpa [← Representation.map₁_ker] using (LinearEquiv.symm_apply_eq _).mp hw

lemma exact_periodSeq₂ : (periodSeq₂ M).Exact := by
  classical
  apply Functor.reflects_exact_of_faithful equivalenceModuleMonoidAlgebra.functor
  apply ShortComplex.Exact.moduleCat_of_ker_le_range
  simp [equivalenceModuleMonoidAlgebra, toModuleMonoidAlgebra, toModuleMonoidAlgebraMap,
    ModuleCat.hom_ofHom]
  intro w hw_ker
  change w ∈ LinearMap.ker (Representation.ind₁'_π (R := R)) at hw_ker
  rw [← Representation.map₂_range] at hw_ker
  obtain ⟨y, rfl⟩ := hw_ker
  use (y : G → M.V)
  change (linearEquivFunOnFinite ..).symm (Representation.map₁ y) = Representation.map₂ (R := R) y
  ext w
  rw [Representation.map₂_apply]
  simp [linearEquivFunOnFinite]

/-- `up M` is the cokernel of the first map in the periodicity sequence,
so is isomorphic to the coimage of the second map. -/
@[simps!]
def upIsoCoimagePeriodSeq₁ : up.obj M ≅ Abelian.coimage (periodSeq₁ M).g :=
  have := (exact_periodSeq₁ M).epi_kernelLift
  cokernel.congr _ _ (by simp) ≪≫ cokernelEpiComp (kernel.lift _ _ (periodSeq₁ M).zero) _

/-- `down M` is the kernel of the third map in the periodicity sequence,
so is isomorphic to the image of the second map. -/
def downIsoImagePeriodSeq₂ : down.obj M ≅ Abelian.image (periodSeq₂ M).f :=
  have := (exact_periodSeq₂ M).mono_cokernelDesc
  kernel.congr _ _ (by simp) ≪≫ kernelCompMono _ (cokernel.desc _ _ (periodSeq₂ M).zero)

/-- The up functor is isomorphic to the first periodicity sequence functor composed with the coimage
functor. -/
def upIsoCoimagePeriodSeq₁Functor :
    up (R := R) (G := G) ≅ periodSeq₁Functor ⋙ ShortComplex.gFunctor ⋙ coimageFunctor :=
  NatIso.ofComponents upIsoCoimagePeriodSeq₁ <| fun f => by
    simp [upIsoCoimagePeriodSeq₁]
    sorry

/-- The down functor is isomorphic to the second periodicity sequence functor composed with the
image functor. -/
def downIsoImagePeriodSeq₂Functor :
    down (R := R) (G := G) ≅ periodSeq₂Functor ⋙ ShortComplex.fFunctor ⋙ imageFunctor :=
  NatIso.ofComponents downIsoImagePeriodSeq₂ sorry

/-- The up and down functors for a finite cyclic group are pointwise isomorphic. -/
@[simps! hom inv]
def upIsoDownObj : up.obj M ≅ down.obj M := calc
    up.obj M
      ≅ Abelian.coimage (periodSeq₁ M).g := upIsoCoimagePeriodSeq₁ _
    _ ≅ Abelian.image (periodSeq₂ M).f := Abelian.coimageIsoImage _
    _ ≅ down.obj M := (downIsoImagePeriodSeq₂ _).symm

/-- The up and down functors for a finite cyclic group are naturally isomorphic. -/
def upIsoDown : up (R := R) (G := G) ≅ down :=
  upIsoCoimagePeriodSeq₁Functor ≪≫
    NatIso.ofComponents (fun M ↦ Abelian.coimageIsoImage _) sorry
    ≪≫ downIsoImagePeriodSeq₂Functor.symm

def periodicCohomology (n : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 3) := by
  apply Iso.trans (down_δiso_natTrans n)
  apply Iso.trans (Functor.isoWhiskerRight upIsoDown.symm _)
  exact up_δiso_natTrans _

def periodicCohomology' (n m : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 1 + 2 * m) := by
  induction m with
  | zero =>
    apply Iso.refl
  | succ m ih =>
    apply Iso.trans ih
    rw [mul_add, mul_one, ←add_assoc, add_assoc, add_comm 1, ←add_assoc]
    exact periodicCohomology _

def periodicCohomology_mod2 (m n : ℕ) (h : m ≡ n [MOD 2]) :
    functor R G (m + 1) ≅ functor R G (n + 1) :=
  if hLe : m ≤ n then
    (periodicCohomology' m ((n - m) /2)).trans <| eqToIso (by grind [Nat.modEq_iff_dvd])
  else
   (eqToIso (by grind [Nat.modEq_iff_dvd])).trans (periodicCohomology' n ((m - n) /2)).symm

/--
Let `M` be a representation of a finite cyclic group `G`. Suppose there are even
and positive integers `e` and `o` with `e` even and `o` odd, such that
`Hᵉ(G,M)` and `Hᵒ(G,M)` are both zero.
Then `Hⁿ(G,M)` is zero for all `n > 0`.
-/
lemma isZero_ofEven_Odd {M : Rep R G} {a b : ℕ}
    (hₑ : IsZero (groupCohomology M (2 * a + 2)))
    (hₒ : IsZero (groupCohomology M (2 * b + 1))) (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) := by
  obtain hn | hn := n.even_or_odd
  · refine .of_iso hₒ <| (periodicCohomology_mod2 n (2 * b) ?_).app M
    grind [Nat.modEq_iff_dvd]
  · refine .of_iso hₑ <| (periodicCohomology_mod2 n (2 * a + 1) ?_).app M
    grind [Nat.modEq_iff_dvd]

end Rep

include instCyclic in
def periodicTateCohomology (n : ℤ) :
    tateCohomology (R := R) (G := G) n ≅ tateCohomology (n + 2) :=
  sorry

variable {n : ℤ} {N : ℕ} {G : Type} [Group G] [IsCyclic G] [Fintype G] {M : Rep ℤ G} [M.IsTrivial]

namespace TateCohomology

/-- The even Tate cohomology of a trivial representation of a finite cyclic group of order `N` is
`ℤ/Nℤ`. -/
def evenTrivialInt [IsCyclic G] (hG : Nat.card G = N) (hn : Even n) :
    (tateCohomology n).obj (trivial ℤ G ℤ) ≅ .of ℤ (ZMod N) := sorry

/-- A trivial torsion-free representation of a finite cyclic group has trivial odd Tate cohomology.
-/
lemma isZero_odd_trivial_of_isAddTorsionFree {M : Type} [AddCommGroup M] [IsAddTorsionFree M]
    (hn : Odd n) : IsZero ((tateCohomology n).obj <| trivial ℤ G M) := sorry

end TateCohomology

namespace groupCohomology

/-- The nonzero even group cohomology of a trivial representation of a finite cyclic group of order
`N` is `ℤ/Nℤ`. -/
def evenTrivialInt {n : ℕ} (hG : Nat.card G = N) (hn : Even n) (hn₀ : n ≠ 0) :
    groupCohomology (trivial ℤ G ℤ) n ≅ .of ℤ (ZMod N) := by
  obtain _ | n := n
  · simp at hn₀
  exact .trans ((TateCohomology.isoGroupCohomology n).app _).symm <|
    TateCohomology.evenTrivialInt hG (mod_cast hn)

/-- A trivial torsion-free representation of a finite cyclic group has trivial odd group
cohomology. -/
lemma isZero_odd_trivial_of_isAddTorsionFree {n : ℕ} {M : Type} [AddCommGroup M]
    [IsAddTorsionFree M] (hn : Odd n) : IsZero (groupCohomology (trivial ℤ G M) n) := by
  obtain _ | n := n
  · simp at hn
  exact .of_iso (TateCohomology.isZero_odd_trivial_of_isAddTorsionFree <| mod_cast hn) <|
    (TateCohomology.isoGroupCohomology n).symm.app _

end groupCohomology

namespace groupHomology

/-- The odd group homology of a trivial representation of a finite cyclic group of order `N` is
`ℤ/Nℤ`. -/
def oddTrivialInt {n : ℕ} (hG : Nat.card G = N) (hn : Odd n) :
    groupHomology (trivial ℤ G ℤ) n ≅ .of ℤ (ZMod N) := by
  obtain _ | n := n
  · simp at hn
  exact .trans ((TateCohomology.isoGroupHomology n).app _).symm <|
    TateCohomology.evenTrivialInt hG <| by rw [← neg_add', even_neg]; exact mod_cast hn.add_one

/-- A trivial torsion-free representation of a finite cyclic group has trivial nonzero even group
homology. -/
lemma isZero_even_trivial_of_isAddTorsionFree {n : ℕ} {M : Type} [AddCommGroup M]
    [IsAddTorsionFree M] (hn : Even n) (hn₀ : n ≠ 0) :
    IsZero (groupHomology (trivial ℤ G M) n) := by
  obtain _ | n := n
  · simp at hn₀
  exact .of_iso (TateCohomology.isZero_odd_trivial_of_isAddTorsionFree <| by
    rw [← neg_add', odd_neg]; exact mod_cast hn.add_one) <|
    (TateCohomology.isoGroupHomology n).symm.app _

end groupHomology

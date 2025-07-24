import Mathlib
import ClassFieldTheory.GroupCohomology._6_LeftRegular
import ClassFieldTheory.GroupCohomology._7_coind1_and_ind1
import ClassFieldTheory.GroupCohomology._8_DimensionShift
import ClassFieldTheory.Mathlib.ModuleCatExact

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
  ConcreteCategory
  Limits
  BigOperators
  groupCohomology

-- TODO: add universes
variable {R : Type} [CommRing R]
variable (G : Type) [Group G] [instCyclic : IsCyclic G]
variable (M : Rep R G)

noncomputable section

/--
`gen G` is a generator of the cyclic group `G`.
-/
abbrev gen : G := IsCyclic.exists_generator.choose

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

variable {G} [Finite G] [DecidableEq G]

@[simp] lemma ofHom_sub (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ - f₂) : A ⟶ B) = ofHom f₁ - ofHom f₂ := rfl

@[simp] lemma ofHom_add (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ + f₂) : A ⟶ B) = ofHom f₁ + ofHom f₂ := rfl

@[simp] lemma ofHom_zero (A B : ModuleCat R) :
  (ofHom 0 : A ⟶ B) = 0 := rfl

@[simp] lemma ofHom_one (A : ModuleCat R) :
  (ofHom 1 : A ⟶ A) = 𝟙 A := rfl

omit [IsCyclic G] [Finite G] [DecidableEq G] in
@[simp] lemma Rep.ρ_mul_eq_comp (M : Rep R G) (x y : G) :
    Action.ρ M (x * y) = (Action.ρ M y) ≫ (Action.ρ M x) := map_mul (Action.ρ M) x y

namespace Representation

variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

omit [Finite G] [DecidableEq G]

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

omit [Finite G] [DecidableEq G]
lemma map₂_apply (f : G →₀ A) (x : G) :
    Representation.map₂ (R := R) f x = f x - f ((gen G)⁻¹ * x) := by
  simp [Representation.map₂]
  convert Finsupp.mapDomain_apply ?_ _ ((gen G)⁻¹ * x)
  · simp
  · intro x y h
    simpa using h

omit [Finite G] [DecidableEq G] in
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

omit [DecidableEq G]

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

omit [Finite G] [DecidableEq G] in
lemma coind_ι_gg_map₁_app : coind₁'_ι.app M ≫ map₁.app M = 0 := by
  ext : 2
  exact Representation.map₁_comp_coind_ι

omit [Finite G] [DecidableEq G] in
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

omit [Finite G] in
lemma map₂_app_gg_ind₁'_π_app :  map₂.app M ≫ ind₁'_π.app M = 0 := by
  ext : 2
  exact Representation.ind₁'_π_comp_map₂

omit [Finite G] in
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

/--
For a cyclic group `G`, this is the sequence of representations of a cyclic group:

` 0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0 `.

The middle map is `map₁ ≫ ind₁'_iso_coind₁'.inv`, which is
equal to `ind₁'_iso_coind₁'.inv ≫ map₂`. The sequence is exact.

It might be sensible to make this into a functor.
-/
def periodicitySequence : CochainComplex (Rep R G) (Fin 4) where
  X
  | 0 => M
  | 1 => coind₁'.obj M
  | 2 => ind₁'.obj M
  | 3 => M
  d
  | 0,1 => coind₁'_ι.app M
  | 1,2 => map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv
  | 2,3 => ind₁'_π.app M
  | _,_ => 0
  d_comp_d' i j k hij hjk := by
    fin_cases i
    all_goals
      fin_cases j
      try simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, Iso.app_inv, zero_comp]
      fin_cases k
      all_goals
        try simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, Fin.mk_one, comp_zero,
          Iso.app_inv, zero_comp]
    · rw [← Category.assoc, coind_ι_gg_map₁_app, zero_comp]
    · fin_cases k
      all_goals try simp only [Fin.reduceFinMk, Fin.isValue, comp_zero]
      rw [← Iso.app_inv _ _, map₁_comp_ind₁'_iso_coind₁', Category.assoc,
        map₂_app_gg_ind₁'_π_app, comp_zero]

lemma periodicitySequence_exactAt_one : (periodicitySequence M).ExactAt 1 := by
  rw [HomologicalComplex.ExactAt, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    ComplexShape.prev_eq' _ (i := 0) (by simp), ComplexShape.next_eq' _ (j := 2) (by simp)]
  -- S is ShortComplex (Rep R G) here
  -- but Rep R G is equivalent to ModuleCat R[G]
  -- this steps transfers our task to exactness in ModuleCat R[G]
  apply Functor.reflects_exact_of_faithful equivalenceModuleMonoidAlgebra.functor
  -- a sequence of R-modules is exact if LinearMap.range _ = LinearMap.ker _
  -- in fact, range ≤ ker in complexes, so we just need ker ≤ range
  apply ShortComplex.Exact.moduleCat_of_ker_le_range
  simp [equivalenceModuleMonoidAlgebra, toModuleMonoidAlgebra,
    toModuleMonoidAlgebraMap, ModuleCat.hom_ofHom]
  -- now we get w with w ∈ ker
  intro (w : G → M.V) hw
  simp only [Fin.isValue, LinearMap.mem_range, LinearMap.coe_mk]
  change w ∈ LinearMap.range Representation.coind₁'_ι
  simpa [← Representation.map₁_ker] using ((LinearEquiv.symm_apply_eq _).mp hw)

lemma periodicitySequence_exactAt_two [Fintype G] [DecidableEq G] :
    (periodicitySequence M).ExactAt 2 := by
  rw [HomologicalComplex.ExactAt, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
    ComplexShape.prev_eq' _ (i := 1) (by simp), ComplexShape.next_eq' _ (j := 3) (by simp)]
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

include instCyclic in
def up_obj_iso_down_obj : up.obj M ≅ down.obj M :=
  have := instCyclic
  /-
  `up.obj M` is the cokernel of the first map is `periodicitySequence`,
  so is isomorphic to the image of the second map. This in turn is isomorphic to the
  kernel of the last map, which is `down.obj M`.
  -/
  sorry

def up_iso_down : up (R := R) (G := G) ≅ down where
  hom := {
    app M := (up_obj_iso_down_obj M).hom
    naturality L N f := by
      ext v
      simp [up_obj_iso_down_obj]
      sorry
  }
  inv := {
    app M := (up_obj_iso_down_obj M).inv
    naturality := sorry
  }

def periodicCohomology (n : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 3) := by
  apply Iso.trans (down_δiso_natTrans n)
  apply Iso.trans (Functor.isoWhiskerRight up_iso_down.symm _)
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

omit [DecidableEq G] in
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
    grind [Nat.modEq_iff_dvd, Nat.even_iff]
  · refine .of_iso hₑ <| (periodicCohomology_mod2 n (2 * a + 1) ?_).app M
    grind [Nat.modEq_iff_dvd, Nat.odd_iff]

end Rep

end

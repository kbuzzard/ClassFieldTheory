/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu
-/
import ClassFieldTheory.Cohomology.Functors.UpDown
import ClassFieldTheory.Mathlib.GroupTheory.GroupAction.Quotient
import ClassFieldTheory.Cohomology.FiniteCyclic.CubeLemma -- move this to mathlib

/-!
# Corestriction

If `S` is a finite index subgroup of `G` and `M` is a `G`-module
then there's a corestriction map `H^n(S,M) → H^n(G,M)`, defined
by averaging on `H^0` and then by dimension shifting for
general `H^n`.

## Remarks

Cassels-Froehlich define cores on *homology* for an arbitrary
morphism `S → G` and then if `G` is finite they
extend it to Tate cohomology by dimension shifting.
It agrees with our definition on H^0-hat so presumably
agrees with our definition in general for G finite.

Arguably this filename has too large a number.

## TODO

cores o res = multiplication by index
-/

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] {S : Subgroup G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace groupCohomology

lemma cores_aux₁ {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v) (g₁ g₂ : G)
    (h : (QuotientGroup.mk g₁ : G ⧸ S) = QuotientGroup.mk g₂) : ρ g₁ v = ρ g₂ v := by
  rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by simp, map_mul, Module.End.mul_apply,
  hv _ (QuotientGroup.eq.1 h)]

lemma cores_aux₂ {X : Type} {V : Type} [Fintype X] [AddCommGroup V] [Module R V] {s₁ : X → G}
    {s₂ : X → G} (ρ : Representation R G V) (v : V) (hv : ∀ s ∈ S, (ρ s) v = v)
    (hs₁ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₁ x) : X → G ⧸ S))
    (hs₂ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₂ x) : X → G ⧸ S)) :
    ∑ x : X, ρ (s₁ x) v = ∑ x : X, ρ (s₂ x) v := by
  let e1 : X ≃ G ⧸ S := Equiv.ofBijective (QuotientGroup.mk ∘ s₁) hs₁
  let e2 : X ≃ G ⧸ S := Equiv.ofBijective (QuotientGroup.mk ∘ s₂) hs₂
  exact Finset.sum_equiv (e1.trans e2.symm) (by simp) fun i _ ↦ cores_aux₁ ρ v hv _ _ <| by
    rw [Equiv.trans_apply]
    exact (e2.apply_symm_apply _).symm

variable [S.FiniteIndex]

/-- The H^0 corestriction map for S ⊆ G a finite index subgroup, as an `R`-linear
map on invariants. -/
def _root_.Representation.cores₀_obj {V : Type} [AddCommGroup V] [Module R V] (ρ : Representation R G V) :
    Representation.invariants (MonoidHom.comp ρ S.subtype) →ₗ[R] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, ρ i.out x.1, fun g ↦ by
    simp only [map_sum, ← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
    letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
    refine (cores_aux₂ ρ x.1 (by simpa [-SetLike.coe_mem] using x.2) (by simp) ?_).symm
    simp_rw [QuotientGroup.mk_mul', QuotientGroup.out_eq', MulAction.bijective]⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

/-- The corestriction functor on H^0 for S ⊆ G a finite index subgroup, as a
functor `H^0(S,-) → H^0(G,-)`. -/
def cores₀ : Rep.res S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M :=
    (H0Iso (M ↓ S.subtype)).hom ≫ (ModuleCat.ofHom (Representation.cores₀_obj M.ρ)) ≫ (H0Iso M).inv
  naturality := by
    intro X Y f
    simp_rw [← Category.assoc]
    rw [(H0Iso Y).comp_inv_eq]
    simp_rw [Category.assoc]
    rw [functor_map, map_id_comp_H0Iso_hom, (H0Iso X).inv_hom_id_assoc, Functor.comp_map,
      functor_map, map_id_comp_H0Iso_hom_assoc, (H0Iso (X ↓ S.subtype)).cancel_iso_hom_left]
    ext x
    have comm := congr(∑ i : G ⧸ S, ModuleCat.Hom.hom $(f.comm i.out) x.val)
    simpa [Representation.cores₀_obj] using comm.symm

/-- The morphism `H¹(S, M↓S) ⟶ H¹(G, M)`. -/
def cores₁_obj [DecidableEq G] (M : Rep R G) :
    -- defining H¹(S, M↓S) ⟶ H¹(G, M) by a diagram chase
    (functor R S 1).obj (M ↓ S.subtype) ⟶ (functor R G 1).obj M := by
  -- Recall we have 0 ⟶ M ⟶ coind₁'^G M ⟶ up_G M ⟶ 0 a short exact sequence
  -- of `G`-modules which restricts to a short exact sequence of `S`-modules.
  -- First I claim δ : H⁰(S,(up_G M)↓S) ⟶ H¹(S,M↓S) is surjective
  haveI : Epi (mapShortComplex₃ (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    -- because `coind₁'^G M` has trivial cohomology
    up_δ_zero_epi_res (R := R) (φ := S.subtype) M S.subtype_injective
  -- so it suffices to give a map H⁰(S,(up_G M)↓S) ⟶ H¹(G,M) such that the
  -- image of H⁰(S,(coind₁'^G M)↓S) is in the kernel of that map
  refine (mapShortComplex₃_exact (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).desc ?_ ?_
  · -- The map H⁰(S,up_G M)↓S) ⟶ H¹(G,M) is just the composite of
    -- cores₀ : H⁰(S,up_G M↓S) ⟶ H⁰(G,up_G M) and δ : H⁰(G,up_G M) ⟶ H¹(G,M)
    exact (cores₀.app _) ≫ (δ (up_shortExact M) 0 1 rfl)
  · -- We now need to prove that the induced map
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H¹(G,M) is 0
    -- This is a diagram chase. The map is H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(S,(up_G M)↓S)
    -- (functoriality of H⁰) followed by cores₀ : H⁰(S,(up_G M)↓S) ⟶ H⁰(G, up_G M)
    -- followed by δ : H⁰(G, up_G M) ⟶ H¹(G, M). First put the brackets around
    -- the first two terms.
    rw [← Category.assoc]
    -- now apply naturality of cores₀, because I want to change
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(S,(up_G M)↓S) ⟶ H⁰(G, up_G M) to
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(G,(coind₁'^G M)) ⟶ H⁰(G, up_G M)
    let foo := ((upShortComplex.obj M).map (res S.subtype))
    let bar := cokernel.π (coind₁'_ι.app M)
    let moo := (res S.subtype ⋙ functor R (↥S) 0).map bar
    -- cores₀ : res S.subtype ⋙ functor R (↥S) 0 ⟶ functor R G 0
    have baz := cores₀.naturality (F := (res S.subtype ⋙ functor R (↥S) 0)) bar
    change ((res S.subtype ⋙ functor R (↥S) 0).map bar ≫ (cores₀.app (up.obj M))) ≫ _ = 0
    change _ ≫ (cores₀.app (up.obj M)) = _ ≫ _ at baz
    rw [baz, Category.assoc]
    convert comp_zero -- cancel first functor
    exact (mapShortComplex₃ (up_shortExact M) (rfl : 0 + 1 = 1)).zero

@[reassoc]
lemma commSq_cores₁ [DecidableEq G] (M : Rep R G) :
  δ (up_shortExact_res M S.subtype) 0 1 rfl ≫ cores₁_obj (S := S) M =
    (cores₀ (S := S)).app _ ≫ δ (up_shortExact M) 0 1 rfl :=
  haveI : Epi (mapShortComplex₃ (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    up_δ_zero_epi_res (R := R) (φ := S.subtype) M S.subtype_injective
  (mapShortComplex₃_exact (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g_desc _ _

lemma CategoryTheory.ShortComplex.cocyclesMk_surjective.{u, v, w} {C : Type u} [Category.{v, u} C] {FC : C → C → Type*}
    {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasForget₂ C Ab] [Preadditive C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
    (S : ShortComplex C) [S.HasHomology] (x : ↑((forget₂ C Ab).obj S.cycles)) :
    ∃ (x₂ : ↑((forget₂ C Ab).obj S.X₂)) (hx₂ : (ConcreteCategory.hom
    ((forget₂ C Ab).map S.g)) x₂ = 0), ShortComplex.cyclesMk _ x₂ hx₂ = x := by
  let y := (ShortComplex.abCyclesIso _).hom <| (S.mapCyclesIso (forget₂ C Ab)).inv x
  use y.1, y.2
  simp +zetaDelta [ShortComplex.cyclesMk]

lemma HomologicalComplex.cyclesMk_surjective.{v, u, u_1, u_2} {C : Type u} [Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type v}
    [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasForget₂ C Ab] [Abelian C]
    [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology] {ι : Type u_2} {c : ComplexShape ι}
    (K : HomologicalComplex C c) {i : ι} (j : ι) (hj : c.next i = j)
    (x : ↑((forget₂ C Ab).obj (K.cycles i))) :
    ∃ (x₂ : ↑((forget₂ C Ab).obj (K.X i))) (hx₂ : (ConcreteCategory.hom
    ((forget₂ C Ab).map (K.d i j))) x₂ = 0), HomologicalComplex.cyclesMk K x₂ j hj hx₂ = x := by
  subst hj
  exact (K.sc i).cocyclesMk_surjective x

lemma cocyclesMk_surjective.{u} {k G : Type u} [CommRing k] [Group G] {A : Rep k G}
    {n : ℕ} (x : cocycles A n) : ∃ (f : (Fin n → G) → A.V)
    (h : (ConcreteCategory.hom (inhomogeneousCochains.d A n)) f = 0), cocyclesMk f h = x := by
  have := (inhomogeneousCochains A).cyclesMk_surjective (n+1) (by simp) x
  convert this <;> simp

-- lemma δ_comm (X Y : Rep R G) (f : X ⟶ Y) [DecidableEq G] :
--     δ (up_shortExact_res X S.subtype) 0 1 rfl ≫ map (MonoidHom.id ↥S) ((res S.subtype).map f) 1 =
--     map (.id S) ((res S.subtype).map (up.map f)) 0 ≫ δ (up_shortExact_res Y S.subtype) 0 1 rfl := by
--   sorry

-- set_option maxHeartbeats 400000 in
theorem δ_naturality {X1 X2 : ShortComplex (Rep R G)} (hX1 : X1.ShortExact)
    (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i j : ℕ) (hij : i + 1 = j) :
  (δ hX1 i j hij) ≫ map (.id G) F.τ₁ j  = map (.id G) F.τ₃ i ≫ δ hX2 i j hij :=
  -- show δ hX1 i j hij ≫ HomologicalComplex.homologyMap F'.τ₁ j =
  --   HomologicalComplex.homologyMap F'.τ₃ i ≫ δ hX2 i j hij
  HomologicalComplex.HomologySequence.δ_naturality
    ((cochainsFunctor R G).mapShortComplex.map F)
    (map_cochainsFunctor_shortExact hX1) (map_cochainsFunctor_shortExact hX2) i j hij

theorem cores₁_naturality  (X Y : Rep R G) (f : X ⟶ Y) [DecidableEq G] :
    (res S.subtype ⋙ functor R (↥S) 1).map f ≫ cores₁_obj Y =
    cores₁_obj X ≫ (functor R G 1).map f := by
  haveI : Epi (δ (up_shortExact_res X S.subtype) 0 1 rfl) :=
    up_δ_zero_epi_res (R := R) (φ := S.subtype) X S.subtype_injective
  symm
  refine CategoryTheory.cubeLemma (ModuleCat R)
    (H0 (up.obj X ↓ S.subtype)) (H1 (X ↓ S.subtype)) (H0 (up.obj X)) (H1 X)
    (H0 (up.obj Y ↓ S.subtype)) (H1 (Y ↓ S.subtype)) (H0 (up.obj Y)) (H1 Y)
    -- four ?_ are the maps in the conclusion of the lemma
    (δ (up_shortExact_res X S.subtype) 0 1 rfl) (δ (up_shortExact X) 0 1 rfl)
    (δ (up_shortExact_res Y S.subtype) 0 1 rfl) (δ (up_shortExact Y) 0 1 rfl)
    (cores₀.app (up.obj X)) _ (cores₀.app (up.obj Y)) _
    (map (.id S) ((res S.subtype).map (up.map f)) 0) _
    (map (.id G) (up.map f) 0) _
    ?_ ?_ ?_ ?_ (by exact (cores₀ (S := S)|>.naturality (X := up.obj X) (up.map f)).symm) this
  · exact (commSq_cores₁ X).symm
  · exact (commSq_cores₁ Y).symm
  · sorry
  · sorry

/-- Corestriction on objects in group cohomology. -/
def cores_obj [DecidableEq G] : (M : Rep R G) → (n : ℕ) →
    (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => cores₁_obj M
| M, (d + 2) =>
  -- δ : H^{d+1}(G,up -) ≅ H^{d+2}(G,-)
  let up_δ_bottom_Iso := Rep.dimensionShift.up_δiso_natTrans (R := R) (G := G) d
  -- `M ⟶ coind₁'^G M ⟶ up_G M` as a complex of S-modules
  let upsc_top := (upShortComplex.obj M).map (res S.subtype)
  -- the above complex of S-modules is exact
  have htopexact : upsc_top.ShortExact := up_shortExact_res M S.subtype
  -- so δ : H^{d+1}(S,up_G M) ≅ H^{d+2}(S,M)...
  let up_δ_top_isIso : IsIso (δ (htopexact) (d + 1) (d + 2) rfl) := by
    -- ...because `coind₁'^G M` has trivial cohomology as S-module
    -- have := M.coind₁'_trivialCohomology
    have : upsc_top.X₂.TrivialCohomology := Rep.TrivialCohomology.res (coind₁'.obj M)
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upShortComplex_obj_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ (htopexact) (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M

variable (R) (S) in
/-- Corestriction as a natural transformation. -/
def coresNatTrans (n : ℕ) [DecidableEq G] : Rep.res S.subtype ⋙ functor R S n ⟶ functor R G n where
  app M := (groupCohomology.cores_obj M n)
  naturality X Y f := match n with
    | 0 => cores₀.naturality f
    | 1 => cores₁_naturality _ _ _
    | (d + 2) => sorry

lemma cores_res (M : Rep R G) (n : ℕ) [DecidableEq G] :
    ((groupCohomology.resNatTrans.{0} R (S.subtype) n) ≫
      (groupCohomology.coresNatTrans R S n) : functor R G n ⟶ functor R G n) =
      S.index • (.id _) := sorry


-- any element of H^n-hat (n ∈ ℤ) is |G|-torsion
lemma tateCohomology_torsion {n : ℤ} [Fintype G] (M : Rep R G) (x : (tateCohomology n).obj M) :
    (Nat.card G) • x = 0 := sorry

-- Should the above really be a statement about a functor?
-- Something like this?

-- instance (n : ℤ) [Finite G] : Functor.Additive (tateCohomology (R := R) (G := G) n) := sorry

-- this doesn't work
-- lemma tateCohomology_torsion' {n : ℤ} [Finite G] :
--     (Nat.card G) • (CategoryTheory.NatTrans.id (tateCohomology (R := R) (G := G) n)) = 0 := sorry

-- p^infty-torsion injects into H^(Sylow) (for group cohomology)
lemma groupCohomology_Sylow {n : ℕ} (hn : 0 < n) [Finite G] (M : Rep R G)
    (x : groupCohomology M n) (p : ℕ) (P : Sylow p G) (hx : ∃ d, (p ^ d) • x = 0)
    (hx' : x ≠ 0) : (groupCohomology.rest (P.toSubgroup.subtype) n).app M x ≠ 0 := sorry

-- Want an analogous statement for Tate cohomology but I can't find restriction
-- in Tate cohomology

import Mathlib
import ClassFieldTheory.GroupCohomology.«01_Basic»
import ClassFieldTheory.GroupCohomology.«02_restriction»
import ClassFieldTheory.GroupCohomology.«04_TateCohomology_def»

/-!
# Trivial (Tate) (co)homology

An object `M : Rep R G` is has *trivial cohomology* if
`Hⁿ(S, M)=0` for all `n > 0` and all subgroup `S` of `G`.

`M` has *trivial homology* if for all subgroups `S` and all `n > 0`
we have `Hₙ(S, M) ≅ 0`.

`M` has *trivial Tate cohomology* if for all subgroups `S` and all `n : ℤ`
we have `Hⁿ_{Tate}(S, M) ≅ 0`.

We define these three classes of representation, and prove that they are preserved
by isomorphisms.
-/

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology

namespace Rep
variable {R G : Type} [CommRing R] [Group G]

/--
A representation `M : Rep R G` has trivial cohomology if the cohomology groups `Hⁿ(H, M)`
are zero for every subgroup `H` of `G` and every `n > 0`.
-/
class TrivialCohomology (M : Rep R G) : Prop where
  isZero (H : Subgroup G) {n : ℕ} :
    IsZero (groupCohomology (M ↓ H.subtype) (n + 1))

lemma _root_.groupCohomology.map_congr.{u} {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f1 f2 : G →* H) (φ1 : (Action.res (ModuleCat k) f1).obj A ⟶ B)
    (φ2 : (Action.res (ModuleCat k) f2).obj A ⟶ B) (h1 : f1 = f2) (h2 : φ1.hom = φ2.hom) (n : ℕ) :
    groupCohomology.map f1 φ1 n = groupCohomology.map f2 φ2 n := by
  subst h1
  congr
  ext
  simp [h2]

noncomputable def groupCohomology.mapIso {H : Type} [Fintype H] [Group H] [Fintype G]
    {M : Rep R G} (e : G ≃* H) {N : Rep R H}
    (e' : M.V ≅ N.V)
    (he' : ∀ (g : G), M.2 g ≫ e'.hom = e'.hom ≫ N.2 (e g)) (n : ℕ) :
    groupCohomology M n ≅ groupCohomology N n where
  hom := groupCohomology.map e.symm ⟨e'.hom, by aesop⟩ n
  inv := groupCohomology.map e ⟨e'.inv, by aesop (add simp [Iso.comp_inv_eq])⟩ n
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr _ _ _ _ (by simp) (by simp) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr _ _ _ _ (by simp) (by simp) n

noncomputable def res_iso_range_res (M : Rep R G) {H : Type} [Group H] (f : H →* G)
    (n : ℕ) (hf : Function.Injective f) :
    groupCohomology (M ↓ f.range.subtype) n ≅
      groupCohomology (M ↓ f) n where
  hom := groupCohomology.map f.rangeRestrict (𝟙 (M ↓ f)) _
  inv := groupCohomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom ⟨𝟙 M.V, by simp⟩ _
  hom_inv_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    exact groupCohomology.map_congr _ _ _ _ (by ext; simp) (by simp) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_id]
    refine groupCohomology.map_congr _ _ _ _ (MonoidHom.ext_iff.2 fun x ↦ ?_) (by simp) n
    rw [MonoidHom.comp_apply]
    exact (MonoidHom.ofInjective hf).symm_apply_apply _

theorem istrivial_of_injective (M : Rep R G) {H : Type} [Group H] (f : H →* G) (n : ℕ) (hn : n ≠ 0)
    (hf : Function.Injective f) [M.TrivialCohomology] : IsZero (groupCohomology (M ↓ f) n) := by
  cases n with
  | zero => tauto
  | succ n => exact IsZero.of_iso (@TrivialCohomology.isZero R G _ _ M _ f.range n) <|
    (res_iso_range_res M f (n + 1) hf).symm

lemma TrivialCohomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] :
    M.TrivialCohomology := by
  constructor
  intro H n
  have : (functor R H n.succ).obj (M ↓ _) ≅ (functor R H n.succ).obj (N ↓ _)
  · apply (functor _ _ n.succ).mapIso
    exact (res H.subtype).mapIso f
  exact isZero H |>.of_iso this

protected lemma TrivialCohomology.res (M : Rep R G) {H : Subgroup G} [M.TrivialCohomology] :
    (M ↓ H.subtype).TrivialCohomology where
  isZero S n := istrivial_of_injective M (H.subtype.comp S.subtype) (n + 1) (by omega)
      (show Function.Injective (H.subtype ∘ _) from
        Function.Injective.comp H.subtype_injective S.subtype_injective)

lemma isZero_of_trivialCohomology {M : Rep R G} [M.TrivialCohomology] {n : ℕ} :
    IsZero (groupCohomology M (n + 1)) :=
  istrivial_of_injective M (.id G) n.succ (by omega) Function.injective_id

lemma trivialCohomology_iff_res {M : Rep R G} :
    M.TrivialCohomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialCohomology where
  mp _ _ _ f inj := ⟨fun S n ↦  istrivial_of_injective M (f.comp S.subtype) (n + 1) (by omega)
    (show Function.Injective (f ∘ _) from Function.Injective.comp inj S.subtype_injective)⟩
  mpr h := h (f := .id G) Function.injective_id

class TrivialHomology (M : Rep R G) : Prop where
  isZero (H : Subgroup G) {n : ℕ} :
    IsZero (groupHomology (M ↓ H.subtype) (n + 1))

lemma _root_.groupHomology.map_congr.{u} {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k G} {B : Rep k H} (f1 f2 : G →* H) (φ1 : A ⟶ (Action.res (ModuleCat k) f1).obj B)
    (φ2 : A ⟶ (Action.res (ModuleCat k) f2).obj B) (h1 : f1 = f2) (h2 : φ1.hom = φ2.hom) (n : ℕ) :
    groupHomology.map f1 φ1 n = groupHomology.map f2 φ2 n := by
  subst h1
  congr
  ext
  simp [h2]

lemma TrivialHomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  constructor
  intro H n
  exact (isZero _).of_iso <| (groupHomology.functor R H n.succ).mapIso <| (res H.subtype).mapIso f

noncomputable def res_iso_range_res_homology (M : Rep R G) {H : Type} [Group H] (f : H →* G)
    (n : ℕ) (hf : Function.Injective f) :
    groupHomology (M ↓ f.range.subtype) n ≅ groupHomology (M ↓ f) n where
  hom := groupHomology.map (MonoidHom.ofInjective hf).symm.toMonoidHom ⟨𝟙 M.V, by simp⟩ _
  inv := groupHomology.map f.rangeRestrict ⟨𝟙 M.V, by simp⟩ _
  hom_inv_id := by
    rw [← groupHomology.map_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← groupHomology.map_id]
    exact groupHomology.map_congr _ _ _ _ (by ext; simp) (by simp) n
  inv_hom_id := by
    rw [← groupHomology.map_comp, ← groupHomology.map_id]
    exact groupHomology.map_congr _ _ _ _ (MonoidHom.ext_iff.2 <| fun x ↦ by
      rw [MonoidHom.comp_apply]
      exact (MonoidHom.ofInjective hf).symm_apply_apply _) (by simp) n

lemma TrivialHomology.of_injective {M : Rep R G} {H : Type} [Group H] (f : H →* G) (n : ℕ)
    (hn : n ≠ 0) (hf : Function.Injective f) [M.TrivialHomology] :
    IsZero (groupHomology (M ↓ f) n) := by
  cases n with
  | zero => tauto
  | succ n => exact IsZero.of_iso (@TrivialHomology.isZero R G _ _ M _ f.range n) <|
    (res_iso_range_res_homology M f (n + 1) hf).symm

protected lemma TrivialHomology.res (M : Rep R G) {H : Type} [Group H] {f : H →* G}
    (hf : Function.Injective f) [M.TrivialHomology] : (M ↓ f).TrivialHomology where
  isZero H n :=
    TrivialHomology.of_injective (f.comp H.subtype) (n + 1) (by omega) <|
      show Function.Injective (f ∘ _) from Function.Injective.comp hf H.subtype_injective

lemma isZero_of_trivialHomology {M : Rep R G} [M.TrivialHomology] {n : ℕ} :
    IsZero (groupHomology M (n + 1)) :=
  TrivialHomology.of_injective (.id G) n.succ (by omega) Function.injective_id

lemma trivialHomology_iff_res {M : Rep R G} :
    M.TrivialHomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialHomology
    where
  mp _ _ _ _ inj := .res M inj
  mpr h := h (f := .id G) Function.injective_id

class TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  isZero (H : Subgroup G) {n : ℤ} :
    IsZero ((tateCohomology n).obj (M ↓ H.subtype : Rep R H))

lemma TrivialTateCohomology.of_iso [Finite G] {M N : Rep R G} (f : M ≅ N)
    [N.TrivialTateCohomology] :
    M.TrivialTateCohomology := ⟨fun H ↦ (TrivialTateCohomology.isZero _).of_iso <|
    (tateCohomology _).mapIso <| (res H.subtype).mapIso f⟩

--TODO : add simp lemma for Rep.norm.hom
noncomputable abbrev _root_.TateCohomology.cochainsmap {G H : Type} [Group G] [Group H] [Fintype G]
    [Fintype H] {M : Rep R G} {N : Rep R H} (e : G ≃* H)
    (φ : M ⟶ N ↓ e) :=
  CochainComplex.ConnectData.map (tateComplexConnectData M) (tateComplexConnectData N)
  (groupHomology.chainsMap e φ)
  (groupCohomology.cochainsMap e.symm ⟨φ.hom, fun h ↦ by simpa using φ.comm (e.symm h)⟩) <| by
  ext f0 (m : M) h0
  simp [cochainsMap_f, Rep.norm, Representation.norm]
  have (h : H) := ModuleCat.hom_ext_iff.1 (φ.comm (e.symm h))
  simp only [Action.res_obj_V, ModuleCat.hom_comp, ρ_hom, Action.res_obj_ρ, MonoidHom.coe_comp,
    MonoidHom.coe_coe, Function.comp_apply, MulEquiv.apply_symm_apply] at this
  conv_lhs =>
    enter [2]
    intro h
    rw[← LinearMap.comp_apply, ← this]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  exact Finset.sum_equiv e.symm.toEquiv (fun _ ↦ by simp) <| fun i _ ↦ rfl

noncomputable abbrev _root_.TateCohomology.map {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    {M : Rep R G} {N : Rep R H} (e : G ≃* H) (φ : M ⟶ (Action.res (ModuleCat R) e).obj N)
    (n : ℤ) :
    (tateCohomology n).obj M ⟶ (tateCohomology n).obj N :=
  HomologicalComplex.homologyMap (TateCohomology.cochainsmap e φ) _

lemma _root_.groupHomology.chainsMap_congr {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k G} {B : Rep k H} (f1 f2 : G →* H) (φ1 : A ⟶ (Action.res (ModuleCat k) f1).obj B)
    (φ2 : A ⟶ (Action.res (ModuleCat k) f2).obj B) (h1 : f1 = f2) (h2 : φ1.hom = φ2.hom) :
    groupHomology.chainsMap f1 φ1 = groupHomology.chainsMap f2 φ2 := by
  subst h1
  congr
  ext
  simp [h2]

lemma _root_.groupCohomology.cochainsMap_congr {k G H : Type} [CommRing k] [Group G] [Group H]
    {A : Rep k G} {B : Rep k H} (f1 f2 : G →* H) (φ1 : (Action.res (ModuleCat k) f1).obj B ⟶ A)
    (φ2 : (Action.res (ModuleCat k) f2).obj B ⟶ A) (h1 : f1 = f2) (h2 : φ1.hom = φ2.hom) :
    groupCohomology.cochainsMap f1 φ1 = groupCohomology.cochainsMap f2 φ2 := by
  subst h1
  congr
  ext
  simp [h2]

noncomputable def TateCohomology.res_iso {H : Type} [Fintype H] [Group H] [Fintype G]
    {M : Rep R G} (e : G ≃* H) {N : Rep R H}
    (e' : M.V ≅ N.V)
    (he' : ∀ (g : G), M.2 g ≫ e'.hom = e'.hom ≫ N.2 (e g)) (n : ℤ) :
    (tateCohomology n).obj M ≅
    ((tateCohomology n).obj N) where
  hom := TateCohomology.map e ⟨e'.hom, by aesop⟩ n
  inv := TateCohomology.map e.symm ⟨e'.inv, e.surjective.forall.mpr <| by
      dsimp
      simp_rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, he',
        e.apply_symm_apply, implies_true]⟩ n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CochainComplex.ConnectData.map_comp]
    conv_rhs => erw [← HomologicalComplex.homologyMap_id, ← CochainComplex.ConnectData.map_id]
    congr
    · rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_id]
      exact groupHomology.chainsMap_congr _ _ _ _ (by simp) (by simp)
    · rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_id]
      exact groupCohomology.cochainsMap_congr _ _ _ _ (by simp) (by simp)
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CochainComplex.ConnectData.map_comp]
    conv_rhs => erw [← HomologicalComplex.homologyMap_id, ← CochainComplex.ConnectData.map_id]
    congr
    · rw [← groupHomology.chainsMap_comp, ← groupHomology.chainsMap_id]
      exact groupHomology.chainsMap_congr _ _ _ _ (by simp) (by simp)
    · rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_id]
      exact groupCohomology.cochainsMap_congr _ _ _ _ (by simp) (by simp)

attribute [local instance] Fintype.ofFinite in
lemma TrivialTateCohomology.of_injective [Fintype G] {M : Rep R G} {H : Type} [Fintype H]
    [Group H] (f : H →* G) (n : ℤ) (hf : Function.Injective f)
    [M.TrivialTateCohomology] : IsZero ((tateCohomology n).obj (M ↓ f)) :=
  .of_iso (isZero (M := M) f.range (n := n)) <| TateCohomology.res_iso
    (MonoidHom.ofInjective hf) (Iso.refl _) (by aesop) _

lemma isZero_of_trivialTateCohomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] {n : ℕ} : IsZero ((tateCohomology n).obj M) :=
  TrivialTateCohomology.of_injective (.id G) n Function.injective_id

instance TrivialTateCohomology.to_trivialCohomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialCohomology where
  isZero H n := (TrivialTateCohomology.isZero (M := M) H (n := Nat.cast n + 1)).of_iso <|
    tateCohomology.isoGroupCohomology n|>.app (M ↓ H.subtype)|>.symm

instance TrivialtateCohomology.to_trivialHomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialHomology where
  isZero H n := (TrivialTateCohomology.isZero H (n := - n - 2)).of_iso <|
    (tateCohomology.isoGroupHomology n|>.app (M ↓ H.subtype)).symm

lemma TrivialTateCohomology.of_cases [Fintype G] {M : Rep R G}
    [M.TrivialCohomology] [M.TrivialHomology]
    (h : ∀ {H : Type} [Group H] (φ : H →* G) (inj : Function.Injective φ),
      have := Fintype.ofInjective φ inj
      IsZero ((tateCohomology 0).obj (M ↓ φ : Rep R H)) ∧
        IsZero ((tateCohomology (-1)).obj (M ↓ φ : Rep R H))) :
    TrivialTateCohomology M where
  isZero H n := by
    match n with
    | .ofNat (n + 1) =>
      letI := TrivialCohomology.res M (H := H)
      exact isZero_of_trivialCohomology.of_iso <|
        (tateCohomology.isoGroupCohomology n).app (M ↓ H.subtype)
    | .negSucc (n + 1) =>
      letI := TrivialHomology.res M (H := H) H.subtype_injective
      rw [show Int.negSucc (n + 1) = -n - 2 by grind]
      exact isZero_of_trivialHomology.of_iso <|
        (tateCohomology.isoGroupHomology n).app (M ↓ H.subtype)
    | 0 =>
      aesop
    | .negSucc 0 =>
      aesop

instance [Subsingleton G] {M : Rep R G} : M.TrivialCohomology where
  isZero H n := by
    letI : Subsingleton H := Function.Injective.subsingleton H.subtype_injective
    apply isZero_groupCohomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialHomology where
  isZero H n := by
    letI : Subsingleton H := Function.Injective.subsingleton H.subtype_injective
    apply isZero_groupHomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialTateCohomology := by
  haveI := Fintype.ofFinite G
  refine .of_cases ?_
  intro H _ φ inj
  have : Subsingleton H := Function.Injective.subsingleton inj
  have : (M ↓ φ).ρ.IsTrivial := {
    out g := by
      rw [Subsingleton.eq_one g, map_one]
      rfl }
  constructor
  · refine IsZero.of_iso ?_ (tateCohomology.zeroIsoOfIsTrivial _)
    rw [Nat.card_unique, Nat.cast_one, LinearMap.range_eq_top_of_cancel (by exact fun _ _ a ↦ a)]
    exact ModuleCat.isZero_of_subsingleton _
  refine IsZero.of_iso ?_ (tateCohomology.negOneIsoOfIsTrivial _)
  rw [Nat.card_unique, Nat.cast_one, LinearMap.ker_eq_bot_of_cancel (by exact fun _ _ a ↦ a)]
  exact ModuleCat.isZero_of_subsingleton _

end Rep

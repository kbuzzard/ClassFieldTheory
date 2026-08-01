module

public import ClassFieldTheory.Cohomology.Functors.Inflation
public import ClassFieldTheory.Cohomology.Functors.UpDown
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

universe u

variable {R G Q : Type u} [CommRing R] [Group G] [Group Q] {φ : G →* Q}
  (surj : Function.Surjective φ)

namespace groupCohomology

/--
Suppose we have a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(K,A) = 0` then the `K`-invariants form a short exact sequence in `Rep R Q`:

  `0 ⟶ Aᴷ ⟶ Bᴷ ⟶ Cᴷ ⟶ 0`, where `K = φ.ker`.
-/
lemma quotientToInvariantsFunctor'_shortExact_ofShortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (hS' : IsZero (H1 (S.X₁ ↓ φ.ker.subtype))) :
    (S.map (quotientToInvariantsFunctor' surj)).ShortExact :=
  /-
  This is the opening section of the long exact sequence. The next term is `H¹(K,S.X₁)`, which
  is assumeed to be zero.
  -/
  -- (S.map (quotientToInvariantsFunctor' surj)).exact_iff_exact_map_forget₂.2 _
  -- forget this to module cat and then do
  -- .mk' ((S.map (quotientToInvariantsFunctor' surj)).moduleCat_exact_iff_range_eq_ker _) _ _
  sorry

abbrev resEquiv_inv (n : ℕ) (G' : Type u) [Group G'] (M : Rep R G) (e : G ≃* G') :
    groupCohomology ((Rep.resEquiv R e).inverse.obj M) n ≅ groupCohomology M n :=
  mapIso e.symm (LinearEquiv.refl R M.V) (fun _ ↦ rfl) n

lemma resEquiv_inv_hom (n : ℕ) (G' : Type u) [Group G'] (M : Rep R G) (e : G ≃* G') :
    (resEquiv_inv n G' M e).hom
      = map e.toMonoidHom (Rep.ofHom ⟨LinearMap.id (M := M.V), fun g ↦ by
          ext x
          change M.ρ (e.symm (e g)) x = M.ρ g x
          rw [e.symm_apply_apply]⟩) n := by
  exact map_congr (by ext; simp) rfl n

lemma map_one {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (φ : Rep.res (1 : G →* H) A ⟶ B) (n : ℕ) [NeZero n] :
    map (1 : G →* H) φ n = 0 := by
  let ψ1 : A ↓ (1 : PUnit →* H) ⟶ A ↓ 1 := 𝟙 _
  let ψ2 : ((A ↓ (1 : PUnit →* H)) ↓ (1 : G →* PUnit)) ⟶ B := Rep.ofHom
    { toLinearMap := φ.hom
      isIntertwining' := fun _ ↦ by ext; simp [← Rep.hom_comm_apply φ]}
  have h : (Rep.resFunctor 1).map ψ1 ≫ ψ2 = φ := by ext; simp [ψ1, ψ2]
  have := @map_comp k _ G PUnit H _ _ _ A (A ↓ 1) B 1 1 ψ1 ψ2 n
  simp only [MonoidHom.one_comp, res_obj_ρ, h] at this
  rw [this]
  convert comp_zero
  refine CategoryTheory.Limits.IsZero.eq_zero_of_src ?_ _
  cases n; · simp_all
  exact isZero_groupCohomology_succ_of_subsingleton _ _

lemma map_one' {k G H : Type u} [CommRing k] [Group G] [Group H] (f : G →* H) (hf : f = 1)
    {A : Rep k H} {B : Rep k G} (φ : res f A ⟶ B) (n : ℕ) [NeZero n] :
    map f φ n = 0 := by
  subst hf
  exact map_one φ n

@[reassoc]
lemma map_zero {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) (n : ℕ) :
    map f (0 : res f A ⟶ B) n = 0 := by
  dsimp [map]
  unfold groupCohomology
  -- unfolding map would unfold the type as well, and groupCohomology is a `def`
  simp

abbrev inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ surj) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ φ.ker.subtype) (n + 1)
  f := (infl surj (n + 1)).app M
  g := (rest φ.ker.subtype (n + 1)).app M
  zero := by
    induction n generalizing M with
    | zero =>
      have : map _ _ _ ≫ map _ (𝟙 (M ↓ φ.ker.subtype)) _ = 0 :=
        (groupCohomology.H1InfRes M φ.ker).zero
      simp only [Nat.reduceAdd, infl, cochain_infl, Functor.hcomp_id, Functor.whiskerRight_app,
        Functor.comp_obj, rest_app]
      change map _ _ 1 ≫ _ = 0
      apply_fun ((resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
        (QuotientGroup.quotientKerEquivOfSurjective φ surj)).hom ≫ ·) at this
      rwa [comp_zero, resEquiv_inv_hom, ← Category.assoc, ← map_comp] at this
    | succ n ih =>
      dsimp [infl, rest, ← map.eq_def, cochain_infl]
      simp only [Functor.hcomp_id, Functor.whiskerRight_app, Functor.comp_obj]
      change map _ _ _ ≫ map _ _ (n + 1 + 1) = 0
      rw [← map_comp, map_one']
      ext ⟨x, hx⟩
      simp [MonoidHom.mem_ker.1 hx]

instance isIso_δ_ofhM (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    IsIso (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
    (n + 1) (n + 1 + 1) rfl) := by
  have := coind₁'_quotientToInvariants_trivialCohomology (M := M) surj
  refine isIso_δ_of_isZero _ (n + 1) ?_ ?_
  <;> simp only [ShortComplex.map_X₂, upSES_X₂]
  <;> exact isZero_of_trivialCohomology

def IsoNext (n) (M : Rep R G) (hM : IsZero (H1 (M ↓ φ.ker.subtype))) :
    inflationRestriction surj n (up.obj M) ≅ inflationRestriction surj (n + 1) M :=
  ShortComplex.isoMk
    (@asIso _ _ _ _
      (δ (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
        (n + 1) (n + 1 + 1) rfl)
      (isIso_δ_ofhM surj n M hM))
    (asIso (δ (shortExact_upSES M) (n + 1) (n + 1 + 1) rfl))
    (δUpResIso M φ.ker.subtype_injective (n + 1))
    (infl_δ_naturality surj (shortExact_upSES M)
      (quotientToInvariantsFunctor'_shortExact_ofShortExact surj (shortExact_upSES M) hM)
      (n + 1) (n + 1 + 1) rfl)
    (rest_δ_naturality (shortExact_upSES M) φ.ker.subtype (n + 1) (n + 1 + 1) rfl)

/-- An isomorphism of short complexes transports `Mono` of the first map. -/
lemma _root_.CategoryTheory.ShortComplex.mono_f_of_iso {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) (h : Mono S₁.f) :
    Mono S₂.f := by
  obtain ⟨h₁, h₂, -⟩ := (ShortComplex.isIso_iff e.hom).1 inferInstance
  have := h
  have : Mono (inv e.hom.τ₁) := IsIso.mono_of_iso _
  have : Mono e.hom.τ₂ := IsIso.mono_of_iso _
  rw [← IsIso.inv_hom_id_assoc e.hom.τ₁ S₂.f, e.hom.comm₁₂]
  exact mono_comp _ _

theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    Mono (inflationRestriction surj n M).f := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following square commutes by `infl_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶  Hⁿ⁺¹(G,M)    `
  `     |                   |        `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶  Hⁿ(G,up M)   `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero =>
    have h1 : Mono (H1InfRes M φ.ker).f := inferInstance
    change Mono (map _ _ _) at h1
    have h2 := @mono_comp _ _ _ _ _
      (resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
        (QuotientGroup.quotientKerEquivOfSurjective φ surj)).hom
      (IsIso.mono_of_iso _) _ h1
    rw [resEquiv_inv_hom, ← map_comp] at h2
    exact h2
  | succ n ih =>
    specialize @ih (up.obj M) <| fun i hi ↦ by
      refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
      exact hM (i + 1) (by omega)
    exact ShortComplex.mono_f_of_iso (IsoNext surj n M (hM 0 (by omega))) ih

/-- In degree zero, the inflation–restriction complex is isomorphic to Mathlib's `H1InfRes`. -/
def isoH1InfRes (M : Rep R G) :
    inflationRestriction surj 0 M ≅ H1InfRes M φ.ker :=
  ShortComplex.isoMk
    (resEquiv_inv 1 Q (M.quotientToInvariants φ.ker)
      (QuotientGroup.quotientKerEquivOfSurjective φ surj))
    (Iso.refl _)
    (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change map _ _ 1 ≫ map _ _ 1 = map _ _ 1
      rw [← map_comp]
      exact map_congr (by ext g; simp [QuotientGroup.quotientKerEquivOfSurjective])
        rfl 1)
    (by
      simp only [Iso.refl_hom]
      rfl)

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ φ.ker.subtype) (i + 1))) :
    (inflationRestriction surj n M).Exact := by
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸S,M^S)     ⟶    Hⁿ⁺¹(G,M)     ⟶    Hⁿ⁺¹(S,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸S,(up M)^S)  ⟶    Hⁿ(G,(up M))  ⟶    Hⁿ(S,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  induction n generalizing M with
  | zero => exact ShortComplex.exact_of_iso (isoH1InfRes surj M).symm (H1InfRes_exact M φ.ker)
  | succ n ih =>
    specialize @ih (up.obj M) <| fun i hi ↦ by
      refine IsZero.of_iso ?_ (Rep.dimensionShift.δUpResIso _ φ.ker.subtype_injective _)
      exact hM (i + 1) (by omega)
    exact ShortComplex.exact_of_iso (IsoNext surj n M (hM 0 (by omega))) ih

end groupCohomology

end

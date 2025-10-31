import ClassFieldTheory.Cohomology.IndCoind.Finite
import ClassFieldTheory.Cohomology.IndCoind.TrivialCohomology
import ClassFieldTheory.Cohomology.TateCohomology
import ClassFieldTheory.Mathlib.RepresentationTheory.Rep

/-!
We define functors `up` and `down` from `Rep R G` to itself.
`up.obj M` is defined to be the cokernel of the injection `coind₁'_ι : M ⟶ coind₁'.obj M` and
`down.obj M` is defined to be the kernel of the surjection `ind₁'_π : ind₁'.obj M → M`.
Hence for any `M : Rep R G` we construct two short exact sequences

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0` and
  `0 ⟶ down.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

These can be used for dimension-shifting because `coind₁'.obj M` has trivial cohomology and
`ind₁'.obj M` has trivial homology. I.e. for all `n > 0` we have (for every subgroup `S` of `G`):

  `Hⁿ(S,up M) ≅ Hⁿ⁺¹(S,M)` and
  `Hₙ(S,down M) ≅ Hₙ₊₁(S,M)`.

If `G` is finite then both the induced and the
coinduced representations have trivial Tate cohomology,
so we have:

  `Hⁿ_{Tate}(S, up M) ≅ Hⁿ⁺¹_{Tate}(S,M)`,
  `Hⁿ_{Tate}(S, down M) ≅ Hⁿ⁻¹_{Tate}(S,M)`.

-/

open
  Rep
  Representation
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable {R G : Type} [CommRing R] [Group G] (M : Rep R G)

namespace Rep.dimensionShift

@[simp] lemma forget₂_map_apply {N : Rep R G} (f : M ⟶ N) :
    (forget₂ (Rep R G) (ModuleCat R)).map f = f.hom := rfl

lemma coind₁'_ι.app_apply {M : Rep R G} (m : M) (x : G) : (coind₁'_ι.app M m) x = m := rfl

/--
The map from `M` to its coinduced representation is a monomorphism.
-/
instance : Mono (coind₁'_ι.app M) where
  right_cancellation g f hgf := by
    ext n
    have : Function.Injective (hom (coind₁'_ι.app M)) := by
      refine (injective_iff_map_eq_zero' (hom (coind₁'_ι.app M))).mpr (fun a  => ?_)
      constructor
      · intro g
        have : Function.const G a = 0 := by exact g
        simpa [Function.const_eq_zero] using this
      · exact fun a_1 ↦ congrArg (⇑(hom (coind₁'_ι.app M))) a_1
    exact this (congrFun (congrArg DFunLike.coe (congrArg hom hgf)) n)

/--
The functor taking `M : Rep R G` to `up.obj M`, defined by the short exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0`.

Since `coind₁'.obj M` is acyclic, the cohomology of `up.obj M` is a shift by one
of the cohomology of `M`.
-/
@[simps] def up : Rep R G ⥤ Rep R G where
  obj M := cokernel (coind₁'_ι.app M)
  map f:= by
    apply cokernel.desc _ (coind₁'.map f ≫ cokernel.π _)
    rw [←Category.assoc, ←coind₁'_ι.naturality, Category.assoc, cokernel.condition, comp_zero]
  map_id := by simp
  map_comp f g := by simpa only using coequalizer.hom_ext (by simp)

/--
The functor taking `M : Rep R G` to the short complex:

  `M ⟶ coind₁'.obj M ⟶ up.obj M`.

-/
@[simps] def upShortComplex : Rep R G ⥤ ShortComplex (Rep R G) where
  obj M := {
    X₁ := M
    X₂ := coind₁'.obj M
    X₃ := up.obj M
    f := coind₁'_ι.app M
    g := cokernel.π (coind₁'_ι.app M)
    zero := cokernel.condition (coind₁'_ι.app M)
  }
  map f := {
    τ₁ := f
    τ₂ := coind₁'.map f
    τ₃ := up.map f
    comm₁₂ := coind₁'_ι.naturality f
    comm₂₃ := (cokernel.π_desc _ _ _).symm
  }
  map_comp f g := by
    congr
    rw [Functor.map_comp]
  map_id M := by
    congr
    rw [up_map]
    apply IsColimit.desc_self

/--
`upShortComplex.obj M` is a short exact sequence of representations.
-/
lemma up_shortExact : (upShortComplex.obj M).ShortExact where
  exact := ShortComplex.exact_cokernel (coind₁'_ι.app M)
  mono_f := inferInstanceAs (Mono (coind₁'_ι.app M))
  epi_g := coequalizer.π_epi

lemma up_shortExact_res {H : Type} [Group H] [DecidableEq G] (φ : H →* G) :
    ((upShortComplex.obj M).map (res φ)).ShortExact := by
  rw [shortExact_res]
  exact up_shortExact M

abbrev up_π : coind₁' ⟶ up (R := R) (G := G) where
  app _             := (upShortComplex.obj _).g
  naturality _ _ _  := (upShortComplex.map _).comm₂₃

variable [DecidableEq G]
/--
The connecting homomorphism from `H⁰(G,up M)` to `H¹(G,M)` is
an epimorphism (i.e. surjective).
-/
instance δ_up_zero_epi : Epi (δ (up_shortExact M) 0 1 rfl) := by
  refine epi_δ_of_isZero (up_shortExact M) 0 ?_
  simpa only [upShortComplex_obj_X₂, zero_add] using isZero_of_trivialCohomology

/--
The connecting homomorphism from `Hⁿ⁺¹(G,up M)` to `Hⁿ⁺²(G,M)` is an isomorphism.
-/
instance δ_up_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) := by
  refine isIso_δ_of_isZero (up_shortExact M) (n + 1) ?_ ?_
  all_goals simpa only [upShortComplex_obj_X₂] using isZero_of_trivialCohomology

def δUpIso (n : ℕ) : groupCohomology (up.obj M) (n + 1) ≅ groupCohomology M (n + 2) :=
  asIso (δ (up_shortExact M) (n + 1) (n + 2) rfl)

def δUpNatIso (n : ℕ) : up ⋙ functor R G (n + 1) ≅ functor R G (n + 2) :=
  NatIso.ofComponents (fun X => by simpa [Functor.comp_obj, functor_obj] using δUpIso (M := X) n)
  <| fun {X Y} f ↦ by
      refine id (Eq.symm (HomologicalComplex.HomologySequence.δ_naturality
        (ShortComplex.homMk ((cochainsFunctor R G).map (upShortComplex.map f).1)
        ((cochainsFunctor R G).map (upShortComplex.map f).2) ((cochainsFunctor R G).map (upShortComplex.map f).3)
        rfl (?_)) (map_cochainsFunctor_shortExact (up_shortExact X))
        (map_cochainsFunctor_shortExact (up_shortExact Y)) (n+1) (n+2) rfl))
      simp only [ShortComplex.map_X₂, upShortComplex_obj_X₂, cochainsFunctor_obj, ShortComplex.map_X₃,
        upShortComplex_obj_X₃, up_obj, Functor.id_obj, upShortComplex_map_τ₂, cochainsFunctor_map, ShortComplex.map_g,
        upShortComplex_obj_g, upShortComplex_map_τ₃, up_map]
      have : coind₁'.map f ≫ cokernel.π (coind₁'_ι.app Y) = cokernel.π (coind₁'_ι.app X) ≫
        cokernel.desc (coind₁'_ι.app X) ((coind₁'.map f) ≫ cokernel.π (coind₁'_ι.app Y))
        (up._proof_2 f) := (cokernel.π_desc _ _ _).symm
      ext a b c
      simp only [CochainComplex.of_x, HomologicalComplex.comp_f, ModuleCat.hom_comp,
        cochainsMap_id_f_hom_eq_compLeft, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.compLeft_apply]
      calc
       _ = (hom (coind₁'.map f ≫ cokernel.π (coind₁'_ι.app Y))) (b c) := rfl
       _ = (hom (cokernel.π (coind₁'_ι.app X) ≫ cokernel.desc (coind₁'_ι.app X)
        (coind₁'.map f ≫ cokernel.π (coind₁'_ι.app Y)) (up._proof_2 f)))
        (b c):= by rw [congrFun (congrArg DFunLike.coe (congrArg hom this)) (b c)]
       _ = _ := rfl

/--
If S ⊆ G then the connecting homomorphism from `H^{0}(S,(up_G M)↓S)` to `H^{1}(S,M↓S)` is
an epimorphism (i.e. surjective).
-/
instance epi_δ_up_zero_res {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) : Epi (δ (up_shortExact_res M φ) 0 1 rfl) := by
  refine epi_δ_of_isZero (up_shortExact_res M φ) 0 ?_
  simpa only [ShortComplex.map_X₂, upShortComplex_obj_X₂, zero_add] using isZero_of_injective _ φ _ (by omega) inj

/--
If `S ⊆ G` and `M` is a `G`-module then the connecting homomorphism
from `H^{n+1}(S,(up_G M)↓S)` to `H^{n+2}(S,M↓S)` is an isomorphism.
-/
instance isIso_δ_up_res {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) (n : ℕ) [NeZero n] :
    IsIso (δ (up_shortExact_res M φ) n (n + 1) rfl) := by
  refine isIso_δ_of_isZero (up_shortExact_res M φ) n ?_ ?_ <;>
    simpa only [ShortComplex.map_X₂, upShortComplex_obj_X₂]
      using isZero_of_injective _ φ _ (NeZero.ne _) inj

def δUpResIso {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) (n : ℕ) [NeZero n] :
    groupCohomology (up.obj M ↓ φ) n ≅ groupCohomology (M ↓ φ) (n + 1) := by
  have := isIso_δ_up_res M inj n
  apply asIso (δ (up_shortExact_res M φ) n (n + 1) rfl)

omit [DecidableEq G] in
lemma ind₁'_obj_ρ : (ind₁'.obj M).ρ = M.ρ.ind₁' := rfl

omit [DecidableEq G] in
lemma ind₁'_obj_ρ_apply (g : G) : (ind₁'.obj M).ρ g = M.ρ.ind₁' g := rfl

omit [DecidableEq G] in
lemma ind₁'_π.app_hom : (ind₁'_π.app M).hom = ofHom Representation.ind₁'_π := rfl

omit [DecidableEq G] in
lemma ind₁'_π.app_apply (f : ind₁'.obj M) :
    (ind₁'_π.app M) f = Finsupp.sum f (fun _ ↦ LinearMap.id (R := R)) := rfl

/--
The functor taking `M : Rep R G` to `down.obj M`, defined by the short exact sequence

  `0 ⟶ down.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`..

Since `ind₁'.obj M` is acyclic, the homology of `down.obj M` is a shift by one
of the homology of `M`.
-/
@[simps] def down : Rep R G ⥤ Rep R G where
  obj M := kernel (ind₁'_π.app M)
  map φ := kernel.lift _ (kernel.ι _ ≫ ind₁'.map φ) (by
    rw [Category.assoc, ind₁'_π.naturality, ←Category.assoc, kernel.condition, zero_comp])
  map_id _ := by simp
  map_comp f g := by simpa only using equalizer.hom_ext (by simp)

/-- The short exact sequence defining `down M`. -/
abbrev downSES : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := kernel.ι (ind₁'_π.app M)
  g := ind₁'_π.app M
  zero := kernel.condition (ind₁'_π.app M)

/-- `down` as a functor from representations to short complexes.

  `M ⟶ coind₁'.obj M ⟶ up.obj M`. -/
@[simps] def downShortComplex : Rep R G ⥤ ShortComplex (Rep R G) where
  obj M := {
    X₁ := down.obj M
    X₂ := ind₁'.obj M
    X₃ := M
    f := kernel.ι (ind₁'_π.app M)
    g := ind₁'_π.app M
    zero := kernel.condition (ind₁'_π.app M)
  }
  map {X Y} f := {
    τ₁ := down.map f
    τ₂ := ind₁'.map f
    τ₃ := f
    comm₁₂ := by
     simp only [down, Functor.id_obj, kernel.lift_ι]
    comm₂₃ := by
      simp only [Functor.id_obj, naturality, Functor.id_map]
  }
  map_comp f g := by
    simp only [Functor.id_obj, Functor.map_comp]
    rfl
  map_id M := by
    simp only [Functor.id_obj, CategoryTheory.Functor.map_id]
    rfl

omit [DecidableEq G] in
lemma shortExact_downSES : (downSES M).ShortExact where
  exact   := ShortComplex.exact_kernel (ind₁'_π.app M)
  mono_f  := inferInstance
  epi_g   := inferInstance

omit [DecidableEq G] in
lemma shortExact_downSES_res {H : Type} [Group H] (φ : H →* G) :
    ((downSES M).map (res φ)).ShortExact := by
  simpa using shortExact_downSES M

variable [Fintype G]

/--
The connecting homomorphism `H⁰(G,down.obj M) ⟶ H¹(G, M)` is an epimorphism if `G` is finite.
-/
instance epi_δ_down_zero : Epi (δ (shortExact_downSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES M) 0 ?_
  simpa only [zero_add] using isZero_of_trivialCohomology

/--
The connecting homomorphism `H⁰(H,down.obj M ↓ H) ⟶ H¹(H, M ↓ H)` is an epimorphism if
`H` is a subgroup of a finite group `G`.
-/
instance epi_δ_down_res_zero {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) : Epi (δ (shortExact_downSES_res M φ) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES_res M φ) 0 ?_
  simpa only [ShortComplex.map_X₂, zero_add] using isZero_of_injective _ φ _ (by omega) inj

/--
The connecting homomorphism `Hⁿ⁺¹(G,down.obj M) ⟶ Hⁿ⁺²(G, M)` is an isomorphism
if `G` is finite.
-/
instance isIso_δ_down (n : ℕ) [NeZero n] : IsIso (δ (shortExact_downSES M) n (n + 1) rfl) :=
  isIso_δ_of_isZero (shortExact_downSES M) n isZero_of_trivialCohomology isZero_of_trivialCohomology

instance isIso_δ_down_res (n : ℕ) [NeZero n] {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) : IsIso (δ (shortExact_downSES_res M φ) n (n + 1) rfl) := by
  have := NeZero.ne n
  refine isIso_δ_of_isZero (shortExact_downSES_res M φ) n ?_ ?_
  all_goals simpa only [ShortComplex.map_X₂] using isZero_of_injective _ φ _ (by omega) inj

def δDownIso (n : ℕ) [NeZero n] : groupCohomology M n ≅ groupCohomology (down.obj M) (n + 1) :=
  asIso (δ (shortExact_downSES M) n (n + 1) rfl)

def δDownResIso {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) (n : ℕ) [NeZero n] :
    groupCohomology (M ↓ φ) n ≅ groupCohomology (down.obj M ↓ φ) (n + 1) :=
  have := isIso_δ_down_res M n inj
  asIso (δ (shortExact_downSES_res M φ) n (n + 1) rfl)

def δDownNatIso (n : ℕ) [NeZero n] : functor R G n ≅ down ⋙ functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ by simp only [functor_obj, Functor.comp_obj]; exact δDownIso M _)
  <| fun {X Y} f ↦ by
    refine id (Eq.symm (HomologicalComplex.HomologySequence.δ_naturality
      (ShortComplex.homMk ((cochainsFunctor R G).map (downShortComplex.map f).1)
      ((cochainsFunctor R G).map (downShortComplex.map f).2) ((cochainsFunctor R G).map (downShortComplex.map f).3)
      ?_ ?_ ) ( map_cochainsFunctor_shortExact (shortExact_downSES X))
      (map_cochainsFunctor_shortExact (shortExact_downSES Y)) n (n + 1) rfl))
    simp only [ShortComplex.map_X₁, cochainsFunctor_obj, ShortComplex.map_X₂, downShortComplex_obj_X₁,
      downShortComplex_map_τ₁, cochainsFunctor_map, ShortComplex.map_f, Functor.id_obj, downShortComplex_obj_X₂,
      downShortComplex_map_τ₂]
    ext a b c
    simp only [CochainComplex.of_x, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      cochainsMap_id_f_hom_eq_compLeft, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.compLeft_apply]
    have :(down.map f) ≫ kernel.ι (ind₁'_π.app Y )= (kernel.ι (ind₁'_π.app X)) ≫ ind₁'.map f := by
      simp only [down, Functor.id_obj, kernel.lift_ι]
    calc
      _ = hom ((down.map f) ≫ kernel.ι (ind₁'_π.app Y)) (b c) := rfl
      _ = hom ((kernel.ι (ind₁'_π.app X)) ≫ ind₁'.map f) (b c) := by rw [this] ; rfl
      _ = _ := rfl
    simp only [ShortComplex.map_X₂, cochainsFunctor_obj, ShortComplex.map_X₃, downShortComplex_obj_X₂,
      downShortComplex_map_τ₂, cochainsFunctor_map, ShortComplex.map_g, downShortComplex_obj_X₃, downShortComplex_map_τ₃]
    ext a b c
    simp only [CochainComplex.of_x, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      cochainsMap_id_f_hom_eq_compLeft, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.compLeft_apply]
    calc
      _ = (hom ((ind₁'.map f) ≫ (ind₁'_π.app Y))) (b c) := rfl
      _ = (hom (ind₁'_π.app X ≫ (𝟭 (Rep R G)).map f)) (b c) := by
        rw [(ind₁'_π (G:= G) (R:= R)).naturality f]
      _ = _ := rfl

end dimensionShift

end Rep

namespace groupCohomology

variable [Fintype G]
open Rep
  dimensionShift

/--
An explicit version of `isZero_of_trivialTateCohomology`
-/
private lemma isZero_of_trivialTateCohomology' (M : Rep R G)
    [M.TrivialTateCohomology] (n : ℤ) : IsZero ((tateComplexFunctor.obj M).homology n) :=
  TrivialTateCohomology.of_injective (.id G) _ Function.injective_id

instance instIsIso_up_shortExact (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (up_shortExact M) n) := by
  have _ : TrivialTateCohomology (coind₁'.obj M) := inferInstance
  refine ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (up_shortExact M))
    n (n + 1) (by rfl) (by simp;exact isZero_of_trivialTateCohomology' (coind₁'.obj M) n)
    (by simp;exact isZero_of_trivialTateCohomology' (coind₁'.obj M) (n + 1))

instance instIsIso_shortExact_downSES (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (shortExact_downSES M) n) := by
  have _ : TrivialTateCohomology (ind₁'.obj M) := inferInstance
  refine ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES M))
    n (n + 1) (by rfl) (by simp;exact isZero_of_trivialTateCohomology' (ind₁'.obj M) n)
    (by simp;exact isZero_of_trivialTateCohomology' (ind₁'.obj M) (n + 1))

def δUpIsoTate (n : ℤ) (M : Rep R G) :
    (tateCohomology n).obj (up.obj M) ≅ (tateCohomology (n + 1)).obj M :=
  have := instIsIso_up_shortExact M n
  asIso (TateCohomology.δ (up_shortExact M) n)

def δDownIsoTate (n : ℤ) (M : Rep R G) :
    (tateCohomology n).obj M ≅ (tateCohomology (n + 1)).obj (down.obj M) :=
  asIso (TateCohomology.δ (shortExact_downSES M) n)

def δUpNatIsoTate (n : ℤ) : up ⋙ tateCohomology (R := R) (G := G) n ≅ tateCohomology (n + 1) :=
  NatIso.ofComponents (fun M ↦ δUpIsoTate n M) sorry

def δDownNatIsoTate (n : ℤ) : tateCohomology (R := R) (G := G) n ≅ down ⋙ tateCohomology (n + 1) :=
  NatIso.ofComponents (δDownIsoTate n) sorry

end groupCohomology

end

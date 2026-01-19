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
  Function
  Rep
  Representation
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology
  HomologicalComplex

noncomputable section

variable {R G : Type} [CommRing R] [Group G] (M : Rep R G)

namespace Rep.dimensionShift

/-! ### The up functor -/

/--
The functor taking `M : Rep R G` to `up.obj M`, defined by the short exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0`.

Since `coind₁'.obj M` is acyclic, the cohomology of `up.obj M` is a shift by one
of the cohomology of `M`.
-/
@[simps] def up : Rep R G ⥤ Rep R G where
  obj M := cokernel (coind₁'_ι.app M)
  map f := by
    apply cokernel.desc _ (coind₁'.map f ≫ cokernel.π _)
    rw [←Category.assoc, ←coind₁'_ι.naturality, Category.assoc, cokernel.condition, comp_zero]
  map_comp f g := by simpa only using coequalizer.hom_ext (by simp)

/-- The projection from the coinduced module to the up module. -/
abbrev up.π : coind₁'.obj M ⟶ up.obj M := cokernel.π (coind₁'_ι.app M)

/-- The short exact sequence defining `up M`. -/
@[simps] def upSES : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := coind₁'.obj M
  X₃ := up.obj M
  f := coind₁'_ι.app M
  g := up.π M
  zero := cokernel.condition (coind₁'_ι.app M)

lemma shortExact_upSES : (upSES M).ShortExact where
  exact := ShortComplex.exact_cokernel (coind₁'_ι.app M)
  mono_f := by dsimp; infer_instance
  epi_g := by dsimp; infer_instance

lemma shortExact_upSES_res {H : Type} [Group H] (φ : H →* G) :
    ((upSES M).map (res φ)).ShortExact := by simpa using shortExact_upSES M

/--
The functor taking `M : Rep R G` to the short complex:

  `M ⟶ coind₁'.obj M ⟶ up.obj M`.

-/
@[simps] def upShortComplex : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := upSES
  map f := {
    τ₁ := f
    τ₂ := coind₁'.map f
    τ₃ := up.map f
  }
  map_comp f g := by simp only [Functor.map_comp]; rfl

/--
The connecting homomorphism from `H⁰(G,up M)` to `H¹(G,M)` is
an epimorphism (i.e. surjective).
-/
instance δ_up_zero_epi : Epi (δ (shortExact_upSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_upSES M) 0 ?_
  simpa only [upSES_X₂, zero_add] using isZero_of_trivialCohomology

/--
The connecting homomorphism from `Hⁿ⁺¹(G,up M)` to `Hⁿ⁺²(G,M)` is an isomorphism.
-/
instance δ_up_isIso (n : ℕ) : IsIso (δ (shortExact_upSES M) (n + 1) (n + 2) rfl) := by
  refine isIso_δ_of_isZero (shortExact_upSES M) (n + 1) ?_ ?_ <;>
    simpa only [upSES_X₂] using isZero_of_trivialCohomology

@[simps! hom]
def δUpIso (n : ℕ) : groupCohomology (up.obj M) (n + 1) ≅ groupCohomology M (n + 2) :=
  asIso (δ (shortExact_upSES M) (n + 1) (n + 2) rfl)

def δUpNatIso (n : ℕ) : up ⋙ functor R G (n + 1) ≅ functor R G (n + 2) :=
  NatIso.ofComponents (fun M ↦ δUpIso M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((upShortComplex ⋙ (cochainsFunctor R G).mapShortComplex).map f)
    (map_cochainsFunctor_shortExact (shortExact_upSES M))
    (map_cochainsFunctor_shortExact (shortExact_upSES N)) (n + 1) (n + 2) rfl

/--
If S ⊆ G then the connecting homomorphism from `H^{0}(S,(up_G M)↓S)` to `H^{1}(S,M↓S)` is
an epimorphism (i.e. surjective).
-/
lemma epi_δ_up_zero_res {S : Type} [Group S] {φ : S →* G} (inj : Injective φ) :
    Epi (δ ((shortExact_res φ).2 <| shortExact_upSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero _ 0 ?_
  simpa only [ShortComplex.map_X₂, upSES_X₂, zero_add]
    using isZero_of_injective _ φ _ (by omega) inj

/--
If `S ⊆ G` and `M` is a `G`-module then the connecting homomorphism
from `H^{n+1}(S,(up_G M)↓S)` to `H^{n+2}(S,M↓S)` is an isomorphism.
-/
lemma isIso_δ_up_res {S : Type} [Group S] {φ : S →* G} (inj : Injective φ) (n : ℕ) [NeZero n] :
    IsIso (δ ((shortExact_res φ).2 <| shortExact_upSES M) n (n + 1) rfl) := by
  refine isIso_δ_of_isZero _ n ?_ ?_ <;>
    simpa only [ShortComplex.map_X₂, upSES_X₂]
      using isZero_of_injective _ φ _ (NeZero.ne _) inj

def δUpResIso {S : Type} [Group S] {φ : S →* G} (inj : Function.Injective φ) (n : ℕ) [NeZero n] :
    groupCohomology (up.obj M ↓ φ) n ≅ groupCohomology (M ↓ φ) (n + 1) := by
  have := isIso_δ_up_res M inj n
  apply asIso (δ ((shortExact_res φ).2 <| shortExact_upSES M) n (n + 1) rfl)

/-! ### The down functor -/

/--
The functor taking `M : Rep R G` to `down.obj M`, defined by the short exact sequence

  `0 ⟶ down.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

Since `ind₁'.obj M` is acyclic, the homology of `down.obj M` is a shift by one
of the homology of `M`.
-/
@[simps] def down : Rep R G ⥤ Rep R G where
  obj M := kernel (ind₁'_π.app M)
  map φ := kernel.lift _ (kernel.ι _ ≫ ind₁'.map φ) (by
    rw [Category.assoc, ind₁'_π.naturality, ←Category.assoc, kernel.condition, zero_comp])
  map_comp f g := by simpa only using equalizer.hom_ext (by simp)

/-- The injection from the down module to the induced module. -/
abbrev down.ι : down.obj M ⟶ ind₁'.obj M := kernel.ι (ind₁'_π.app M)

/-- The short exact sequence defining `down M`. -/
@[simps] def downSES : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := down.ι M
  g := ind₁'_π.app M
  zero := kernel.condition (ind₁'_π.app M)

lemma shortExact_downSES : (downSES M).ShortExact where
  exact := ShortComplex.exact_kernel (ind₁'_π.app M)
  mono_f := by dsimp; infer_instance
  epi_g := by dsimp; infer_instance

lemma shortExact_downSES_res {H : Type} [Group H] (φ : H →* G) :
    ((downSES M).map (res φ)).ShortExact := by simpa using shortExact_downSES M

/-- `down` as a functor from representations to short complexes.

  `M ⟶ coind₁'.obj M ⟶ up.obj M`. -/
@[simps] def downShortComplex : Rep R G ⥤ ShortComplex (Rep R G) where
  obj := downSES
  map f := {
    τ₁ := down.map f
    τ₂ := ind₁'.map f
    τ₃ := f
  }
  map_comp f g := by simp only [Functor.map_comp]; rfl

variable [Fintype G]

/--
The connecting homomorphism `H⁰(G,down.obj M) ⟶ H¹(G, M)` is an epimorphism if `G` is finite.
-/
instance epi_δ_down_zero : Epi (δ (shortExact_downSES M) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES M) 0 ?_
  simpa only [downSES_X₂, zero_add] using isZero_of_trivialCohomology

/--
The connecting homomorphism `H⁰(H,down.obj M ↓ H) ⟶ H¹(H, M ↓ H)` is an epimorphism if
`H` is a subgroup of a finite group `G`.
-/
lemma epi_δ_down_res_zero {S : Type} [Group S] {φ : S →* G} (inj : Injective φ) :
    Epi (δ (shortExact_downSES_res M φ) 0 1 rfl) := by
  refine epi_δ_of_isZero (shortExact_downSES_res M φ) 0 ?_
  simpa only [downSES_X₂, ShortComplex.map_X₂, zero_add]
    using isZero_of_injective _ φ _ (by omega) inj

/--
The connecting homomorphism `Hⁿ⁺¹(G,down.obj M) ⟶ Hⁿ⁺²(G, M)` is an isomorphism
if `G` is finite.
-/
instance isIso_δ_down (n : ℕ) [NeZero n] : IsIso (δ (shortExact_downSES M) n (n + 1) rfl) := by
  apply isIso_δ_of_isZero <;> dsimp only [downSES_X₂] <;> exact isZero_of_trivialCohomology

lemma isIso_δ_down_res (n : ℕ) [NeZero n] {H : Type} [Group H] {φ : H →* G} (inj : Injective φ) :
    IsIso (δ (shortExact_downSES_res M φ) n (n + 1) rfl) := by
  have := NeZero.ne n
  refine isIso_δ_of_isZero (shortExact_downSES_res M φ) n ?_ ?_ <;>
    simpa only [downSES_X₂, ShortComplex.map_X₂] using isZero_of_injective _ φ _ (by omega) inj

def δDownIso (n : ℕ) [NeZero n] : groupCohomology M n ≅ groupCohomology (down.obj M) (n + 1) :=
  asIso (δ (shortExact_downSES M) n (n + 1) rfl)

def δDownResIso {H : Type} [Group H] {φ : H →* G} (inj : Injective φ) (n : ℕ) [NeZero n] :
    groupCohomology (M ↓ φ) n ≅ groupCohomology (down.obj M ↓ φ) (n + 1) :=
  have := isIso_δ_down_res M n inj
  asIso (δ (shortExact_downSES_res M φ) n (n + 1) rfl)

def δDownNatIso (n : ℕ) [NeZero n] : functor R G n ≅ down ⋙ functor R G (n + 1) :=
  NatIso.ofComponents (fun M ↦ δDownIso M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((downShortComplex ⋙ (cochainsFunctor R G).mapShortComplex).map f)
    (map_cochainsFunctor_shortExact (shortExact_downSES M))
    (map_cochainsFunctor_shortExact (shortExact_downSES N)) n (n + 1) rfl

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

instance instIsIso_shortExact_upSES (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (shortExact_upSES M) n) := by
  have _ : TrivialTateCohomology (coind₁'.obj M) := inferInstance
  exact ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES M))
    n (n + 1) (by rfl) (by simp; exact isZero_of_trivialTateCohomology' (coind₁'.obj M) n)
    (by simp; exact isZero_of_trivialTateCohomology' (coind₁'.obj M) (n + 1))

instance instIsIso_shortExact_downSES (M : Rep R G) (n : ℤ) :
    IsIso (TateCohomology.δ (shortExact_downSES M) n) := by
  have _ : TrivialTateCohomology (ind₁'.obj M) := inferInstance
  exact ShortComplex.ShortExact.isIso_δ
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES M))
    n (n + 1) (by rfl) (by simp; exact isZero_of_trivialTateCohomology' (ind₁'.obj M) n)
    (by simp; exact isZero_of_trivialTateCohomology' (ind₁'.obj M) (n + 1))

@[simps! hom]
def δUpIsoTate (M : Rep R G) (n : ℤ) :
    (tateCohomology n).obj (up.obj M) ≅ (tateCohomology (n + 1)).obj M :=
  have := instIsIso_shortExact_upSES M n
  asIso (TateCohomology.δ (shortExact_upSES M) n)

@[simps! hom]
def δDownIsoTate (M : Rep R G) (n : ℤ) :
    (tateCohomology n).obj M ≅ (tateCohomology (n + 1)).obj (down.obj M) :=
  asIso (TateCohomology.δ (shortExact_downSES M) n)

def δUpResIsoTate {S : Type} [Group S] [Fintype S] {φ : S →* G} (inj : Injective φ) (n : ℤ) :
    (tateCohomology n).obj (up.obj M ↓ φ) ≅ (tateCohomology (n + 1)).obj (M ↓ φ) := sorry

def δDownResIsoTate {H : Type} [Group H] [Fintype H] {φ : H →* G} (inj : Injective φ) (n : ℤ) :
    (tateCohomology n).obj (M ↓ φ) ≅ (tateCohomology (n + 1)).obj (down.obj M ↓ φ) := sorry

def δUpNatIsoTate (n : ℤ) : up ⋙ tateCohomology (R := R) (G := G) n ≅ tateCohomology (n + 1) :=
  NatIso.ofComponents (fun M ↦ δUpIsoTate M n) fun {M N} f ↦ .symm <| HomologySequence.δ_naturality
    ((upShortComplex ⋙ tateComplexFunctor.mapShortComplex).map f)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES M))
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_upSES N)) n (n + 1) rfl

def δDownNatIsoTate (n : ℤ) : tateCohomology (R := R) (G := G) n ≅ down ⋙ tateCohomology (n + 1) :=
  NatIso.ofComponents (fun M ↦ δDownIsoTate M n) fun {M N} f ↦ .symm <|
    HomologySequence.δ_naturality
      ((downShortComplex ⋙ tateComplexFunctor.mapShortComplex).map f)
      (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES M))
      (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_downSES N)) n (n + 1) rfl

end groupCohomology

end

import Mathlib
import ClassFieldTheory.GroupCohomology._4_TateCohomology_def
import ClassFieldTheory.GroupCohomology._7_coind1_and_ind1

/-!
We define functors `up` and `down` from `Rep R G` to itself.
`up.obj M` is defined to be the cokernel of the injection `coind₁'_ι : M ⟶ coind₁'.obj M` and
`down.obj M` is defined to be the kernel of the surjection `ind₁'_π : ind₁'.obj M → M`.
Hence for any `M : Rep R G` we construct two short exact sequences
(the second defined only for finite `G`):

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0` and
  `0 ⟶ down.obj M ⟶ coind₁'.obj M ⟶ M ⟶ 0`.

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
instance : Mono (coind₁'_ι.app M) := by
  /-
  The function which takes `m : M` to the constant
  function on `G` with value `m` is clearly injective.
  -/
  sorry

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
  map_id := sorry
  map_comp := sorry

/--
The functor taking `M : Rep R G` to the short complex:

  `M ⟶ coind₁'.obj M ⟶ up.obj M`.

-/
@[simps] def upSes : Rep R G ⥤ ShortComplex (Rep R G) where
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
`upSes.obj M` is a short exact sequence of representations.
-/
lemma up_shortExact : (upSes.obj M).ShortExact where
  exact := ShortComplex.exact_cokernel (coind₁'_ι.app M)
  mono_f := inferInstanceAs (Mono (coind₁'_ι.app M))
  epi_g := coequalizer.π_epi

lemma up_shortExact_res {H : Type} [Group H] [DecidableEq G] (φ : H →* G) :
    ((upSes.obj M).map (res φ)).ShortExact := by
  rw [res_respectsShortExact]
  exact up_shortExact M

abbrev up_π : coind₁' ⟶ up (R := R) (G := G) where
  app _             := (upSes.obj _).g
  naturality _ _ _  := (upSes.map _).comm₂₃

variable [DecidableEq G]
/--
The connecting homomorphism from `H⁰(G,up M)` to `H¹(G,M)` is
an epimorphism (i.e. surjective).
-/
instance up_δ_zero_epi : Epi (δ (up_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is `H¹(G,coind₁'.obj M)`, which is zero
  since coinduced representations are acyclic.
  -/
  sorry

/--
The connecting homomorphism from `Hⁿ⁺¹(G,up M)` to `Hⁿ⁺²(G,M)` is an isomorphism.
-/
instance up_δ_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso (n : ℕ) : groupCohomology (up.obj M) (n + 1) ≅ groupCohomology M (n + 2) :=
  asIso (δ (up_shortExact M) (n + 1) (n + 2) rfl)

def up_δiso_natTrans (n : ℕ) : up ⋙ functor R G (n + 1) ≅ functor R G (n + 2) where
  hom := {
    app M := (up_δiso M n).hom
    naturality := by
      simp only [up_δiso, asIso]

  }
  inv := {
    app M := (up_δiso M n).inv
    naturality := sorry
  }

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is
an epimorphism (i.e. surjective).
-/
instance up_δ_zero_epi_res {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) : Epi (δ (up_shortExact_res M φ) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is an
isomorphism.
-/
instance up_δ_isIso_res {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) (n : ℕ) : IsIso (δ (up_shortExact_res M φ) (n + 1) (n + 2) rfl)
  :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso_res {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) (n : ℕ) :
    groupCohomology (up.obj M ↓ φ) (n + 1) ≅ groupCohomology (M ↓ φ) (n + 2) := by
  have := up_δ_isIso_res M inj n
  apply asIso (δ (up_shortExact_res M φ) (n + 1) (n + 2) rfl)

omit [DecidableEq G] in
lemma ind₁'_obj_ρ : (ind₁'.obj M).ρ = M.ρ.ind₁' := rfl

omit [DecidableEq G] in
lemma ind₁'_obj_ρ_apply (g : G) : (ind₁'.obj M).ρ g = M.ρ.ind₁' g := rfl

omit [DecidableEq G] in
lemma ind₁'_π.app_hom : (ind₁'_π.app M).hom = ofHom Representation.ind₁'_π := rfl

omit [DecidableEq G] in
lemma ind₁'_π.app_apply (f : ind₁'.obj M) :
    (ind₁'_π.app M) f = Finsupp.sum f (fun _ ↦ LinearMap.id (R := R)) := rfl

def down : Rep R G ⥤ Rep R G where
  obj M := kernel (ind₁'_π.app M)
  map φ := kernel.lift _ (kernel.ι _ ≫ ind₁'.map φ) (by
    rw [Category.assoc, ind₁'_π.naturality, ←Category.assoc, kernel.condition, zero_comp])
  map_id _ := sorry
  map_comp _ := sorry

abbrev down_ses : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := kernel.ι (ind₁'_π.app M)
  g := ind₁'_π.app M
  zero := kernel.condition (ind₁'_π.app M)

omit [DecidableEq G] in
lemma down_shortExact : (down_ses M).ShortExact where
  exact   := ShortComplex.exact_kernel (ind₁'_π.app M)
  mono_f  := inferInstance
  epi_g   := inferInstance

omit [DecidableEq G] in
lemma down_shortExact_res {H : Type} [Group H] (φ : H →* G) :
    ((down_ses M).map (res φ)).ShortExact := by
  rw [res_respectsShortExact]
  exact down_shortExact M

variable [Finite G]

/--
The connecting homomorphism `H⁰(G,down.obj M) ⟶ H¹(G, M)` is an epimorphism if `G` is finite.
-/
instance down_δ_zero_epi : Epi (δ (down_shortExact M) 0 1 rfl) := by
  have := ind₁'_trivialCohomology M
  sorry

/--
The connecting homomorphism `H⁰(H,down.obj M ↓ H) ⟶ H¹(H, M ↓ H)` is an epimorphism if
`H` is a subgroup of a finite group `G`.
-/
instance down_δ_zero_res_epi {S : Type} [Group S] [DecidableEq S] {φ : S →* G}
    (inj : Function.Injective φ) : Epi (δ (down_shortExact_res M φ) 0 1 rfl) := by
  have := ind₁'_trivialCohomology M
  sorry

/--
The connecting homomorphism `Hⁿ⁺¹(G,down.obj M) ⟶ Hⁿ⁺²(G, M)` is an isomorphism
if `G` is finite.
-/
instance down_δ_isIso  (n : ℕ) : IsIso (δ (down_shortExact M) (n + 1) (n + 2) rfl) := by
  have := ind₁'_trivialCohomology M
  sorry

def down_δiso (n : ℕ) : groupCohomology M (n + 1) ≅ groupCohomology (down.obj M) (n + 2) :=
  asIso (δ (down_shortExact M) (n + 1) (n + 2) rfl)

def down_δiso_natTrans (n : ℕ) : functor R G (n + 1) ≅ down ⋙ functor R G (n + 2) where
  hom := {
    app M := (down_δiso M n).hom
    naturality := sorry
  }
  inv := {
    app M := (down_δiso M n).inv
    naturality := sorry
  }

/--
The connecting homomorphism `Hⁿ⁺¹(H,down.obj M ↓ H) ⟶ Hⁿ⁺²(H, M ↓ H)` is an isomorphism
if `H` is a subgroup of a finite group `G`.
-/
instance down_δ_res_isIso (n : ℕ) {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) : IsIso (δ (down_shortExact_res M φ) (n + 1) (n + 2) rfl) := by
  have := ind₁'_trivialCohomology M
  sorry

def down_δiso_res {H : Type} [Group H] [DecidableEq H] {φ : H →* G}
    (inj : Function.Injective φ) (n : ℕ) :
    groupCohomology (M ↓ φ) (n + 1) ≅ groupCohomology (down.obj M ↓ φ) (n + 2) :=
  have := down_δ_res_isIso M n inj
  asIso (δ (down_shortExact_res M φ) (n + 1) (n + 2) rfl)

end dimensionShift

end Rep

namespace groupCohomology

variable [Finite G]
open Rep
  dimensionShift

-- An explicit version of `isZero_of_trivialTateCohomology`
private lemma isZero_of_trivialTateCohomology' [DecidableEq G] (M : Rep R G)
    [M.TrivialTateCohomology] (n : ℤ) : IsZero ((TateComplexFunctor.obj M).homology n) :=
  TrivialTateCohomology.isZero (.id G) Function.injective_id

instance instIsIso_up_shortExact (M : Rep R G) [DecidableEq G] (n : ℤ) :
    IsIso (TateCohomology.δ (up_shortExact M) n) := by
  have _ : TrivialTateCohomology (coind₁'.obj M) := inferInstance
  refine ShortComplex.ShortExact.isIso_δ (TateCohomology.cochainsFunctor_Exact (up_shortExact M))
    n (n + 1) (by rfl) (by simp;exact isZero_of_trivialTateCohomology' (coind₁'.obj M) n)
    (by simp;exact isZero_of_trivialTateCohomology' (coind₁'.obj M) (n + 1))

instance instIsIso_down_shortExact (M : Rep R G) [DecidableEq G] (n : ℤ) :
    IsIso (TateCohomology.δ (down_shortExact M) n) := by
  have _ : TrivialTateCohomology (ind₁'.obj M) := inferInstance
  refine ShortComplex.ShortExact.isIso_δ (TateCohomology.cochainsFunctor_Exact (down_shortExact M))
    n (n + 1) (by rfl) (by simp;exact isZero_of_trivialTateCohomology' (ind₁'.obj M) n)
    (by simp;exact isZero_of_trivialTateCohomology' (ind₁'.obj M) (n + 1))

def upδiso_Tate (n : ℤ) [DecidableEq G] (M : Rep R G) :
    (TateCohomology n).obj (up.obj M) ≅ (TateCohomology (n + 1)).obj M :=
  have := instIsIso_up_shortExact M n
  asIso (TateCohomology.δ (up_shortExact M) n)

def downδiso_Tate (n : ℤ) [DecidableEq G] (M : Rep R G) :
    (TateCohomology n).obj M ≅ (TateCohomology (n + 1)).obj (down.obj M) :=
  asIso (TateCohomology.δ (down_shortExact M) n)

end groupCohomology

end

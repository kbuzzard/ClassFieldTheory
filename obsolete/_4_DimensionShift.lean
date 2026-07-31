module

public import Mathlib
public import ClassFieldTheory.GroupCohomology.«03_LeftRegular»

/-!
We define two "coinduction" functors taking values in the acyclic objects of `Rep R G`.

The first is `coind₁ G : ModuleCat R ⥤ Rep R G`.

This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ A`, where `G` acts by
its action of `R[G]`. Note that the linear maps `R[G] ⟶ A` are equivalent to the functions
`G → A`, since the elements of `G` form a basis for the group ring `R[G]`.

The second functor is `coind₁' : Rep R G ⥤ Rep R G`.

This takes a representation `M` of `G` to the space of
This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ M`, where `G` acts by
conjugation (i.e. on both `R[G]` and on `M`).

The representations `coind₁'.obj M` and `(coind₁ G).obj M.V` are isomorphic (although
the isomorphism is not simply the identity map on the space of functions `G → M`, since the
actions of `G` on these spaces are not the same).

For any `M : Rep R G` we construct two short exact sequences
(the second defined only for finite `G`):

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up M ⟶ 0` and `0 ⟶ down M ⟶ coind₁'.obj M ⟶ M ⟶ 0`.

These can be used for dimension-shifting because `coind₁'.obj M` is acyclic.
-/

open
  Rep
  leftRegular
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable {R : Type} [CommRing R]
variable (G : Type) [Group G]

namespace Rep
/--
The functor taking an `R`-module `A` to the trivial representation of `G` on `A`.
-/
def fTrivial : ModuleCat R ⥤ Rep R G where
  obj A := trivial R G A
  map f := ⟨f, by tauto⟩

#check coind

/--
The coinduced representation of an `R`-module `A`, defined to be the
space of linear maps `R[G] → A`, on which `G` acts on `R[G]`.
This is isomorphic to the function space `G → A`, where `G` acts by translation.
-/
abbrev coind₁ : ModuleCat R ⥤ Rep R G := fTrivial G ⋙ (leftRegular R G).ihom

/--
Coinduced representations are acyclic.
-/
theorem coind₁_isAcyclic (A : ModuleCat R) : ((coind₁ G).obj A).IsAcyclic :=
  /-
  There are many ways to prove this. The following method uses none of the
  technology of homological algebra, so it should be fairly easy to formalize.

  Fix a subgroup `H` of `G` and let `{gᵢ}` be a set of coset representatives for `H \ G`.
  Recall that a homogeneous `n + 1`-cochain on `H` with values in `G → A`
  is a function `σ : H^{n+2} → (G → A)` satisfying

    `σ (h * h₀, ... , h * h_{n+1}) (h * g) = σ (h₀,...,hₙ).`

  The cochain `σ` is a cocycle if it satisfies the relation

    `∑ᵢ (-1)ⁱ * σ (h₀, ... , (not hᵢ), ... , h_{n+2}) (g) = 0`.

  Given a homogeneous `n + 1`-cocycle `σ`, we'll define a homogeneous `n`-cochain `τ` by

    `τ (h₀,...,hₙ) (h * gᵢ) = σ (h,h₀,...,hₙ) (h * gᵢ)`.

  The cocycle relation for `σ` implies `∂ τ = σ`, so `σ` is a coboundary.

  Let's rephrase this in terms of inhomogeneous cocycles. The inhomogeneous cocycle
  corresponding to `σ` is

    `σ' (h₀,...,hₙ) (h * gᵢ) = σ (1,h₁,h₁*h₂,..., h₁*...*hₙ) (h * gᵢ)`

  and the inhomogeneous cochain corresponding to `τ` is

    `τ' (h₁,...,hₙ) (h * gᵢ)  = τ (1,h₁,... , h₁*...*hₙ) (h * gᵢ)`
    `                         = σ (h, 1, h₁, h₁*h₂, ..., h₁*...*hₙ) (h * gᵢ)`
    `                         = σ (1, h⁻¹, h⁻¹*h₁, h⁻¹*h₁*h₂, ..., h⁻¹* h₁*...*hₙ) (gᵢ)`
    `                         = σ' (h⁻¹,h₁,...,hₙ) (gᵢ)`.

  The last formula above defines an inhomogeneous cochain `τ'`, such that `∂ τ' = σ'`.
  -/
  sorry


def coind₁_quotientToInvariants_iso (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    ((coind₁ G).obj A).quotientToInvariants H ≅ (coind₁ (G ⧸ H)).obj A :=
  /-
  Use the isomorphism `Rep.coind₁_iso` on the left.
  Then the `H`-invariants on the left hand side are just functions `G/H ⟶ M` with the action
  of `G/H` by translation on `G/H`. This is exactly the right hand side.

  Since `quotientToInvariants` is a current PR, this will have to wait.
  -/
  sorry

/--
The `H`-invariants of `(coind₁ G).obj A` form an acyclic representation of `G ⧸ H`.
-/
lemma coind₁_quotientToInvariants_isAcyclic (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    (((coind₁ G).obj A).quotientToInvariants H).IsAcyclic := by
  apply Rep.isAcyclic_of_iso
  apply Rep.coind₁_quotientToInvariants_iso
  exact coind₁_isAcyclic (G ⧸ H) A

variable {G}

/--
The coinduced representation of a repesentation `M`, defined to be the
space of linear maps `R[G] → M`, on which `G` acts on both `R[G]` and `M`.
This is isomorphic to the function space `G → M` on which `G` acts on both `G` and `M`.
-/
abbrev coind₁' : Rep R G ⥤ Rep R G := (leftRegular R G).ihom

/--
This can be used to regard an element of `coind₁'.obj M` as a linear map of type
`leftRegular R G →ₗ[R] M`.
-/
def asₗ {M : Rep R G} (f : coind₁'.obj M) : leftRegular R G →ₗ[R] M := f

instance (M : Rep R G) : FunLike (coind₁'.obj M) (leftRegular R G) M :=
  inferInstanceAs (FunLike ((leftRegular R G) →ₗ[R] M) _ _)

@[simp] lemma asₗ_apply {M : Rep R G} (f : coind₁'.obj M) (v : leftRegular R G) : asₗ f v = f v :=
  rfl

@[ext] lemma coind₁'.ext {M : Rep R G} (f₁ f₂ : coind₁'.obj M)
    (h : ∀ g : G, f₁ (leftRegular.of g) = f₂ (leftRegular.of g)) : f₁ = f₂ := by
  apply Finsupp.lhom_ext
  intro g c
  rw [←Finsupp.smul_single_one, map_smul, h, map_smul]

lemma coind₁'_obj_ρ_apply {M : Rep R G} (g : G) (f : coind₁'.obj M) :
  (coind₁'.obj M).ρ g f = M.ρ g ∘ₗ f ∘ₗ (leftRegular R G).ρ g⁻¹ := rfl

lemma coind₁'_obj_ρ_apply₂ {M : Rep R G} (g : G) (f : coind₁'.obj M) (v : leftRegular R G):
  (coind₁'.obj M).ρ g f v = M.ρ g (f ((leftRegular R G).ρ g⁻¹ v)) := rfl

lemma coind₁'_map_apply {M N : Rep R G} (f₁ : M ⟶ N) (f₂ : coind₁'.obj M) (v : leftRegular R G) :
    coind₁'.map f₁ f₂ v = f₁ (f₂ v) := by rfl

/--
Both of the representations `coind₁'.obj M` and `(coind₁ G).obj M.V` can be thought of
as spaces of linear maps `R[G] ⟶ M`, or equivalently as spaces of functions `G → M`.
However the action of `G` on `coind₁'.obj M` is by conjugation, wheras the action
of `G` on `(coind₁ G).obj M.V` is by translation on `G`.
The isomorphism between them takes a function `f : G → M` to the function
`x ↦ M.ρ x⁻¹ (f x)`. Equivalently, if `F : R[G] ⟶ M` is a linear map then this is taken to the
linear map `R[G] ⟶ M` defined by `v ↦ ∑ x ∈ v.support, (v x) •  M.ρ x⁻¹ (F (leftRegular.of x))`.

It would be nicer to state this as an isomorphism of functors
between `coind₁'` and `(forget₂ _ _) ⋙ coind₁ G`, but this isn't needed right now.
-/
def coind₁'_iso_coind₁ (M : Rep R G) : coind₁'.obj M ≅ (coind₁ G).obj M.V where
  hom := {
    hom := ofHom {
      toFun φ := {
        toFun v := ∑ g ∈ v.support, (v g) • M.ρ g⁻¹ (φ.toFun (leftRegular.of g))
        map_add' := sorry
        map_smul' := sorry
      }
      map_add' := sorry
      map_smul' := sorry
    }
    comm g := by
      sorry
  }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry



variable (M : Rep R G)

/--
`coind₁'.obj M` is an acyclic representation of `G`.
-/
lemma coind₁'_isAcyclic : (coind₁'.obj M).IsAcyclic := by
  apply isAcyclic_of_iso
  apply coind₁'_iso_coind₁
  exact coind₁_isAcyclic G M.V

/--
The `H`-invariants in `coind₁'.obj M` form an acyclic representation of `G ⧸ H`.
-/
lemma coind₁'_quotientToInvariants_isAcyclic (H : Subgroup G) [H.Normal] :
    ((coind₁'.obj M).quotientToInvariants H).IsAcyclic := by
  have : (coind₁'.obj M).quotientToInvariants H ≅ ((coind₁ G).obj M.V).quotientToInvariants H
  · /-
    It would be helpful to define `quotientToInvariants` as a functor, in order to make this
    automatic from the isomorphism `coind₁'.obj M ≅ (coind₁ G).obj M.V`. Since `quotientToInvariants`
    is a current PR, this will need to wait.
    -/
    sorry
  exact Rep.isAcyclic_of_iso this (coind₁_quotientToInvariants_isAcyclic _ _ _)


lemma coind₁_homologyAcyclic [Finite G]  [Group G] (A : ModuleCat R) :
    ((coind₁ G).obj A).TrivialHomology :=
  sorry

open TensorProduct Representation



def ind₁' : Rep R G ⥤ Rep R G where
  obj M := Rep.of ((leftRegular R G).ρ.tprod M.ρ)
  map := by
    intro X Y f
    exact {
      hom := ofHom (LinearMap.lTensor (G →₀ R) ↑(hom f))
      comm g := by
        ext : 1
        change (LinearMap.lTensor (G →₀ R) ↑(hom f)) ∘ₗ (((leftRegular R G).ρ.tprod X.ρ)) g  =
          (((leftRegular R G).ρ.tprod Y.ρ)) g ∘ₗ (LinearMap.lTensor (G →₀ R) ↑(hom f))
        rw [Representation.tprod_apply, Representation.tprod_apply, LinearMap.lTensor_comp_map,
          LinearMap.map_comp_lTensor]
        congr 1
        ext v
        have := f.comm g
        change ((ofHom (X.ρ g) : X.V ⟶ X.V) ≫ f.hom) v = (Y.ρ g ∘ₗ ↑(hom f)) v
        simp only [ofHom_ρ, f.comm g, ModuleCat.hom_comp, ρ_hom, LinearMap.coe_comp,
          Function.comp_apply]
        rfl
    }

variable (G)
def ind₁ : ModuleCat R ⥤ Rep R G := fTrivial G ⋙ ind₁'
variable {G}
def ind₁'_iso_ind₁ : ind₁'.obj M ≅ (ind₁ G).obj M.V where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

lemma ind₁_trivialHomology (A : ModuleCat R) : ((ind₁ G).obj A).TrivialHomology :=
  sorry --requires current PR

lemma ind₁'_trivialHomology : (ind₁'.obj M).TrivialHomology := by
  sorry


/--
If `G` is finite then `G →₀ M ≃ G → M`, and therefore `ind₁'.obj M ≅ coind₁'.obj M`.
We can state this as an isomorphism of functors.
-/
def ind₁'_iso_coind₁' [Finite G] : ind₁' (R := R) (G := G) ≅ coind₁' :=
  sorry


namespace dimensionShift

/--
The inclusion of `M` in its coinduced representation. If we think of the
coinduced representation as the function space `G → M`, then this inclusion is
the map `m ↦ const G m`.
-/
def up_ι : M ⟶ coind₁'.obj M := by
  apply ofHom
  exact {
    val := {
      toFun m := {
        toFun v := ε R G v • m
        map_add' := sorry
        map_smul' := sorry
      }
      map_add' := sorry
      map_smul' := sorry
    }
    property g := by
      sorry
  }

lemma up_ι_apply {M : Rep R G} (m : M) (v : leftRegular R G) : (up_ι M) m v = (ε R G v) • m := rfl

lemma up_ι_apply_of {M : Rep R G} (m : M) (x : G) : (up_ι M) m (leftRegular.of x) = m := by
  rw [up_ι_apply, ε_of, one_smul]

/--
The inclusion of `M : Rep R G` in `coind₁'.obj M` as a natural transformation.
-/
def up_ι' : 𝟭 (Rep R G) ⟶ coind₁' where
  app := up_ι
  naturality M N f := by
    ext m x
    simp only [Functor.id_obj, Functor.id_map, Action.comp_hom, ModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_ofHom, LinearMap.llcomp_apply,
      hom_apply]
    rw [up_ι_apply_of, coind₁'_map_apply, up_ι_apply_of]

/--
The map from `M` to its coinduced representation is a monomorphism.
-/
instance : Mono (up_ι M) := by
  /-
  This is because the map is injective.
  (Choose `v` in `R[G]` such that `ε R G v = 1`; for example we can take
  `v := leftRegular.of 1`. Then we have `m = (up_ι M m).toFun v`.)
  -/
  sorry

/-
The functor taking `M : Rep R G` to `up.obj M`, defined by the short exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0`.

Since `coind₁'.obj M` is acyclic, the cohomology of `up.obj M` is a shift by one
of the cohomology of `M`.
-/
@[simps] def up : Rep R G ⥤ Rep R G where
  obj M := cokernel (up_ι'.app M)
  map f := by
    dsimp
    apply cokernel.desc _ (coind₁'.map f ≫ cokernel.π (up_ι'.app _))
    rw [←Category.assoc, ←up_ι'.naturality, Category.assoc, cokernel.condition, comp_zero]
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
    f := up_ι'.app M
    g := cokernel.π (up_ι'.app M)
    zero := cokernel.condition (up_ι'.app M)
  }
  map f := {
    τ₁ := f
    τ₂ := coind₁'.map f
    τ₃ := up.map f
    comm₁₂ := up_ι'.naturality f
    comm₂₃ := (cokernel.π_desc _ _ _).symm
  }
  map_comp f g := by
    congr
    rw [Functor.map_comp]

lemma up_shortExact : (upSes.obj M).ShortExact where
  exact := ShortComplex.exact_cokernel (up_ι'.app M)
  mono_f := inferInstanceAs (Mono (up_ι M))
  epi_g := coequalizer.π_epi


lemma up_shortExact' (H : Subgroup G) : ((upSes.obj M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact up_shortExact M

abbrev up_π : coind₁' ⟶ up (R := R) (G := G) where
  app _             := (upSes.obj _).g
  naturality _ _ _  := (upSes.map _).comm₂₃


/--
The connecting homomorphism from `H⁰(G,up M)` to `H¹(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi : Epi (δ (up_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind₁`.
  -/
  sorry

/--
The connecting homomorphism from `Hⁿ⁺¹(G,up M)` to `Hⁿ⁺²(G,M)` is an
isomorphism.
-/
instance up_δ_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso (n : ℕ) : groupCohomology (up.obj M) (n + 1) ≅ groupCohomology M (n + 2) :=
  asIso (δ (up_shortExact M) (n + 1) (n + 2) rfl)

/--
The connecting homomorphism from `H^{n+1}(G,dimensionShift M)` to `H^{n+2}(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi' (H : Subgroup G) : Epi (δ (up_shortExact' M H) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind₁`.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is an
isomorphism.
-/
instance up_δ_isIso' (H : Subgroup G) (n : ℕ) : IsIso (δ (up_shortExact' M H) (n + 1) (n + 2) rfl)
  :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso' (H : Subgroup G) (n : ℕ) :
    groupCohomology (up.obj M ↓ H) (n + 1) ≅ groupCohomology (M ↓ H) (n + 2) :=
  asIso (δ (up_shortExact' M H) (n + 1) (n + 2) rfl)


def down_π'' : ind₁' ⟶ 𝟭 (Rep R G) where
  app M := by
    rw [ind₁']
    dsimp
    apply ofHom
    exact {
      val := by
        dsimp
        apply lift
        sorry
      property := sorry
    }
  naturality := sorry

variable [Fintype G]

def down_π : coind₁'.obj M ⟶ M where
  hom := ofHom {
      toFun f := ∑ g : G, f (leftRegular.of g)
      map_add' := sorry
      map_smul' := sorry
    }
  comm := sorry

lemma down_π_apply (f : coind₁'.obj M) : down_π M f = ∑ g : G, f (leftRegular.of g) := rfl

def down_π' : coind₁' ⟶ 𝟭 (Rep R G) where
  app M := down_π M
  naturality X Y φ := by
    dsimp only [Functor.id_obj, Functor.id_map]
    ext f
    rw [hom_apply, hom_apply]
    simp only [hom_comp, Function.comp_apply, down_π_apply, map_sum]
    rw [Finset.sum_congr rfl]
    intro x _
    rw [coind₁'_map_apply]



instance : Epi (down_π M) :=
  /-
  This is because `down_π M` is surjective.
  A pre-image of an element `m : M` is the function `G → M` taking the value
  `m` at `1 : G` and `0` elsewhere. Equivalently this is the linear map
  `(leftRegular R G).V ⟶ M.V` taking `f` to `(f 1) • m`.
  -/
  sorry


def down : Rep R G ⥤ Rep R G where
  obj M := kernel (down_π'.app M)
  map φ := by
    dsimp only [Functor.id_obj]
    apply kernel.lift _ (kernel.ι _ ≫ coind₁'.map φ)
    rw [Category.assoc, down_π'.naturality, ←Category.assoc, kernel.condition, zero_comp]
  map_id := sorry
  map_comp := sorry

abbrev down_ses : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := coind₁'.obj M
  X₃ := M
  f := kernel.ι (down_π M)
  g := down_π M
  zero := kernel.condition (down_π M)

lemma down_shortExact : (down_ses M).ShortExact where
  exact := ShortComplex.exact_kernel (down_π M)
  mono_f := inferInstance
  epi_g := inferInstance

lemma down_shortExact' (H : Subgroup G) :
    ((down_ses M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact down_shortExact M

/--
The connecting homomorphism from `H^{n+1}(G,M)` to `H^{n+2}(G,down M)` is
an epimorphism (i.e. surjective).
-/
lemma down_δ_zero_epi : Epi (δ (down_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind₁`.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,M)` to `H^{n+2}(G,down M)` is an
isomorphism.
-/
instance down_δ_isIso (n : ℕ) : IsIso (δ (down_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

instance down_δ_isIso' (H : Subgroup G) (n : ℕ) :
    IsIso (δ (down_shortExact' M H) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry
/--
The isomorphism `H^{n+1}(G,up M) ≅ H^{n+2}(G,M)`.
-/
def down_δiso (n : ℕ) : groupCohomology M (n + 1) ≅ groupCohomology (down.obj M) (n + 2) :=
  asIso (δ (down_shortExact M) (n + 1) (n + 2) rfl)

/--
The isomorphism `H^{n+1}(H,up M) ≅ H^{n+2}(H,M)`.
-/
def down_δiso' (H : Subgroup G) (n : ℕ) :
    groupCohomology (M ↓ H) (n + 1) ≅ groupCohomology ((down.obj M) ↓ H) (n + 2) :=
  asIso (δ (down_shortExact' M H) (n + 1) (n + 2) rfl)

end dimensionShift
end Rep
end

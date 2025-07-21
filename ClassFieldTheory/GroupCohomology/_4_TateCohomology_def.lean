import Mathlib
open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [Finite G] [DecidableEq G]

noncomputable section

namespace Representation
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

def norm : A →ₗ[R] A :=
  let _ := Fintype.ofFinite G
  ∑ g : G, ρ g

lemma norm_comm (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm := sorry

lemma norm_comm' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm := sorry

end Representation

namespace groupCohomology

def _root_.groupHomology.zeroChainsIso (M : Rep R G) : (inhomogeneousChains M).X 0 ≅ M.V :=
  LinearEquiv.toModuleIso (Finsupp.LinearEquiv.finsuppUnique R (↑M.V) (Fin 0 → G))

def _root_.Rep.norm (M : Rep R G) : M.V ⟶ M.V := ModuleCat.ofHom M.ρ.norm

/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (zeroChainsIso M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv

lemma TateNorm_comp_d (M : Rep R G) : TateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 :=
  sorry

lemma d_comp_TateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ TateNorm M  = 0 :=
  sorry

def TateComplex.ConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := TateNorm M
  comp_d₀ := d_comp_TateNorm M
  d₀_comp := TateNorm_comp_d M

def TateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (TateComplex.ConnectData M)

lemma TateComplex_d_neg_one (M : Rep R G) : (TateComplex M).d (-1) 0 = TateNorm M := rfl

lemma TateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (TateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma TateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (TateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map φ := {
    f
    | Int.ofNat i => ((cochainsFunctor R G).map φ).f ↑i
    | Int.negSucc i => (chainsMap (MonoidHom.id G) φ).f i
    comm' := sorry
  }
  map_id := sorry
  map_comp := sorry

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

instance TateComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ n (n + 1) rfl

def TateCohomology.isoGroupCohomology' (n : ℕ) :
    TateCohomology (n + 1) ≅ groupCohomology.functor R G (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology.isoGroupHomology' (n : ℕ) :
    TateCohomology (-n - 2) ≅ groupHomology.functor R G (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology.isoGroupCohomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (n + 1)).obj M ≅ groupCohomology M (n + 1) := (isoGroupCohomology' n).app M

def TateCohomology.isoGroupHomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (-n - 2)).obj M ≅ groupHomology M (n + 1) :=  (isoGroupHomology' n).app M

def TateCohomology_zero_iso (M : Rep R G) : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
  sorry

def TateCohomology_neg_one_iso (M : Rep R G) : (TateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
    (Submodule.span R (⋃ g : G, range (1 - M.ρ g))).submoduleOf (ker M.ρ.norm)) :=
  sorry

def TateCohomology_zero_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  sorry

def TateCohomology_neg_one_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (TateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)):=
  sorry

end groupCohomology
end

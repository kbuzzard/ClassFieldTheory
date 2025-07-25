import Mathlib
import ClassFieldTheory.GroupCohomology._8_DimensionShift

/-

# Corestriction

If `S` is a finite index subgroup of `G` and `M` is a `G`-module
then there's a corestriction map `H^n(S,M) → H^n(G,M)`, defined
by averaging on H^0 and then by dimension shifting for
general `H^n`.

## Remarks

Cassels-Froehlich define this on homology for an arbitrary
morphism `S → G` and then if `G` is finite they
extend it to Tate cohomology by dimension shifting.

Arguably this filename has too large a number.

-/

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] {S : Subgroup G} [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace groupCohomology

#check ModuleCat.moduleCategory

#check Representation

def cores₀_obj {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V) :
    Representation.invariants (MonoidHom.comp ρ S.subtype) →ₗ[R] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, ρ i.out x.1, sorry⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

def cores₀ : Rep.res S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M := (H0Iso (M ↓ S.subtype)).hom ≫ (ModuleCat.ofHom (cores₀_obj M.ρ)) ≫ (H0Iso M).inv
  naturality := by
    intro X Y f
    simp_rw [← Category.assoc]
    rw [(H0Iso Y).comp_inv_eq]
    simp_rw [Category.assoc]
    rw [functor_map, map_id_comp_H0Iso_hom, (H0Iso X).inv_hom_id_assoc, Functor.comp_map,
      functor_map, map_id_comp_H0Iso_hom_assoc, (H0Iso (X ↓ S.subtype)).cancel_iso_hom_left]
    ext x
    have comm := congr(∑ i : G ⧸ S, ModuleCat.Hom.hom $(f.comm i.out) x.val)
    simpa [cores₀_obj] using comm.symm

def cores_obj : (M : Rep R G) → (n : ℕ) → (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => sorry -- data -- see kmb question on Fri morning
| M, (d + 2) =>
  let fooG := Rep.dimensionShift.up_δiso_natTrans (R := R) (G := G) d
  let fooS := Rep.dimensionShift.up_δiso_natTrans (R := R) (G := S) d
  let ih := cores_obj (up.obj M) (d + 1)
  let trans :
    res S.subtype ⋙ up ⋙ functor R S (d + 1) ⟶
    up ⋙ res S.subtype ⋙ functor R S (d + 1) := sorry -- data -- rmh says this is an iso
    -- proof uses coind_1^G | S is a coind
  (fooS).inv.app (M ↓ S.subtype) ≫ trans.app M ≫ ih ≫ (fooG).hom.app M

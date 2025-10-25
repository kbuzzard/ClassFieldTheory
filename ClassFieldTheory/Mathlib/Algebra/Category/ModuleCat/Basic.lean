import Mathlib.Algebra.Category.ModuleCat.Basic

variable {R : Type*} [CommRing R]

lemma ModuleCat.Iso_symm_iso (M N : ModuleCat R) (e : M ≅ N)  :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm := rfl

lemma ModuleCat.Iso_hom (M N : ModuleCat R) (e : M ≅ N) (x : M) :
    e.toLinearEquiv x = e.hom x := rfl

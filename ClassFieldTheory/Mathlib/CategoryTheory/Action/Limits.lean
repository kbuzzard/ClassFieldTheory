import Mathlib.CategoryTheory.Action.Limits

open CategoryTheory

universe u
variable {V : Type (u + 1)} [LargeCategory V] {G : Type u} [Monoid G] [Preadditive V]
  {X Y : Action V G}

@[simp]
lemma Action.sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := by
  rw [eq_sub_iff_add_eq, ←Action.add_hom, sub_add_cancel]

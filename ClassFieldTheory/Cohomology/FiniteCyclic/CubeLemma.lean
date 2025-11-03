import Mathlib.Combinatorics.Quiver.ReflQuiver

open CategoryTheory

universe u v

variable {A : Type u} [Category.{v} A]

variable (M000 M001 M010 M011 M100 M101 M110 M111 : A)

variable (f00x : M000 ⟶ M001) (f01x : M010 ⟶ M011) (f10x : M100 ⟶ M101) (f11x : M110 ⟶ M111)
variable (f0x0 : M000 ⟶ M010) (f0x1 : M001 ⟶ M011) (f1x0 : M100 ⟶ M110) (f1x1 : M101 ⟶ M111)
variable (fx00 : M000 ⟶ M100) (fx01 : M001 ⟶ M101) (fx10 : M010 ⟶ M110) (fx11 : M011 ⟶ M111)
-- Assume the cube commutes
variable (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1)
variable (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
variable (hx0x : fx00 ≫ f10x = f00x ≫ fx01)
variable (hx1x : fx10 ≫ f11x = f01x ≫ fx11)
variable (hxx0 : f0x0 ≫ fx10 = fx00 ≫ f1x0)
variable (hepi : Epi f00x)

include hepi h0xx h1xx hx0x hx1x hxx0 hepi in
theorem CategoryTheory.cubeLemma : f0x1 ≫ fx11 = fx01 ≫ f1x1 := by
  rw [← cancel_epi f00x]
  slice_lhs 1 2 => rw [← h0xx]
  slice_lhs 2 3 => rw [← hx1x]
  slice_lhs 1 2 => rw [hxx0]
  rw [Category.assoc]
  slice_lhs 2 3 => rw [h1xx]
  slice_lhs 1 2 => rw [hx0x]
  rw [Category.assoc]

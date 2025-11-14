import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory in
theorem CategoryTheory.comp_commSq (C' : Type*) [Category C'] {A B C D E F : C'}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (g₁ : A ⟶ D) (g₂ : C ⟶ F) (h₁ : D ⟶ E) (h₂ : E ⟶ F) (f : B ⟶ E)
    (comm1 : f₁ ≫ f = g₁ ≫ h₁) (comm2 : f₂ ≫ g₂ = f ≫ h₂) :
    (f₁ ≫ f₂) ≫ g₂ = g₁ ≫ (h₁ ≫ h₂) := by
  rw [← Category.assoc, ← comm1, Category.assoc, comm2, Category.assoc]

import ClassFieldTheory.Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Hom

theorem isLocalHom_iff_one {R S F : Type*} [Monoid R] [Monoid S]
    [FunLike F R S] [MulHomClass F R S] {f : F} (hf : (⇑f).Surjective) :
    IsLocalHom f ↔ ∀ ⦃x⦄, f x = 1 → IsUnit x := by
  refine ⟨fun h x hx ↦ .of_map f _ <| hx ▸ isUnit_one, fun h ↦ ⟨fun x hx ↦ ?_⟩⟩
  obtain ⟨y, hxy, hyx⟩ := isUnit_iff_exists.mp hx
  obtain ⟨y, rfl⟩ := hf y
  rw [← map_mul] at hxy hyx
  exact .of_mul (h hxy) (h hyx)

import Mathlib
import ClassFieldTheory.GroupCohomology._06_CyclicGroup_v2

noncomputable section
variable {R G : Type} [CommRing R] [Group G]

open LinearMap


section abstract_Herbrand_Quotient

abbrev herbrandRing.X₀ : MvPolynomial (Fin 2) R := MvPolynomial.X 0
abbrev herbrandRing.X₁ : MvPolynomial (Fin 2) R := MvPolynomial.X 1

open herbrandRing

def herbrandIdeal : Ideal (MvPolynomial (Fin 2) R) := by
  apply Ideal.span {X₀ * X₁}

variable (R)
def herbrandRing := (MvPolynomial (Fin 2) R) ⧸ herbrandIdeal

instance : CommRing (herbrandRing R) :=
  inferInstanceAs (CommRing ((MvPolynomial (Fin 2) R) ⧸ herbrandIdeal))
instance : Algebra R (herbrandRing R) :=
  inferInstanceAs (Algebra R ((MvPolynomial (Fin 2) R) ⧸ herbrandIdeal))
def herbrandRing.d₀ : herbrandRing R := Quotient.mk _ X₀
def herbrandRing.d₁ : herbrandRing R := Quotient.mk _ X₁


namespace herbrandModule

variable (A : Type) [AddCommGroup A] [Module R A]

def of (φ₀ φ₁ : A →ₗ[R] A) (h01 : φ₀ ∘ₗ φ₁ = 0) (h10 : φ₁ ∘ₗ φ₀ = 0) :
    Module (herbrandRing R) A := by
  let inst : Module (MvPolynomial (Fin 2) R) A
  · sorry
    /- make `A` a module over the polynomial ring in such a way that
    `X₀` and `X₁` act by `φ₀` and `φ₁` respectively.-/
  have this (a : A) : X₀ (R := R) • a = φ₀ a
  · sorry
  have that (a : A) : X₁ (R := R) • a = φ₁ a
  · sorry
  unfold herbrandRing herbrandIdeal
  apply Module.IsTorsionBy.module
  intro a
  rw [mul_smul, that, this, ←comp_apply, h01, zero_apply]


variable [Module (herbrandRing R) A] [IsScalarTower R (herbrandRing R) A]

@[simps] def δ₀ : A →ₗ[R] A where
  toFun a := d₀ R • a
  map_add' := sorry
  map_smul' := sorry

@[simps] def δ₁ : A →ₗ[R] A where
  toFun a := d₁ R • a
  map_add' := sorry
  map_smul' := sorry

abbrev Z0 := ker (δ₀ R A)
abbrev Z1 := ker (δ₁ R A)
abbrev B0 := range (δ₁ R A)
abbrev B1 := range (δ₀ R A)
def H0 := (Z0 R A) ⧸ (B0 R A).submoduleOf (Z0 R A)
def H1 := (Z1 R A) ⧸ (B1 R A).submoduleOf (Z1 R A)

instance : AddCommGroup (H0 R A) :=
  inferInstanceAs (AddCommGroup ((Z0 R A) ⧸ (B0 R A).submoduleOf (Z0 R A)))
instance : Module R (H0 R A) :=
  inferInstanceAs (Module R ((Z0 R A) ⧸ (B0 R A).submoduleOf (Z0 R A)))
instance : AddCommGroup (H1 R A) :=
  inferInstanceAs (AddCommGroup ((Z1 R A) ⧸ (B1 R A).submoduleOf (Z1 R A)))
instance : Module R (H1 R A) :=
  inferInstanceAs (Module R ((Z1 R A) ⧸ (B1 R A).submoduleOf (Z1 R A)))

def quotient : ℚ := Nat.card (H0 R A) / Nat.card (H1 R A)

lemma B0_le_Z0 : B0 R A ≤ Z0 R A := sorry
lemma B1_le_Z1 : B1 R A ≤ Z1 R A := sorry

lemma quotient_eq_one_of_finite [Finite A] : quotient R A = 1 := sorry

lemma quotient_eq_quotient_submodule_mul_quotient_quotientmodule
    (S : Submodule (herbrandRing R) A) : quotient R A = quotient R S * quotient R (A ⧸ S) :=
  sorry

abbrev _root_.HerbrandCat := ModuleCat (herbrandRing R)

def _root_.HerbrandCat.of {φ₀ φ₁ : A →ₗ[R] A} (h01 : φ₀ ∘ₗ φ₁ = 0) (h10 : φ₁ ∘ₗ φ₀ = 0) :
    HerbrandCat R := by
  let : Module (herbrandRing R) A
  · exact herbrandModule.of R A φ₀ φ₁ h01 h10
  exact ModuleCat.of (herbrandRing R) A

end herbrandModule





end abstract_Herbrand_Quotient



namespace Representation

variable {A : Type} [AddCommGroup A] [Module R A]
variable [IsCyclic G] [Fintype G]
variable (ρ : Representation R G A)

def oneSubGen : A →ₗ[R] A := 1 - ρ (gen G)

def norm : A →ₗ[R] A := ∑ g : G, ρ g

lemma oneSubGen_comp_norm : oneSubGen ρ ∘ₗ norm ρ = 0 := sorry

lemma norm_comp_oneSubGen : norm ρ ∘ₗ oneSubGen ρ = 0 := sorry

open
  CategoryTheory
  ConcreteCategory

def toHerbrandModule : Rep R G ⥤ HerbrandCat R where
  obj M := HerbrandCat.of R M.V M.ρ.oneSubGen_comp_norm M.ρ.norm_comp_oneSubGen
  map f := ofHom {
    toFun := hom f
    map_add' _ _ := by simp
    map_smul' _ _ := by sorry }
  map_id M := by
    sorry
  map_comp f₁ f₂ := by
    sorry



def herbrandModule : Module (herbrandRing R) A :=
  herbrandModule.of R A _ _ (oneSubGen_comp_norm ρ) (norm_comp_oneSubGen ρ)

def herbrandQuotient : ℚ :=
  let _ := ρ.herbrandModule
  herbrandModule.quotient R A

lemma herbrandQuotient_eq_one_of_finite [Finite A] :
    ρ.herbrandQuotient = 1 := by
  let _ := ρ.herbrandModule
  have : IsScalarTower R (herbrandRing R) A
  · sorry
  apply herbrandModule.quotient_eq_one_of_finite

end Representation
end

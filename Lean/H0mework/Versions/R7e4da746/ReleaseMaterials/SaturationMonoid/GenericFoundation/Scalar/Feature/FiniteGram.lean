import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Coordinates (ι : Type*) := EuclideanSpace ℂ ι

def action (gram : Matrix ι ι ℂ) : Coordinates ι →ₗ[ℂ] Coordinates ι :=
  gram.toEuclideanLin

abbrev Kernel (gram : Matrix ι ι ℂ) := (action gram).ker

def Compatible (gram : Matrix ι ι ℂ) (rhs : Coordinates ι) : Prop :=
  ∀ z : Coordinates ι, action gram z = 0 → inner ℂ z rhs = 0

private theorem rhs_mem_range (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) :
    rhs ∈ (action gram).range := by
  have orthogonal : rhs ∈ (Kernel gram)ᗮ := by
    intro z zero
    exact compatible z zero
  have symmetric : (action gram).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hermitian
  rw [LinearMap.orthogonal_ker, symmetric.adjoint_eq] at orthogonal
  exact orthogonal

/-- Invert the actual image; no invertibility or solution witness is supplied. -/
def solutionClass (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) :
    Coordinates ι ⧸ Kernel gram :=
  (action gram).quotKerEquivRange.symm
    ⟨rhs, rhs_mem_range gram hermitian rhs compatible⟩

def coefficients (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) : Coordinates ι :=
  ((Kernel gram).quotientEquivOrthogonal
    (solutionClass gram hermitian rhs compatible) : Coordinates ι)

theorem coefficients_orthogonal (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) :
    coefficients gram hermitian rhs compatible ∈ (Kernel gram)ᗮ :=
  ((Kernel gram).quotientEquivOrthogonal
    (solutionClass gram hermitian rhs compatible)).property

theorem coefficients_class (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) :
    (Kernel gram).mkQ (coefficients gram hermitian rhs compatible) =
      solutionClass gram hermitian rhs compatible := by
  have original := (Kernel gram).quotientEquivOrthogonal.symm_apply_apply
    (solutionClass gram hermitian rhs compatible)
  rw [Submodule.quotientEquivOrthogonal_symm_eq_mk] at original
  exact original

theorem equation (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) :
    action gram (coefficients gram hermitian rhs compatible) = rhs := by
  have generated := congrArg (fun q : Coordinates ι ⧸ Kernel gram =>
    ((action gram).quotKerEquivRange q : Coordinates ι))
    (coefficients_class gram hermitian rhs compatible)
  change ((action gram).quotKerEquivRange
    (Submodule.Quotient.mk (coefficients gram hermitian rhs compatible)) : Coordinates ι) =
    ((action gram).quotKerEquivRange
      (solutionClass gram hermitian rhs compatible) : Coordinates ι) at generated
  simpa only [LinearMap.quotKerEquivRange_apply_mk, solutionClass,
    LinearEquiv.apply_symm_apply] using generated

/-- All coefficient ambiguity is retained as the original Gram kernel. -/
theorem full_fibre (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs) (x : Coordinates ι) :
    action gram x = rhs ↔
      x - coefficients gram hermitian rhs compatible ∈ Kernel gram := by
  change _ ↔ action gram (x - coefficients gram hermitian rhs compatible) = 0
  rw [map_sub, equation, sub_eq_zero]

def sourceEffect {H : Type*} [AddCommGroup H] [Module ℂ H]
    (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs)
    (synthesis : Coordinates ι →ₗ[ℂ] H)
    (relations : Kernel gram ≤ synthesis.ker) : H :=
  (Kernel gram).liftQ synthesis relations
    (solutionClass gram hermitian rhs compatible)

theorem source_effect_eq {H : Type*} [AddCommGroup H] [Module ℂ H]
    (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs)
    (synthesis : Coordinates ι →ₗ[ℂ] H)
    (relations : Kernel gram ≤ synthesis.ker) :
    sourceEffect gram hermitian rhs compatible synthesis relations =
      synthesis (coefficients gram hermitian rhs compatible) := by
  rw [sourceEffect, ← coefficients_class gram hermitian rhs compatible]
  rfl

theorem source_effect_of_equation {H : Type*} [AddCommGroup H] [Module ℂ H]
    (gram : Matrix ι ι ℂ) (hermitian : gram.IsHermitian)
    (rhs : Coordinates ι) (compatible : Compatible gram rhs)
    (synthesis : Coordinates ι →ₗ[ℂ] H)
    (relations : Kernel gram ≤ synthesis.ker)
    (x : Coordinates ι) (generated : action gram x = rhs) :
    synthesis x = sourceEffect gram hermitian rhs compatible synthesis relations := by
  have same := relations ((full_fibre gram hermitian rhs compatible x).mp generated)
  change synthesis (x - coefficients gram hermitian rhs compatible) = 0 at same
  rw [map_sub, sub_eq_zero] at same
  exact same.trans (source_effect_eq gram hermitian rhs compatible synthesis relations).symm

end SourceGeneratedFiniteGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

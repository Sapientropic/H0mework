import H0mework.Realization.Integral.GroupRingPairing
import H0mework.Realization.Coherent.Completion
import H0mework.Realization.Integral.FaithfulAction

/-!
# Relative-source coefficient residual

The integral group ring enters its complex scalar extension faithfully.  A
nonzero complex scalar of norm below one cannot be hidden inside an integral
basis coefficient.  Consequently, inverse-character normalization followed
by an integral translation is an explicit action-escape residual, not an
integral source transition.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedRelativeSourceCoefficientResidual

open SourceGeneratedFaithfulIntegralFace
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentCompletion
open SourceGeneratedIntegralGroupRingPerfectPair
open scoped TensorProduct

noncomputable section

universe u
variable {G : Type u} [Group G]

/-- Complexification of the literal coefficient detector at one integral
basis element. -/
def complexifiedCoefficient (element : G) :
    ComplexifiedCarrier (Carrier G) →ₗ[ℂ] ℂ :=
  complexifiedLinearMap
    ((Int.castRingHom ℂ).toIntAlgHom.toLinearMap.comp
      (coefficientFunctional element))

@[simp] theorem complexifiedCoefficient_tmul
    (element : G) (coefficient : ℂ) (value : Carrier G) :
    complexifiedCoefficient element (coefficient ⊗ₜ[ℤ] value) =
      coefficient * (value.coeff element : ℂ) := by
  simp [complexifiedCoefficient, coefficientFunctional, smul_eq_mul]

/-- The integral group ring has no coefficient kernel inside its canonical
complex scalar extension. -/
theorem integralToComplexification_injective :
    Function.Injective
      (integralToComplexification :
        Carrier G →ₗ[ℤ] ComplexifiedCarrier (Carrier G)) := by
  intro left right equality
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro element
  have atElement := congrArg (complexifiedCoefficient element) equality
  have castEquality : (left.coeff element : ℂ) = right.coeff element := by
    simpa [integralToComplexification_apply] using atElement
  exact_mod_cast castEquality

/-- Canonical faithful integral face of the group ring in its scalar
extension. -/
def integralGroupRingComplexificationFace :
    FaithfulIntegralFace
      (L := Carrier G) (Ambient := ComplexifiedCarrier (Carrier G)) where
  realization := integralToComplexification
  injective := integralToComplexification_injective

/-- No integral group-ring vector can become a nonzero proper-subunit scalar
multiple of one complexified basis vector. -/
theorem no_integral_lift_of_nonzero_norm_lt_one
    (element : G) (coefficient : ℂ)
    (nonzero : coefficient ≠ 0) (small : ‖coefficient‖ < 1) :
    ¬ ∃ value : Carrier G,
      integralToComplexification value =
        coefficient ⊗ₜ[ℤ] delta element := by
  rintro ⟨value, equality⟩
  have coefficientEquality := congrArg
    (complexifiedCoefficient element) equality
  have castEquality : (value.coeff element : ℂ) = coefficient := by
    simpa [integralToComplexification_apply, delta] using coefficientEquality
  have integerNonzero : value.coeff element ≠ 0 := by
    intro integerZero
    apply nonzero
    rw [← castEquality, integerZero]
    simp
  have integerAbs : (1 : ℤ) ≤ |value.coeff element| :=
    Int.one_le_abs integerNonzero
  have realAbs : (1 : ℝ) ≤ |(value.coeff element : ℝ)| := by
    exact_mod_cast integerAbs
  have integerNorm : (1 : ℝ) ≤ ‖(value.coeff element : ℂ)‖ := by
    simpa using realAbs
  rw [castEquality] at integerNorm
  exact (not_lt_of_ge integerNorm) small

/-- Complexified left translation followed by one scalar normalization. -/
def scaledComplexifiedLeftTranslation
    (coefficient : ℂ) (element : G) :
    ComplexifiedCarrier (Carrier G) →ₗ[ℂ]
      ComplexifiedCarrier (Carrier G) :=
  coefficient • TensorProduct.AlgebraTensorModule.map LinearMap.id
    (leftTranslation element).toLinearMap

@[simp] theorem scaledComplexifiedLeftTranslation_delta_one
    (coefficient : ℂ) (element : G) :
    scaledComplexifiedLeftTranslation coefficient element
        (integralToComplexification (delta (1 : G))) =
      coefficient ⊗ₜ[ℤ] delta element := by
  simp [scaledComplexifiedLeftTranslation, integralToComplexification_apply]
  rw [TensorProduct.smul_tmul']
  simp

/-- A proper-subunit normalized translation visibly leaves the source-owned
integral face at its identity occurrence. -/
theorem scaledComplexifiedLeftTranslation_delta_one_escapes
    (element : G) (coefficient : ℂ)
    (nonzero : coefficient ≠ 0) (small : ‖coefficient‖ < 1) :
    (scaledComplexifiedLeftTranslation coefficient element).restrictScalars ℤ
        ((integralGroupRingComplexificationFace (G := G)).realization
          (delta (1 : G))) ∉
      LinearMap.range
        (integralGroupRingComplexificationFace (G := G)).realization := by
  rintro ⟨value, equality⟩
  apply no_integral_lift_of_nonzero_norm_lt_one element coefficient
    nonzero small
  refine ⟨value, ?_⟩
  change integralToComplexification value =
    scaledComplexifiedLeftTranslation coefficient element
      (integralToComplexification (delta (1 : G))) at equality
  rw [scaledComplexifiedLeftTranslation_delta_one] at equality
  exact equality

/-- The escaping identity occurrence as an existing generic action residual,
not a failed or freely renewed source transition. -/
def scaledComplexifiedLeftTranslationResidual
    (element : G) (coefficient : ℂ)
    (nonzero : coefficient ≠ 0) (small : ‖coefficient‖ < 1) :
    ActionEscapeCoordinate
      (integralGroupRingComplexificationFace (G := G))
      ((scaledComplexifiedLeftTranslation coefficient element).restrictScalars ℤ) where
  source := delta (1 : G)
  escapes := scaledComplexifiedLeftTranslation_delta_one_escapes
    element coefficient nonzero small

end

end SourceGeneratedRelativeSourceCoefficientResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

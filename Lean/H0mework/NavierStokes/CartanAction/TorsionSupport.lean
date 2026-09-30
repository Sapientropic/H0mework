import H0mework.NavierStokes.CartanAction.SpinSupport

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanTorsionSupport

open PhysicsCore DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource StageNineLorentzConnectionVariation
open StageNineCartanTorsionThreeFormCoordinates StageNineCartanTorsionThreeFormEquiv
open StageNineCartanContorsionTorsionEquiv StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalGravityCurvatureVariancePairing StageNineResidualLinearPlebanskiTorsionReduction
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeSourceCartan NativeCartanSpinSupport

noncomputable section

theorem undual_repeated (velocity : PhysicalSpace) (internal contracted direction : Fin 4) :
    orderedPhysicalBivectorThreeFormComponent (internalBivectorUndualThreeForm (spinResponse velocity))
      internal contracted contracted internal direction = 0 := by
  fin_cases internal <;> fin_cases contracted <;> fin_cases direction <;>
    simp [orderedPhysicalBivectorThreeFormComponent, orderedInternalBivectorThreeFormComponent,
      internalBivectorUndualThreeForm, lorentzianCoframeHodge,
      orientedLorentzBivectorBasisCoefficient, orientedLorentzThreeFormBasisCoefficient,
      threeFormFirst, threeFormSecond, threeFormThird, pairFirst, pairSecond,
      Fin.sum_univ_four, Fin.sum_univ_six,
      spinResponse_support, missingTripleOfOneForm, lorentzBivectorFirst, lorentzBivectorSecond]

private theorem oriented_swap_last (triple first second third : Fin 4) :
    orientedLorentzThreeFormBasisCoefficient triple first second third =
      -orientedLorentzThreeFormBasisCoefficient triple first third second := by
  unfold orientedLorentzThreeFormBasisCoefficient
  ring

private theorem ordered_swap_last (form : PhysicalBivectorThreeForm) (a b first second third : Fin 4) :
    orderedPhysicalBivectorThreeFormComponent form a b first second third =
      -orderedPhysicalBivectorThreeFormComponent form a b first third second := by
  unfold orderedPhysicalBivectorThreeFormComponent
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro triple _
  rw [oriented_swap_last triple first second third]
  ring

theorem undual_repeated_last (velocity : PhysicalSpace) (internal contracted direction : Fin 4) :
    orderedPhysicalBivectorThreeFormComponent (internalBivectorUndualThreeForm (spinResponse velocity))
      internal contracted contracted direction internal = 0 := by
  rw [ordered_swap_last, undual_repeated, neg_zero]

theorem first_contraction_repeated (velocity : PhysicalSpace) (internal direction : Fin 4) :
    cartanThreeFormFirstContraction (NativeCanonicalFluidCoframe.coframe velocity)
      (internalBivectorUndualThreeForm (spinResponse velocity)) internal internal direction = 0 := by
  simp [cartanThreeFormFirstContraction, NativeCanonicalFluidCoframe.coframe_inv,
    Matrix.diagonal_apply, ite_mul, undual_repeated]

theorem first_contraction_repeated_last (velocity : PhysicalSpace) (internal direction : Fin 4) :
    cartanThreeFormFirstContraction (NativeCanonicalFluidCoframe.coframe velocity)
      (internalBivectorUndualThreeForm (spinResponse velocity)) internal direction internal = 0 := by
  simp [cartanThreeFormFirstContraction, NativeCanonicalFluidCoframe.coframe_inv,
    Matrix.diagonal_apply, ite_mul, undual_repeated_last]

theorem double_contraction_zero (velocity : PhysicalSpace) (direction : Fin 4) :
    cartanThreeFormDoubleContraction (NativeCanonicalFluidCoframe.coframe velocity)
      (internalBivectorUndualThreeForm (spinResponse velocity)) direction = 0 := by
  simp [cartanThreeFormDoubleContraction, NativeCanonicalFluidCoframe.coframe_inv,
    Matrix.diagonal_apply, ite_mul, first_contraction_repeated]

/-- The original KIN-3 output has no repeated internal/spacetime torsion component. -/
theorem torsion_support (velocity : PhysicalSpace) (pair : Fin 6) (internal : Fin 4)
    (repeated : internal = pairFirst pair ∨ internal = pairSecond pair) :
    (torsion velocity).component pair internal = 0 := by
  rcases repeated with first | second
  · rw [first]
    simp [torsion, cartanTorsionOfThreeForm, cartanTorsionOfUndualThreeForm,
      first_contraction_repeated, double_contraction_zero]
  · rw [second]
    simp [torsion, cartanTorsionOfThreeForm, cartanTorsionOfUndualThreeForm,
      first_contraction_repeated_last, double_contraction_zero]

end
end SaturationMonoid.NavierStokes.NativeCartanTorsionSupport

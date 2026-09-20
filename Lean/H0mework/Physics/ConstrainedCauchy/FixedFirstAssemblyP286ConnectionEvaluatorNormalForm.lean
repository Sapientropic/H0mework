import H0mework.Physics.ConstrainedCauchy.FixedFirstAssemblyGeneratedJointNormalForm

/-!
# FirstAssembly P286 connection evaluator normal form

This module unfolds the exact revised-current trace generated from
`firstGravityCurrent`: the root-owned P286 negative-gradient A/F/B step,
the GL gravity occurrence, and the final constitutive refresh.  It identifies
the next open residual coordinate with the Yang--Mills Euler three-form of
that generated refreshed state.

The accompanying scalar action defect is nonnegative and vanishes exactly
when the evaluator coordinate vanishes.  No theorem here asserts that the
finite step settles the connection row or preserves the old SafeFinal
residual; zero and nonzero remain honest dependent consumers of the revised
occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyP286ConnectionEvaluatorNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathGLCoframe
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyGeneratedJointNormalForm
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286JointYangMillsGradientFlow

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev SafeFinal : StageNineHolonomicConfiguration :=
  firstGravityCurrent.configuration

def firstAssemblyGeneratedP286Stage : StageNineHolonomicConfiguration :=
  (rootActionAt firstGravityCurrent).p286Stage

private abbrev GravityOccurrence :=
  sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
    Source firstAssemblyGeneratedP286Stage

def firstAssemblyGeneratedGravityFinal : StageNineHolonomicConfiguration :=
  GravityOccurrence.finalActual

def firstAssemblyGeneratedP286Refreshed : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout Source
    firstAssemblyGeneratedGravityFinal

theorem firstAssembly_p286Stage_eq_sourceEulerStep :
    firstAssemblyGeneratedP286Stage =
      p286JointYangMillsEulerStep positiveSmoothUnifiedSource
        firstGravityCurrent.configuration :=
  rfl

theorem firstAssembly_configuration_eq_p286Refreshed :
    firstAssemblyCurrent.configuration =
      firstAssemblyGeneratedP286Refreshed :=
  rfl

theorem firstAssembly_p286Refreshed_gaugeConnection_eq_p286Stage :
    firstAssemblyGeneratedP286Refreshed.gaugeConnection =
      firstAssemblyGeneratedP286Stage.gaugeConnection := by
  rw [show firstAssemblyGeneratedP286Refreshed.gaugeConnection =
      firstAssemblyGeneratedGravityFinal.gaugeConnection by rfl]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_gaugeConnection
      Source firstAssemblyGeneratedP286Stage

theorem firstAssembly_p286Stage_connectionCoordinate_eq_source_sub_gradient
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        firstAssemblyGeneratedP286Stage point =
      holonomicP286GaugeConnectionCoordinate
          firstGravityCurrent.configuration point -
        p286JointYangMillsActionGradient positiveSmoothUnifiedSource
          firstGravityCurrent.configuration point := by
  rw [firstAssembly_p286Stage_eq_sourceEulerStep]
  exact p286JointYangMillsEulerStep_connectionCoordinate Source SafeFinal point

theorem firstAssembly_p286Refreshed_auxiliary_eq_generatedConstitutive
    (point : BasePoint) :
    firstAssemblyGeneratedP286Refreshed.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (firstAssemblyGeneratedGravityFinal.coframe point)
        (holonomicGaugeCurvature firstAssemblyGeneratedGravityFinal point) :=
  rfl

theorem firstAssembly_connectionEvaluatorDefect_eq_refreshedEuler
    (point : BasePoint) :
    firstAssemblyGeneratedP286ConnectionEvaluatorDefect point =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        firstAssemblyGeneratedP286Refreshed point := by
  calc
    firstAssemblyGeneratedP286ConnectionEvaluatorDefect point =
        (firstAssemblyGeneratedPointwiseJointNormalForm point
          ).p286GaugeConnection := rfl
    _ = ((rootResidualAt firstAssemblyCurrent).classicalJoint point
          ).p286GaugeConnection := by
      exact congrArg
        DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeConnection
        (root_firstAssembly_classicalJoint_eq_generatedNormalForm point).symm
    _ = holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
          firstAssemblyCurrent.configuration point := rfl
    _ = holonomicFormNativeP286GaugeEulerThreeForm Source 0
          firstAssemblyGeneratedP286Refreshed point := by
      rw [firstAssembly_configuration_eq_p286Refreshed]

theorem firstAssembly_connectionEvaluatorDefect_allPoint_zero_iff_yangMills :
    (∀ point : BasePoint,
        firstAssemblyGeneratedP286ConnectionEvaluatorDefect point = 0) ↔
      FormNativeP286GaugeYangMillsPointwiseEquation positiveSmoothUnifiedSource
        firstAssemblyGeneratedGravityFinal := by
  change
    (∀ point : BasePoint,
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        firstAssemblyGeneratedP286Refreshed point = 0) ↔
      FormNativeP286GaugeConnectionPointwiseEquation positiveSmoothUnifiedSource
        firstAssemblyGeneratedP286Refreshed
  constructor
  · intro zero point
    exact
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
        positiveSmoothUnifiedSource 0 firstAssemblyGeneratedP286Refreshed
          point).mp (zero point)
  · intro equation point
    exact
      (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
        positiveSmoothUnifiedSource 0 firstAssemblyGeneratedP286Refreshed
          point).mpr
          (equation point)

theorem firstAssembly_connectionEvaluatorDefect_allPoint_zero_iff_wholeField :
    (∀ point : BasePoint,
        firstAssemblyGeneratedP286ConnectionEvaluatorDefect point = 0) ↔
      ∀ point : BasePoint,
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
            firstAssemblyGeneratedP286Refreshed point =
          formNativePhysicalChargedGaugeCurrentThreeForm
            positiveSmoothUnifiedSource 0 point
            (toContinuumPointField
              firstAssemblyGeneratedGravityFinal point) := by
  rw [firstAssembly_connectionEvaluatorDefect_allPoint_zero_iff_yangMills]
  exact
    formNativeP286GaugeYangMillsPointwiseEquation_iff_wholeField
      positiveSmoothUnifiedSource firstAssemblyGeneratedGravityFinal

/-- Existing source-native entropy carrier on the revised exact current. -/
def firstAssemblyGeneratedP286ConnectionActionDefect
    (point : BasePoint) : ℝ :=
  p286JointYangMillsActionDefect positiveSmoothUnifiedSource
    firstAssemblyGeneratedP286Refreshed point

theorem firstAssemblyGeneratedP286ConnectionActionDefect_nonnegative
    (point : BasePoint) :
    0 ≤ firstAssemblyGeneratedP286ConnectionActionDefect point :=
  p286JointYangMillsActionDefect_nonnegative positiveSmoothUnifiedSource
    firstAssemblyGeneratedP286Refreshed point

theorem
    firstAssemblyGeneratedP286ConnectionActionDefect_eq_zero_iff_evaluator_zero
    (point : BasePoint) :
    firstAssemblyGeneratedP286ConnectionActionDefect point = 0 ↔
      firstAssemblyGeneratedP286ConnectionEvaluatorDefect point = 0 := by
  rw [firstAssemblyGeneratedP286ConnectionActionDefect,
    p286JointYangMillsActionDefect_eq_zero_iff]
  rw [firstAssembly_connectionEvaluatorDefect_eq_refreshedEuler]

theorem
    firstAssemblyGeneratedP286ConnectionActionDefect_pos_iff_evaluator_nonzero
    (point : BasePoint) :
    0 < firstAssemblyGeneratedP286ConnectionActionDefect point ↔
      firstAssemblyGeneratedP286ConnectionEvaluatorDefect point ≠ 0 := by
  constructor
  · intro positive evaluatorZero
    have scalarZero :=
      (firstAssemblyGeneratedP286ConnectionActionDefect_eq_zero_iff_evaluator_zero
        point).2 evaluatorZero
    rw [scalarZero] at positive
    exact (lt_irrefl 0) positive
  · intro evaluatorNonzero
    have scalarNonzero :
        firstAssemblyGeneratedP286ConnectionActionDefect point ≠ 0 := by
      intro scalarZero
      exact evaluatorNonzero
        ((firstAssemblyGeneratedP286ConnectionActionDefect_eq_zero_iff_evaluator_zero
          point).1 scalarZero)
    exact lt_of_le_of_ne
      (firstAssemblyGeneratedP286ConnectionActionDefect_nonnegative point)
      scalarNonzero.symm

/-- Exact same-row consumer for a computed nonzero revised connection
coordinate. -/
def firstAssemblyGeneratedP286ConnectionObstructionAt
    (point : BasePoint)
    (nonzero : firstAssemblyGeneratedP286ConnectionEvaluatorDefect point ≠ 0) :
    N.ObstructionAt firstAssemblyCurrent :=
  firstAssemblyGeneratedJointNormalFormObstructionAt point <| by
    intro wholeZero
    have coordinateZero := congrArg
      DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeConnection
      wholeZero
    exact nonzero <| by
      simpa only [zero_p286GaugeConnection,
        firstAssemblyGeneratedPointwiseJointNormalForm_p286GaugeConnection_eq_evaluatorDefect]
        using coordinateZero

#print axioms firstAssembly_p286Stage_eq_sourceEulerStep
#print axioms firstAssembly_configuration_eq_p286Refreshed
#print axioms firstAssembly_p286Refreshed_gaugeConnection_eq_p286Stage
#print axioms
  firstAssembly_p286Stage_connectionCoordinate_eq_source_sub_gradient
#print axioms
  firstAssembly_p286Refreshed_auxiliary_eq_generatedConstitutive
#print axioms firstAssembly_connectionEvaluatorDefect_eq_refreshedEuler
#print axioms
  firstAssembly_connectionEvaluatorDefect_allPoint_zero_iff_yangMills
#print axioms
  firstAssembly_connectionEvaluatorDefect_allPoint_zero_iff_wholeField
#print axioms
  firstAssemblyGeneratedP286ConnectionActionDefect_nonnegative
#print axioms
  firstAssemblyGeneratedP286ConnectionActionDefect_eq_zero_iff_evaluator_zero
#print axioms
  firstAssemblyGeneratedP286ConnectionActionDefect_pos_iff_evaluator_nonzero

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyP286ConnectionEvaluatorNormalForm
end PhysicsCore
end SaturationMonoid

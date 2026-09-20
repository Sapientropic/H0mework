import H0mework.Physics.CartanAction.CartanP286CriticalPair
import H0mework.Physics.FinalJoint.FixedGlobalRegularity
import H0mework.Physics.RepairedAction.ActionSpatialSectionResidual

/-!
# Fixed P506/L0 repaired-constitutive--Cartan whole-field write

This module composes two existing source/action-owned operators on the
authoritative globally smooth fixed P506/L0 predecessor:

```text
fixedP506L0FinalCommonActionActual 0
  -> repaired constitutive spatial-section operator
  -> current-native Cartan/reaction restart.
```

Both constructors receive only the same fixed source and the current produced
by the preceding leg.  No residual, support, target field, branch, equation
receipt, or zero-fiber witness enters the write.

The outer Cartan leg closes gravity simplicity, gravity auxiliary, and the
Lorentz equation at every nondegenerate point, while retaining the repaired
section's P286 fields.  Consequently the repaired section's action-generated
P286 auxiliary zero survives on the outer actual, and the full P286 Euler
three-form is preserved literally by the Cartan--P286 critical pair.

This is a positive coupled whole-field write.  It does not claim that the
remaining scalar, matter, adjoint-matter, or coframe residuals vanish.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanWholeFieldWrite

open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanP286CriticalPair
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionResidual
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

private abbrev Predecessor : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

/-! ## Source/current-only composite -/

/-- First leg: the authoritative repaired constitutive operator assembled as
one four-dimensional spatial section from the smooth fixed predecessor. -/
def fixedP506L0FinalCommonRepairedConstitutiveSectionActual :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
    positiveSmoothUnifiedSource Predecessor

/-- Second leg: run the current-native Cartan/reaction write on the complete
output of the repaired spatial-section producer. -/
def fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual

/-! ## Literal primitive provenance -/

@[simp] theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe :
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.coframe =
      Predecessor.coframe := by
  calc
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.coframe =
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual.coframe :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual
    _ = Predecessor.coframe :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource Predecessor

@[simp] theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeConnection :
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.gaugeConnection =
      Predecessor.gaugeConnection := by
  calc
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.gaugeConnection =
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual.gaugeConnection :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual
    _ = Predecessor.gaugeConnection :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource Predecessor

@[simp] theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_scalar :
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.scalar =
      Predecessor.scalar := by
  calc
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.scalar =
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual.scalar :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar
        positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual
    _ = Predecessor.scalar :=
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource Predecessor

/-! ## Outer gravity closure -/

theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
    positiveSmoothUnifiedSource
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual

theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gravityAuxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
    positiveSmoothUnifiedSource
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual

private theorem
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual_coframe_contDiff :
    ContDiff ℝ ∞
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.coframe := by
  rw [show
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual.coframe =
        Predecessor.coframe by
    exact
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource Predecessor]
  exact fixedP506L0FinalCommonActionActual_coframe_contDiff 0

theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_lorentzEulerThreeForm_zero_at
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
          ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
            ).coframe point) ≠
        0) :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
        point =
      0 := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      positiveSmoothUnifiedSource
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual_coframe_contDiff
      point (by
        rw [← congrFun
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
            positiveSmoothUnifiedSource
            fixedP506L0FinalCommonRepairedConstitutiveSectionActual) point]
        exact nondegenerate)

theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_typedTorsionSpinAt
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
          ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
            ).coframe point) ≠
        0) :
    cartanTorsionThreeForm
        ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
          ).coframe point)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
              ).coframe point)
          ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
            ).gravityConnection point)) =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
        point := by
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
      positiveSmoothUnifiedSource
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual point
      (by
        rw [← congrFun
          (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
            positiveSmoothUnifiedSource
            fixedP506L0FinalCommonRepairedConstitutiveSectionActual) point]
        exact nondegenerate)

/-! ## P286 critical-pair closure -/

private theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe_eq_inner :
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.coframe =
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.coframe :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
    positiveSmoothUnifiedSource
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual

private theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeAuxiliary_eq_inner :
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual.gaugeAuxiliary =
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual.gaugeAuxiliary :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeAuxiliary
    positiveSmoothUnifiedSource
    fixedP506L0FinalCommonRepairedConstitutiveSectionActual

private theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeCurvature
    (point : BasePoint) :
    holonomicGaugeCurvature
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual point =
      holonomicGaugeCurvature
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual point := by
  exact
    holonomicGaugeCurvature_eq_of_connection_eq_current
      fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
        positiveSmoothUnifiedSource
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual)
      point

/-- The P286 auxiliary equation generated by the repaired section survives
the outer Cartan write at the same spacetime point. -/
theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_p286GaugeAuxiliaryEquation
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
          ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
            ).coframe point) ≠
        0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
        point) := by
  have predecessorNondegenerate :
      Matrix.det (Predecessor.coframe point) ≠ 0 := by
    simpa using nondegenerate
  have innerEquation :=
    diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliaryEquation
      positiveSmoothUnifiedSource Predecessor
      (fixedP506L0FinalCommonActionActual_smooth 0)
      point predecessorNondegenerate
  unfold FormNativeP286GaugeAuxiliaryEquationAtBoundary at innerEquation ⊢
  simp only [toContinuumPointField] at innerEquation ⊢
  rw [
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeCurvature,
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_coframe_eq_inner,
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_gaugeAuxiliary_eq_inner]
  exact innerEquation

theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_p286GaugeAuxiliaryResidual_zero
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
          ((fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
            ).coframe point) ≠
        0) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField
          fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
          point) =
      0 := by
  exact
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual
        point)).2
      (fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_p286GaugeAuxiliaryEquation
        point nondegenerate)

/-- The complete P286 connection Euler section is unchanged by the outer
Cartan/reaction write. -/
theorem
    fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual_p286EulerThreeForm :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0FinalCommonRepairedConstitutiveCartanWholeFieldActual =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0FinalCommonRepairedConstitutiveSectionActual := by
  funext point
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm
      positiveSmoothUnifiedSource
      fixedP506L0FinalCommonRepairedConstitutiveSectionActual point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonRepairedConstitutiveCartanWholeFieldWrite

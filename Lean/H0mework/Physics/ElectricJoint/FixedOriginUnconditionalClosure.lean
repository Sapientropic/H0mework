import H0mework.Physics.JointVariation.LiveElectricGlobalDevelopmentOperator
import H0mework.Physics.GlobalDevelopment.FixedOriginUnconditionalClosure
import H0mework.Physics.Holonomic.HolonomicGaugeCurvatureTransport

/-!
# Fixed P506/L0 live-electric unconditional origin closure

The live-electric common global actual closes the three Cartan-owned origin
channels directly on its own final output.  Its P286 auxiliary channel is
transported reader-by-reader from the preceding global actual using only the
preserved coframe and connection fields together with the exact origin
auxiliary seam.

No whole point-field equality, residual coordinate, support branch, target
field, or equation receipt enters either the producer or these readouts.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginUnconditionalClosure

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginUnconditionalClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286ActionCauchySplit

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev LiveCartanInput : StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current positiveSmoothUnifiedSource
    FixedInput

abbrev fixedP506L0CompleteJointLiveElectricOriginClosureActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

private abbrev ExistingActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- Simplicity is generated directly by the final Cartan preparation on the
live-electric actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityMultiplier_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0
      ).gravityMultiplier =
      0 := by
  change formNativeGravityMultiplierEulerResidual
    (toContinuumPointField
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0) = 0
  exact
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        positiveSmoothUnifiedSource LiveCartanInput 0)

/-- The live reaction write closes the `B`-equation on the same final
live-electric actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityAuxiliary_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0
      ).gravityAuxiliary =
      0 := by
  change holonomicFormNativeGravityAuxiliaryEulerResidual
    fixedP506L0CompleteJointLiveElectricOriginClosureActual 0 = 0
  exact congrFun
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
      positiveSmoothUnifiedSource LiveCartanInput) 0

/-- The P286 auxiliary reader sees exactly the old global origin data:
whole-field connection and coframe preservation determine curvature and the
constitutive map, while the live write supplies the exact auxiliary seam. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_p286GaugeAuxiliary_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0
      ).p286GaugeAuxiliary =
      0 := by
  have curvatureEq :
      holonomicGaugeCurvature
          fixedP506L0CompleteJointLiveElectricOriginClosureActual 0 =
        holonomicGaugeCurvature ExistingActual 0 :=
    holonomicGaugeCurvature_eq_of_connection_eq
      fixedP506L0CompleteJointLiveElectricOriginClosureActual ExistingActual
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing
      0
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        fixedP506L0CompleteJointLiveElectricOriginClosureActual 0) = 0
  calc
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField
          fixedP506L0CompleteJointLiveElectricOriginClosureActual 0) =
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField ExistingActual 0) := by
          unfold formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          simp only [toContinuumPointField]
          rw [curvatureEq,
            fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
            fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeAuxiliary_origin_eq_existing]
    _ = 0 :=
      fixedP506L0CompleteJointGlobalDevelopmentActual_p286GaugeAuxiliary_origin_zero

/-- The source-native Cartan connection on the live input gives the complete
Lorentz zero readout at the fixed origin. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_lorentzConnection_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0
      ).lorentzConnection =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
      fixedP506L0CompleteJointLiveElectricOriginClosureActual 0 = 0
  have coframeSmooth :
      ContDiff ℝ ∞ LiveCartanInput.coframe := by
    rw [←
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource LiveCartanInput]
    change ContDiff ℝ ∞
      fixedP506L0CompleteJointLiveElectricOriginClosureActual.coframe
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
    apply contDiff_pi'
    intro internal
    apply contDiff_pi'
    intro coordinate
    exact
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
        internal coordinate
  have nondegenerate :
      Matrix.det (LiveCartanInput.coframe 0) ≠ 0 := by
    rw [←
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe
        positiveSmoothUnifiedSource LiveCartanInput]
    change Matrix.det
      (fixedP506L0CompleteJointLiveElectricOriginClosureActual.coframe 0) ≠ 0
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
    simpa only [canonicalCauchySlicePoint_zero_zero] using
      fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate_zeroSlice
        (0 : StageNineSpatialPoint)
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      positiveSmoothUnifiedSource LiveCartanInput coframeSmooth 0
      nondegenerate

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginUnconditionalClosure

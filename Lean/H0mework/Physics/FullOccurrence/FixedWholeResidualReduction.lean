import H0mework.Physics.FullOccurrence.FixedGravityCoframeVerdict
import H0mework.Physics.FullOccurrence.FixedCoframeZeroSliceRead
import H0mework.Physics.FullOccurrence.FixedLorentzClosure
import H0mework.Physics.FullOccurrence.FixedMatterAdjointTemporalSupport
import H0mework.Physics.FullOccurrence.FixedMatterScalarVerdict
import H0mework.Physics.FullOccurrence.FixedP286Verdict
import H0mework.Physics.FullOccurrence.FixedAdjointZeroSliceClosure
import H0mework.Physics.FullOccurrence.FixedPrimalZeroSliceClosure
import H0mework.Physics.ScalarJets.FixedJointP286AlgebraicMatterScalarDelta

/-!
# U6 whole-residual reduction

This file removes the four channels already settled on the final U6 actual
and exposes the exact remaining support of the same nine-channel carrier.
The remaining reads stay diagnostics: none is fed backwards into a writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWholeResidualReduction

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCoframeVerdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalLorentzClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterAdjointTemporalSupport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalMatterScalarVerdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAdjointZeroSliceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalPrimalZeroSliceClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECAllPointMatterScalarReadTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECMatterScalarDeltas
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeMotherAction
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterCovariantDerivativeAffine
open StageNineConjugateMatterVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source
    FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source
    FixedP506FormNativeJointActionSolvedSuccessor

/-- The complete U6 zero-fiber obligation after discharging every channel
already settled by the same source/current-only producer.  This theorem is a
whole-carrier reduction: it does not turn any remaining read into a writer. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_pointwiseZeroFiber_iff_directRemaining
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (nondegenerate :
      Matrix.det
          (U6.coframe (canonicalCauchySlicePoint time space)) ≠ 0) :
    OnDiracDualFormNativePointwiseJointZeroFiber Source U6
        (canonicalCauchySlicePoint time space) ↔
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
          (canonicalCauchySlicePoint time space)).gravityCurvature = 0 ∧
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint time space) = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Temporal
          (canonicalCauchySlicePoint time space)).scalar = 0 ∧
      ((diracDualFormNativePointwiseJointResidual Source Temporal
            (canonicalCauchySlicePoint time space)).matter +
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
            (canonicalCauchySlicePoint time space)) = 0 ∧
      ((diracDualFormNativePointwiseJointResidual Source Temporal
            (canonicalCauchySlicePoint time space)).conjugateMatter +
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
            (canonicalCauchySlicePoint time space)) = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source U6
          (canonicalCauchySlicePoint time space)).coframe = 0 := by
  let point := canonicalCauchySlicePoint time space
  rw [onDiracDualFormNativePointwiseJointZeroFiber_iff_components]
  constructor
  · rintro ⟨_, gravityAuxiliary, _, _, p286GaugeConnection, scalar,
      matter, conjugateMatter, coframe⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, coframe⟩
    · exact
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityAuxiliary_eq_zero_iff_gravityCurvatureSeam_zero
          point).1 gravityAuxiliary
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point
          ).p286GaugeConnection = 0 at p286GaugeConnection
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_algebraic
          point] at p286GaugeConnection
      exact p286GaugeConnection
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point).scalar = 0
          at scalar
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_temporal
          point] at scalar
      exact scalar
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point).matter = 0
          at matter
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_temporal_add_connectionAction
          point] at matter
      exact matter
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point
          ).conjugateMatter = 0 at conjugateMatter
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_temporal_add_connectionAction
          point] at conjugateMatter
      exact conjugateMatter

  · rintro ⟨gravityCurvature, p286GaugeConnection, scalar, matter,
      conjugateMatter, coframe⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, coframe⟩
    · exact
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityMultiplier_zero
          point
    · exact
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_gravityAuxiliary_eq_zero_iff_gravityCurvatureSeam_zero
          point).2 gravityCurvature
    · exact
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286AuxiliaryResidual_zero
          point nondegenerate
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point
          ).lorentzConnection = 0
      simpa [Source, U6, point,
        diracDualFormNativePointwiseJointResidual] using
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_lorentz_zero_onDomain
          time space inDomain
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point
          ).p286GaugeConnection = 0
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_algebraic
          point]
      exact p286GaugeConnection
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point).scalar = 0
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_scalarResidual_eq_temporal
          point]
      exact scalar
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point).matter = 0
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_temporal_add_connectionAction
          point]
      exact matter
    · change
        (diracDualFormNativePointwiseJointResidual Source U6 point
          ).conjugateMatter = 0
      rw [
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_temporal_add_connectionAction
          point]
      exact conjugateMatter

/-- On the complete zero slice, the generated primal and adjoint action laws
remove both matter coordinates, while the same U6 action jet also closes the
joint gauge-plus-matter coframe read.  The remaining three reads are exactly
the same diagnostics as in the all-time reduction. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_zeroSlice_pointwiseZeroFiber_iff_directRemaining
    (space : StageNineSpatialPoint)
    (inDomain :
      (0 : ℝ) ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (nondegenerate :
      Matrix.det
          (U6.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0) :
    OnDiracDualFormNativePointwiseJointZeroFiber Source U6
        (canonicalCauchySlicePoint 0 space) ↔
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeam
          (canonicalCauchySlicePoint 0 space)).gravityCurvature = 0 ∧
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 space) = 0 ∧
      (diracDualFormNativePointwiseJointResidual Source Temporal
          (canonicalCauchySlicePoint 0 space)).scalar = 0 := by
  rw [
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_pointwiseZeroFiber_iff_directRemaining
      0 space inDomain nondegenerate]
  have matter :
      ((diracDualFormNativePointwiseJointResidual Source Temporal
            (canonicalCauchySlicePoint 0 space)).matter +
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalPrimalConnectionAction
            (canonicalCauchySlicePoint 0 space)) = 0 := by
    rw [←
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_eq_temporal_add_connectionAction
        (canonicalCauchySlicePoint 0 space)]
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_matterResidual_zeroSlice
        space
  have conjugateMatter :
      ((diracDualFormNativePointwiseJointResidual Source Temporal
            (canonicalCauchySlicePoint 0 space)).conjugateMatter +
          fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalTemporalAdjointConnectionAction
            (canonicalCauchySlicePoint 0 space)) = 0 := by
    rw [←
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_eq_temporal_add_connectionAction
        (canonicalCauchySlicePoint 0 space)]
    exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_conjugateMatterResidual_zeroSlice
        space
  have coframe :=
    StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalCoframeZeroSliceRead.fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_coframe_zeroSlice_zero
        space
  constructor
  · rintro ⟨gravityCurvature, p286GaugeConnection, scalar, _, _, _⟩
    exact ⟨gravityCurvature, p286GaugeConnection, scalar⟩
  · rintro ⟨gravityCurvature, p286GaugeConnection, scalar⟩
    exact ⟨gravityCurvature, p286GaugeConnection, scalar, matter,
      conjugateMatter, coframe⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWholeResidualReduction

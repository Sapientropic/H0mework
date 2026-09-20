import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.JointVariation.GlobalDevelopmentFixed
import H0mework.Physics.FinalJoint.FixedTimeAxisCoframe

/-!
# Fixed P506/L0 complete-joint temporal matter regularity

The complete-joint temporal write is defined by the same action-owned matter
profile at every point.  On the canonical time-axis domain of the fixed
P506/L0 source, the input coframe is the already verified final-common
coframe.  Its nondegeneracy and unit temporal principal symbol therefore make
the matter correction smooth on the whole domain, not only at the origin.

The final theorem applies the operator's canonical integral law and records
the resulting coordinate derivative.  No residual value, target field,
branch witness, or zero-fiber receipt is used to construct the write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointTemporalMatterTimeAxisRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- Along each canonical time line, the current consumed by the temporal
write has the verified final-common coframe. -/
theorem fixedP506L0CompleteJointTemporalInput_coframe_eq_finalCommon
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    Input.coframe (canonicalCauchySlicePoint time space) =
      (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0) := by
  simpa [Input] using
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_timeLine_eq_finalCommon
      time space

/-- The fixed action-owned matter correction is smooth at every point of the
canonical time-axis domain. -/
theorem
    fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContDiffAt ℝ ∞
      (completeJointMatterTemporalCoordinateCorrection Source Input)
      (canonicalCauchySlicePoint time space) := by
  apply completeJointMatterTemporalCoordinateCorrection_contDiffAt
    Source Input fixedP506FormNativeJointActionSolvedSuccessor_smooth
  · rw [fixedP506L0CompleteJointTemporalInput_coframe_eq_finalCommon]
    exact
      fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate space inDomain
  · rw [fixedP506L0CompleteJointTemporalInput_coframe_eq_finalCommon,
      fixedP506L0FinalCommonTimeAxis_temporalPrincipalScalar_eq_one
        space time inDomain]
    norm_num

private theorem timeInterval_subset_timeAxisDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Set.uIcc 0 time ⊆ fixedP506L0FinalCommonTimeAxisOriginDomain space := by
  have ordConnected :
      Set.OrdConnected (fixedP506L0FinalCommonTimeAxisOriginDomain space) :=
    isPreconnected_iff_ordConnected.mp
      (fixedP506L0FinalCommonTimeAxisOriginDomain_connected space).isPreconnected
  exact ordConnected.uIcc_subset
    (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space) inDomain

private theorem canonicalTimeLine_continuous
    (space : StageNineSpatialPoint) :
    Continuous (fun time => canonicalCauchySlicePoint time space) := by
  rw [show
    (fun time => canonicalCauchySlicePoint time space) =
      fun time =>
        canonicalCauchySlicePoint 0 space +
          time • coordinateDirection canonicalLorentzianTimeDirection by
    funext time
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
  fun_prop

/-- The fixed correction is continuous on the exact interval consumed by the
canonical time primitive. -/
theorem
    fixedP506L0CompleteJointTemporalMatterCorrection_timeLine_continuousOn_uIcc
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    ContinuousOn
      (fun candidateTime =>
        completeJointMatterTemporalCoordinateCorrection Source Input
          (canonicalCauchySlicePoint candidateTime space))
      (Set.uIcc 0 time) := by
  intro candidateTime inInterval
  have candidateInDomain :=
    timeInterval_subset_timeAxisDomain time space inDomain inInterval
  have profileContinuous :=
    (fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
      candidateTime space candidateInDomain).continuousAt
  have lineContinuous :
      ContinuousAt
        (fun targetTime => canonicalCauchySlicePoint targetTime space)
        candidateTime :=
    (canonicalTimeLine_continuous space).continuousAt
  have composed :
      ContinuousAt
        ((completeJointMatterTemporalCoordinateCorrection Source Input) ∘
          fun targetTime => canonicalCauchySlicePoint targetTime space)
        candidateTime :=
    ContinuousAt.comp
      (f := fun targetTime : ℝ => canonicalCauchySlicePoint targetTime space)
      (g := completeJointMatterTemporalCoordinateCorrection Source Input)
      profileContinuous lineContinuous
  simpa [Function.comp_def] using composed.continuousWithinAt

/-- On the fixed canonical domain, the generated temporal matter field is an
actual integral of the same occurrence-native action velocity in every
matter coordinate. -/
theorem
    fixedP506L0CompleteJointTemporalMatter_timeLine_hasDerivAt_on_timeAxisDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (index : MatterCoordinateIndex)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    NormedHasDerivAt
      (fun candidateTime =>
        matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source Input).matter
            (canonicalCauchySlicePoint candidateTime space)) index)
      (matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles Source Input
          (canonicalCauchySlicePoint time space)).matterVelocity index)
      time := by
  have correctionContinuousOn :=
    fixedP506L0CompleteJointTemporalMatterCorrection_timeLine_continuousOn_uIcc
      time space inDomain
  have correctionContinuousAt :
      ContinuousAt
        (fun candidateTime =>
          completeJointMatterTemporalCoordinateCorrection Source Input
            (canonicalCauchySlicePoint candidateTime space))
        time := by
    have composed :
        ContinuousAt
          ((completeJointMatterTemporalCoordinateCorrection Source Input) ∘
            fun candidateTime => canonicalCauchySlicePoint candidateTime space)
          time :=
      ContinuousAt.comp
        (f := fun candidateTime : ℝ =>
          canonicalCauchySlicePoint candidateTime space)
        (g := completeJointMatterTemporalCoordinateCorrection Source Input)
        (fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
          time space inDomain).continuousAt
        (canonicalTimeLine_continuous space).continuousAt
    simpa [Function.comp_def] using composed
  apply
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_timeLine_hasDerivAt_of_intervalIntegrable
      Source Input space time index
  · exact
      fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.2.1
        |>.differentiable (by simp)
        |>.differentiableAt
  · exact correctionContinuousOn.intervalIntegrable
  · exact
      ContinuousAt.stronglyMeasurableAtFilter
        (fixedP506L0FinalCommonTimeAxisOriginDomain_open space)
        (fun candidateTime candidateInDomain => by
          have composed :
              ContinuousAt
                ((completeJointMatterTemporalCoordinateCorrection Source Input) ∘
                  fun targetTime =>
                    canonicalCauchySlicePoint targetTime space)
                candidateTime :=
            ContinuousAt.comp
              (f := fun targetTime : ℝ =>
                canonicalCauchySlicePoint targetTime space)
              (g := completeJointMatterTemporalCoordinateCorrection Source Input)
              (fixedP506L0CompleteJointTemporalMatterCorrection_contDiffAt_on_timeAxisDomain
                candidateTime space candidateInDomain).continuousAt
              (canonicalTimeLine_continuous space).continuousAt
          simpa [Function.comp_def] using composed)
        time inDomain
  · exact correctionContinuousAt

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointTemporalMatterTimeAxisRegularity

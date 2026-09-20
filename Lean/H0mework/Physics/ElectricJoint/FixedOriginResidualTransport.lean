import H0mework.Physics.ElectricJoint.FixedFieldTransport
import H0mework.Physics.FinalJoint.FixedZeroFiber

/-!
# Fixed P506/L0 live-electric origin residual transport

The live-electric global writer preserves the complete scalar, coframe,
gauge-connection, matter, and adjoint fields of the preceding global
development.  This module transports the accepted scalar and coframe
zero-fiber consumers across those literal field equalities.

The remaining hypotheses compare the preceding global development with the
accepted actual: scalar momentum divergence for the second-jet channel, and
the common gauge--matter coframe load together with the gravity-curvature
seam.  Every live-electric-to-preceding-development equality is discharged
internally.  None of these reads is fed into the live-electric producer and
no residual coordinate is used to construct a field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginResidualTransport

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeScalarVariation
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- Stable API alias for the fixed source/current live-electric actual. -/
abbrev LiveActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

/-- Stable API alias for its preceding complete-joint global development. -/
abbrev ExistingActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev AlgebraicActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricAlgebraicCurrent

private abbrev CanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

/-- Stable API alias for the accepted fixed-origin common actual. -/
abbrev AcceptedActual : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

private abbrev LiveCartanInput : StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current positiveSmoothUnifiedSource
    FixedInput

private abbrev AcceptedCartanInput : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonPreECActionActual 0

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem liveActual_coframe_origin_eq_accepted :
    LiveActual.coframe 0 = AcceptedActual.coframe 0 := by
  calc
    LiveActual.coframe 0 = ExistingActual.coframe 0 :=
      congrFun
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
        0
    _ = AcceptedActual.coframe 0 := by
      simpa only [canonicalCauchySlicePoint_zero_zero] using
        fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_timeLine_eq_finalCommon
          0 (0 : StageNineSpatialPoint)

private theorem liveActual_scalar_origin_eq_accepted :
    LiveActual.scalar 0 = AcceptedActual.scalar 0 := by
  calc
    LiveActual.scalar 0 = AlgebraicActual.scalar 0 := by
      exact congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
          positiveSmoothUnifiedSource FixedInput) 0
    _ = CanonicalActual.scalar 0 :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_origin_eq_canonical
    _ = AcceptedActual.scalar 0 := rfl

private theorem liveActual_matter_origin_eq_accepted :
    LiveActual.matter 0 = AcceptedActual.matter 0 := by
  calc
    LiveActual.matter 0 = AlgebraicActual.matter 0 := by
      exact congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
          positiveSmoothUnifiedSource FixedInput) 0
    _ = CanonicalActual.matter 0 :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matter_origin_eq_canonical
    _ = AcceptedActual.matter 0 := rfl

private theorem liveActual_conjugateMatter_origin_eq_accepted :
    LiveActual.conjugateMatter 0 = AcceptedActual.conjugateMatter 0 := by
  calc
    LiveActual.conjugateMatter 0 = AlgebraicActual.conjugateMatter 0 := by
      exact congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
          positiveSmoothUnifiedSource FixedInput) 0
    _ = CanonicalActual.conjugateMatter 0 :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatter_origin_eq_canonical
    _ = AcceptedActual.conjugateMatter 0 := rfl

private theorem
    canonicalActual_scalarCovariantDerivative_origin_eq_accepted :
    holonomicScalarCovariantDerivative CanonicalActual 0 =
      holonomicScalarCovariantDerivative AcceptedActual 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  change
    fieldDirectionalDerivative AcceptedActual.scalar 0 direction +
        scalarMotherLieAction
          (p286LieBlockEmbed
            ((fixedP506L0P286CanonicalConnectionCandidate
              fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection
                0 direction))
          (AcceptedActual.scalar 0) =
      _
  unfold fixedP506L0P286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    p286HolonomicSecondJetQuadraticRealization_origin]
  simp only [Pi.zero_apply, map_zero, smul_zero, add_zero]

private theorem liveActual_scalarCovariantDerivative_origin_eq_accepted :
    holonomicScalarCovariantDerivative LiveActual 0 =
      holonomicScalarCovariantDerivative AcceptedActual 0 := by
  have scalarEq : LiveActual.scalar = AlgebraicActual.scalar :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
      positiveSmoothUnifiedSource FixedInput
  have gaugeConnectionEq :
      LiveActual.gaugeConnection = AlgebraicActual.gaugeConnection :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
      positiveSmoothUnifiedSource FixedInput
  calc
    holonomicScalarCovariantDerivative LiveActual 0 =
        holonomicScalarCovariantDerivative AlgebraicActual 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [scalarEq, gaugeConnectionEq]
    _ = holonomicScalarCovariantDerivative CanonicalActual 0 :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalarCovariantDerivative_origin_eq_canonical
    _ = holonomicScalarCovariantDerivative AcceptedActual 0 :=
      canonicalActual_scalarCovariantDerivative_origin_eq_accepted

private theorem liveActual_gaugeConnection_origin_eq_accepted :
    LiveActual.gaugeConnection 0 = AcceptedActual.gaugeConnection 0 := by
  calc
    LiveActual.gaugeConnection 0 = AlgebraicActual.gaugeConnection 0 := by
      exact congrFun
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
          positiveSmoothUnifiedSource FixedInput) 0
    _ = CanonicalActual.gaugeConnection 0 :=
      congrFun
        fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical
        0
    _ = AcceptedActual.gaugeConnection 0 := by
      funext direction
      change
        (fixedP506L0P286CanonicalConnectionCandidate
            fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection
              0 direction =
          AcceptedActual.gaugeConnection 0 direction
      unfold fixedP506L0P286CanonicalConnectionCandidate
        installP286HolonomicConnectionSecondJet
      rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
        p286HolonomicSecondJetQuadraticRealization_origin]
      simp only [Pi.zero_apply, map_zero, smul_zero, add_zero]

private theorem liveActual_scalarAlgebraic_origin_eq_accepted
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        LiveActual direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        AcceptedActual direction 0 := by
  have variationEquality :
      holonomicScalarVariationAlgebraicDirection LiveActual direction 0 =
        holonomicScalarVariationAlgebraicDirection AcceptedActual direction
          0 := by
    funext formDirection
    unfold holonomicScalarVariationAlgebraicDirection
    rw [liveActual_gaugeConnection_origin_eq_accepted]
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [liveActual_coframe_origin_eq_accepted,
    liveActual_scalar_origin_eq_accepted,
    liveActual_scalarCovariantDerivative_origin_eq_accepted,
    liveActual_matter_origin_eq_accepted,
    liveActual_conjugateMatter_origin_eq_accepted, variationEquality]

private theorem liveActual_scalarDifferentialMomentum_eq_existing
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource LiveActual
        direction derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource ExistingActual
        direction derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalarCovariantDerivative_eq_existing]

private theorem liveActual_scalarDifferentialMomentumDivergence_eq_existing
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        LiveActual direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ExistingActual direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [liveActual_scalarDifferentialMomentum_eq_existing]

/-- The live-electric scalar residual has exactly one remaining second-jet
consumer: equality of the preceding and accepted scalar momentum divergence
at the common occurrence.  All live-electric transport, algebraic data, and
first-jet data are discharged internally. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_origin_zero_of_momentumDivergence
    (momentumDivergence :
      ∀ direction : ScalarCoordinateCarrier,
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
            ExistingActual direction 0 =
          scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
            AcceptedActual direction 0) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      LiveActual 0).scalar =
      0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
      positiveSmoothUnifiedSource LiveActual direction 0 = 0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [liveActual_scalarAlgebraic_origin_eq_accepted,
    show
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          LiveActual direction 0 =
        scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
          ExistingActual direction 0 by
      exact congrFun
        (liveActual_scalarDifferentialMomentumDivergence_eq_existing direction)
        0,
    momentumDivergence direction]
  exact
    fixedP506L0FinalCommonActionActual_scalarEuler_origin_zero 0 direction

private theorem liveActual_gravityAuxiliary_origin_eq_accepted :
    LiveActual.gravityAuxiliary 0 =
      AcceptedActual.gravityAuxiliary 0 := by
  calc
    LiveActual.gravityAuxiliary 0 =
        physicalIIPlusBivector (LiveActual.coframe 0) := by
      exact
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary
          positiveSmoothUnifiedSource LiveCartanInput 0
    _ = physicalIIPlusBivector (AcceptedActual.coframe 0) := by
      rw [liveActual_coframe_origin_eq_accepted]
    _ = AcceptedActual.gravityAuxiliary 0 :=
      (fixedP506L0FinalCommonActionActual_simplicity
        (0 : StageNineSpatialPoint) 0).symm

/-- The two source-generated reactions differ exactly by the live
contravariant gravity-curvature seam.  The changed P286 temporal field is not
read by this reaction producer. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityReaction_sub_accepted :
    LiveActual.gravitySimplicityMultiplier 0 -
        AcceptedActual.gravitySimplicityMultiplier 0 =
      -(holonomicContravariantGravityCurvature LiveActual 0 -
          holonomicContravariantGravityCurvature AcceptedActual 0) := by
  rw [show
      LiveActual.gravitySimplicityMultiplier 0 =
        formNativeGravityReactionField LiveActual 0 by
      exact congrFun
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
          positiveSmoothUnifiedSource LiveCartanInput) 0]
  rw [show
      AcceptedActual.gravitySimplicityMultiplier 0 =
        formNativeGravityReactionField AcceptedActual 0 by
      exact congrFun
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reactionSelfGenerated
          positiveSmoothUnifiedSource AcceptedCartanInput) 0]
  unfold formNativeGravityReactionField
  rw [liveActual_gravityAuxiliary_origin_eq_accepted]
  module

/-- The live-electric coframe residual transports from the accepted zero
fiber once the preceding global development's common gauge--matter load and
gravity curvature are identified with the accepted actual.  The complete
live-electric point field at the origin is transported to the preceding
development internally. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_origin_zero_of_commonLoad_and_curvature
    (commonLoad :
      diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
            (toContinuumPointField ExistingActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField ExistingActual 0) =
        diracDualFormNativeCoframeGaugeEulerCovector
              positiveSmoothUnifiedSource
              (toContinuumPointField AcceptedActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField AcceptedActual 0))
    (curvature :
      holonomicContravariantGravityCurvature ExistingActual 0 =
        holonomicContravariantGravityCurvature AcceptedActual 0) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      LiveActual 0).coframe =
      0 := by
  have liveCommonLoad :
      diracDualFormNativeCoframeGaugeEulerCovector positiveSmoothUnifiedSource
            (toContinuumPointField LiveActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField LiveActual 0) =
        diracDualFormNativeCoframeGaugeEulerCovector
              positiveSmoothUnifiedSource
              (toContinuumPointField AcceptedActual 0) +
          diracDualFormNativeCoframeMatterEulerCovector
            positiveSmoothUnifiedSource 0
            (toContinuumPointField AcceptedActual 0) := by
    rw [
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_pointField_origin_eq_existing]
    exact commonLoad
  have liveCurvature :
      holonomicContravariantGravityCurvature LiveActual 0 =
        holonomicContravariantGravityCurvature AcceptedActual 0 := by
    calc
      holonomicContravariantGravityCurvature LiveActual 0 =
          holonomicContravariantGravityCurvature ExistingActual 0 :=
        congrFun
          fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_contravariantGravityCurvature_eq_existing
          0
      _ = holonomicContravariantGravityCurvature AcceptedActual 0 :=
        curvature
  have multiplier :
      LiveActual.gravitySimplicityMultiplier 0 =
        AcceptedActual.gravitySimplicityMultiplier 0 := by
    have seam :=
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityReaction_sub_accepted
    rw [liveCurvature, sub_self, neg_zero] at seam
    exact sub_eq_zero.mp seam
  have reaction :
      (fun variation =>
        formNativeCoframeConstraintReaction
          (toContinuumPointField LiveActual 0) variation) =
      fun variation =>
        formNativeCoframeConstraintReaction
          (toContinuumPointField AcceptedActual 0) variation := by
    funext variation
    unfold formNativeCoframeConstraintReaction
    simp only [toContinuumPointField]
    rw [liveActual_coframe_origin_eq_accepted, multiplier]
  have liveNondegenerate :
      Matrix.det (LiveActual.coframe 0) ≠ 0 := by
    rw [liveActual_coframe_origin_eq_accepted,
      fixedP506L0FinalCommonActionActual_coframe_origin]
    norm_num
  have acceptedNondegenerate :
      Matrix.det (AcceptedActual.coframe 0) ≠ 0 := by
    rw [fixedP506L0FinalCommonActionActual_coframe_origin]
    norm_num
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField LiveActual 0) =
      0
  rw [←
    fixedP506L0FinalCommonActionActual_fullCoframeEuler_zero
      (0 : StageNineSpatialPoint)]
  apply ContinuousLinearMap.ext
  intro variation
  rw [
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      positiveSmoothUnifiedSource 0
      (toContinuumPointField LiveActual 0) liveNondegenerate variation,
    diracDualFormNativeCoframeEulerCovector_apply_eq_gauge_add_matter_sub_reaction
      positiveSmoothUnifiedSource 0
      (toContinuumPointField AcceptedActual 0) acceptedNondegenerate variation]
  have commonLoadAt := DFunLike.congr_fun liveCommonLoad variation
  simp only [add_apply] at commonLoadAt
  rw [commonLoadAt, congrFun reaction variation]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginResidualTransport

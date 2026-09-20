import H0mework.Physics.JointVariation.GlobalDevelopmentFixedP286Compatibility
import H0mework.Physics.FinalJoint.FixedZeroFiber
import H0mework.Physics.ActualGerms.FixedFullOccurrenceAdjointTemporalRegularity
import H0mework.Physics.ActualGerms.FixedFullOccurrenceMatterTemporalRegularity
import H0mework.Physics.DualVariation.PointwiseActionJetCarrier

/-!
# Fixed P506/L0 global primal/adjoint origin closure

This module promotes the already-verified first-jet chain for the
source/current-only global development to production.  The temporal matter
primitive satisfies the action-generated primal law at the fixed occurrence;
the corresponding matter vector and conjugate-matter Euler reader therefore
vanish on that same global actual.

Every derivative is computed from the generated polynomial/affine fields.
No residual coordinate, target field, branch receipt, or supplied equation
enters a constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeLocalDifferentiability
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonZeroFiber
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceMatterTemporalRegularity
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionAdjointFirstJet
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterFirstJet
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeCoframeLocalVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

abbrev NewActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

abbrev AcceptedActual : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonActionActual 0

abbrev AlgebraicActual : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

abbrev CanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

abbrev InputActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

abbrev ProfileRestartActual : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent
    positiveSmoothUnifiedSource InputActual 0

abbrev ProfilePrimalActual : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    ProfileRestartActual

abbrev ProfileAdjointActual : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    ProfilePrimalActual

theorem profileRestartActual_eq_fixedCartan :
    ProfileRestartActual = fixedP506L0CartanRestartActual 0 := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
    fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
  rw [fullyRecenterHolonomicConfiguration_zero,
    spatiallyRecenterHolonomicConfiguration_zero]

abbrev NewCartanInput : StageNineHolonomicConfiguration :=
  completeJointGlobalP286Current positiveSmoothUnifiedSource
    FixedP506FormNativeJointActionSolvedSuccessor

abbrev AcceptedCartanInput : StageNineHolonomicConfiguration :=
  fixedP506L0FinalCommonPreECActionActual 0

theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem newActual_coframe_eq_algebraic :
    NewActual.coframe = AlgebraicActual.coframe :=
  rfl

theorem newActual_scalar_eq_algebraic :
    NewActual.scalar = AlgebraicActual.scalar :=
  rfl

theorem newActual_matter_eq_algebraic :
    NewActual.matter = AlgebraicActual.matter :=
  rfl

theorem newActual_conjugateMatter_eq_algebraic :
    NewActual.conjugateMatter = AlgebraicActual.conjugateMatter :=
  rfl

theorem newActual_scalarCovariantDerivative_eq_algebraic :
    holonomicScalarCovariantDerivative NewActual 0 =
      holonomicScalarCovariantDerivative AlgebraicActual 0 :=
  rfl

theorem canonicalActual_coframe_eq_accepted :
    CanonicalActual.coframe = AcceptedActual.coframe :=
  rfl

theorem canonicalActual_scalar_eq_accepted :
    CanonicalActual.scalar = AcceptedActual.scalar :=
  rfl

theorem canonicalActual_matter_eq_accepted :
    CanonicalActual.matter = AcceptedActual.matter :=
  rfl

theorem canonicalActual_conjugateMatter_eq_accepted :
    CanonicalActual.conjugateMatter = AcceptedActual.conjugateMatter :=
  rfl

theorem canonicalActual_scalarCovariantDerivative_eq_accepted :
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
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate]
  rw [p286HolonomicSecondJetQuadraticRealization_origin]
  simp only [Pi.zero_apply, map_zero, smul_zero, add_zero]

theorem newActual_coframe_origin_eq_accepted :
    NewActual.coframe 0 = AcceptedActual.coframe 0 :=
  (congrFun newActual_coframe_eq_algebraic 0).trans
    ((congrFun
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical
      0).trans (congrFun canonicalActual_coframe_eq_accepted 0))

theorem newActual_coframe_eq_accepted :
    NewActual.coframe = AcceptedActual.coframe :=
  newActual_coframe_eq_algebraic.trans
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical.trans
      canonicalActual_coframe_eq_accepted)

theorem newActual_scalar_origin_eq_accepted :
    NewActual.scalar 0 = AcceptedActual.scalar 0 :=
  (congrFun newActual_scalar_eq_algebraic 0).trans
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_scalar_origin_eq_canonical.trans
      (congrFun canonicalActual_scalar_eq_accepted 0))

theorem newActual_matter_origin_eq_accepted :
    NewActual.matter 0 = AcceptedActual.matter 0 :=
  (congrFun newActual_matter_eq_algebraic 0).trans
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_matter_origin_eq_canonical.trans
      (congrFun canonicalActual_matter_eq_accepted 0))

theorem newActual_conjugateMatter_origin_eq_accepted :
    NewActual.conjugateMatter 0 = AcceptedActual.conjugateMatter 0 :=
  (congrFun newActual_conjugateMatter_eq_algebraic 0).trans
    (fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_conjugateMatter_origin_eq_canonical.trans
      (congrFun canonicalActual_conjugateMatter_eq_accepted 0))

theorem newActual_matterCoordinates_hasFDerivAt_origin :
    HasFDerivAt
      (fun point => matterCoordinateEquiv (NewActual.matter point))
      ((fderiv ℝ
          (fun point => matterCoordinateEquiv (InputActual.matter point)) 0) +
        canonicalTimeProjection.smulRight
          (completeJointMatterTemporalCoordinateCorrection
            positiveSmoothUnifiedSource InputActual 0))
      0 := by
  have inputDerivative :
      HasFDerivAt
        (fun point => matterCoordinateEquiv (InputActual.matter point))
        (fderiv ℝ
          (fun point => matterCoordinateEquiv (InputActual.matter point)) 0)
        0 :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth
      |>.2.2.2.2.2.2.2.1.differentiable (by simp)
      |>.differentiableAt).hasFDerivAt
  have primitiveDerivative :=
    fixedP506L0FullOccurrenceMatterTemporalPrimitive_hasFDerivAt_origin
  have totalDerivative := inputDerivative.add primitiveDerivative
  have functionEquality :
      (fun point => matterCoordinateEquiv (NewActual.matter point)) =
        (fun point => matterCoordinateEquiv (InputActual.matter point)) +
          canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection
              positiveSmoothUnifiedSource InputActual) := by
    funext point
    rw [congrFun newActual_matter_eq_algebraic point]
    change
      matterCoordinateEquiv
          ((completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
            InputActual).matter point) =
        _
    simp [completeJointGlobalTemporalCurrent,
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator]
  rw [functionEquality]
  exact totalDerivative

theorem newActual_matterCoordinateDerivative_origin
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 direction =
      fieldDirectionalDerivative
          (fun point => matterCoordinateEquiv (InputActual.matter point))
          0 direction +
        canonicalTimeProjection (coordinateDirection direction) •
          completeJointMatterTemporalCoordinateCorrection
            positiveSmoothUnifiedSource InputActual 0 := by
  unfold fieldDirectionalDerivative
  rw [newActual_matterCoordinates_hasFDerivAt_origin.fderiv]
  rfl

theorem canonicalTimeProjection_coordinateDirection
    (direction : LorentzianIndex) :
    canonicalTimeProjection (coordinateDirection direction) =
      if direction = canonicalLorentzianTimeDirection then 1 else 0 := by
  fin_cases direction <;>
    simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
      coordinateDirection, localBaseCoordinate_apply]

theorem newActual_matterCoordinateTimeDerivative_origin :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          positiveSmoothUnifiedSource InputActual 0).matterVelocity := by
  rw [newActual_matterCoordinateDerivative_origin,
    canonicalTimeProjection_coordinateDirection]
  simp only [if_pos, one_smul]
  unfold completeJointMatterTemporalCoordinateCorrection
  module

theorem
    newActual_conjugateMatterCoordinates_eq_input_add_primitive :
    holonomicConjugateMatterCoordinates NewActual =
      holonomicConjugateMatterCoordinates InputActual +
        canonicalTimePrimitive
          (completeJointAdjointTemporalCoordinateCorrection
            positiveSmoothUnifiedSource InputActual) := by
  funext point
  unfold holonomicConjugateMatterCoordinates
  rw [congrFun newActual_conjugateMatter_eq_algebraic point]
  change
    matterDualCoordinates
        ((completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          InputActual).conjugateMatter point) =
      _
  simp [completeJointGlobalTemporalCurrent,
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator,
    matterDualCoordinates_add]

theorem
    newActual_conjugateMatterCoordinates_differentiableAt_origin :
    DifferentiableAt ℝ (holonomicConjugateMatterCoordinates NewActual) 0 := by
  rw [newActual_conjugateMatterCoordinates_eq_input_add_primitive]
  exact
    (holonomicConjugateMatterCoordinates_contDiff
      InputActual fixedP506FormNativeJointActionSolvedSuccessor_smooth
      |>.differentiable (by simp) |>.differentiableAt).add
      fixedP506L0FullOccurrenceAdjointTemporalPrimitive_hasFDerivAt_origin.differentiableAt

def newAdjointDerivativeNormalForm
    (direction : LorentzianIndex) : MatterCoordinateCarrier :=
  holonomicConjugateMatterDerivativeCoordinates InputActual 0 direction +
    canonicalTimeProjection (coordinateDirection direction) •
      completeJointAdjointTemporalCoordinateCorrection
        positiveSmoothUnifiedSource InputActual 0

def newAdjointDerivative
    (direction : LorentzianIndex) : MatterCoordinateCarrier :=
  holonomicConjugateMatterDerivativeCoordinates NewActual 0 direction

theorem newActual_conjugateMatterDerivativeCoordinates_origin
    (direction : LorentzianIndex) :
    newAdjointDerivative direction =
      newAdjointDerivativeNormalForm direction := by
  have inputDerivative :
      HasFDerivAt
        (holonomicConjugateMatterCoordinates InputActual)
        (fderiv ℝ (holonomicConjugateMatterCoordinates InputActual) 0)
        0 :=
    (holonomicConjugateMatterCoordinates_contDiff
      InputActual fixedP506FormNativeJointActionSolvedSuccessor_smooth
      |>.differentiable (by simp) |>.differentiableAt).hasFDerivAt
  have primitiveDerivative :=
    fixedP506L0FullOccurrenceAdjointTemporalPrimitive_hasFDerivAt_origin
  have totalDerivative := inputDerivative.add primitiveDerivative
  unfold newAdjointDerivative newAdjointDerivativeNormalForm
    holonomicConjugateMatterDerivativeCoordinates fieldDirectionalDerivative
  rw [newActual_conjugateMatterCoordinates_eq_input_add_primitive,
    totalDerivative.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]

def newAdjointActionVelocity :
    Module.Dual ℂ DiracExteriorMatterCarrier :=
  (sourceActionGeneratedDiracDualCompleteJointProfiles
    positiveSmoothUnifiedSource InputActual 0).adjointVelocity

def newAdjointActionVelocityCoordinates : MatterCoordinateCarrier :=
  matterDualCoordinates newAdjointActionVelocity

theorem newAdjointDerivative_time_origin :
    newAdjointDerivative canonicalLorentzianTimeDirection =
      newAdjointActionVelocityCoordinates := by
  rw [newActual_conjugateMatterDerivativeCoordinates_origin]
  unfold newAdjointDerivativeNormalForm newAdjointActionVelocityCoordinates
    newAdjointActionVelocity
  rw [canonicalTimeProjection_coordinateDirection]
  simp only [if_pos, one_smul]
  unfold completeJointAdjointTemporalCoordinateCorrection
  change
    holonomicConjugateMatterDerivativeCoordinates InputActual 0
          canonicalLorentzianTimeDirection +
        (matterDualCoordinates
            (sourceActionGeneratedDiracDualCompleteJointProfiles
              positiveSmoothUnifiedSource InputActual 0).adjointVelocity -
          holonomicConjugateMatterDerivativeCoordinates InputActual 0
            canonicalLorentzianTimeDirection) =
      matterDualCoordinates
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          positiveSmoothUnifiedSource InputActual 0).adjointVelocity
  module

theorem newActual_conjugateMatterTimeDerivative_origin :
    holonomicConjugateMatterDerivativeDual NewActual 0
        canonicalLorentzianTimeDirection =
      newAdjointActionVelocity := by
  unfold holonomicConjugateMatterDerivativeDual
  change matterDualOfCoordinates
      (newAdjointDerivative canonicalLorentzianTimeDirection) = _
  rw [newAdjointDerivative_time_origin]
  unfold newAdjointActionVelocityCoordinates
  exact matterDualOfCoordinates_surjective _

theorem newActual_coframe_eq_profileRestart :
    NewActual.coframe = ProfileRestartActual.coframe := by
  unfold NewActual fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
    completeJointGlobalP286Current
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  rw [fullyRecenterHolonomicConfiguration_zero]
  rfl

theorem newActual_scalar_origin_eq_input :
    NewActual.scalar 0 = InputActual.scalar 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      InputActual).scalar 0 =
      InputActual.scalar 0
  rw [completeJointGlobalTemporalCurrent]
  simpa only [canonicalCauchySlicePoint_zero_zero] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
      positiveSmoothUnifiedSource InputActual 0

theorem profileRestartActual_scalar_origin_eq_input :
    ProfileRestartActual.scalar 0 = InputActual.scalar 0 := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_scalar_origin]

theorem newActual_matter_origin_eq_input :
    NewActual.matter 0 = InputActual.matter 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      InputActual).matter 0 =
      InputActual.matter 0
  rw [completeJointGlobalTemporalCurrent]
  simpa only [canonicalCauchySlicePoint_zero_zero] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      positiveSmoothUnifiedSource InputActual 0

theorem profileRestartActual_matter_origin_eq_input :
    ProfileRestartActual.matter 0 = InputActual.matter 0 := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_matter_origin]

theorem newActual_conjugateMatter_origin_eq_input :
    NewActual.conjugateMatter 0 = InputActual.conjugateMatter 0 := by
  change
    (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
      InputActual).conjugateMatter 0 =
      InputActual.conjugateMatter 0
  rw [completeJointGlobalTemporalCurrent]
  simpa only [canonicalCauchySlicePoint_zero_zero] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      positiveSmoothUnifiedSource InputActual 0

theorem profileRestartActual_conjugateMatter_origin_eq_input :
    ProfileRestartActual.conjugateMatter 0 = InputActual.conjugateMatter 0 := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_conjugateMatter_origin]

theorem profileRestartActual_coframe_eq_input :
    ProfileRestartActual.coframe = InputActual.coframe := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_zero]

theorem profileRestartActual_matter_eq_input :
    ProfileRestartActual.matter = InputActual.matter := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_zero]

theorem profileRestartActual_conjugateMatter_eq_input :
    ProfileRestartActual.conjugateMatter = InputActual.conjugateMatter := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_zero]

theorem profileRestartActual_gaugeConnection_eq_input :
    ProfileRestartActual.gaugeConnection = InputActual.gaugeConnection := by
  unfold ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_zero]

theorem newActual_gaugeConnection_origin_eq_profileRestart :
    NewActual.gaugeConnection 0 =
      ProfileRestartActual.gaugeConnection 0 := by
  rw [profileRestartActual_gaugeConnection_eq_input]
  change
    (diracDualFormNativeP286CanonicalConnectionCandidate
      (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
        InputActual)
      (diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource
        (completeJointGlobalTemporalCurrent positiveSmoothUnifiedSource
          InputActual))).gaugeConnection 0 =
      InputActual.gaugeConnection 0
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  funext direction
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    p286HolonomicSecondJetQuadraticRealization_origin]
  simp
  rfl

theorem newActual_gravityConnection_origin_eq_profileRestart :
    NewActual.gravityConnection 0 =
      ProfileRestartActual.gravityConnection 0 := by
  have coframeFieldEq :
      NewCartanInput.coframe = InputActual.coframe := by
    change NewActual.coframe = InputActual.coframe
    rw [newActual_coframe_eq_profileRestart,
      profileRestartActual_coframe_eq_input]
  have coframeEq :
      NewCartanInput.coframe 0 = InputActual.coframe 0 := by
    exact congrFun coframeFieldEq 0
  have matterEq :
      NewCartanInput.matter 0 = InputActual.matter 0 := by
    change NewActual.matter 0 = InputActual.matter 0
    exact newActual_matter_origin_eq_input
  have conjugateMatterEq :
      NewCartanInput.conjugateMatter 0 =
        InputActual.conjugateMatter 0 := by
    change NewActual.conjugateMatter 0 = InputActual.conjugateMatter 0
    exact newActual_conjugateMatter_origin_eq_input
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource NewCartanInput InputActual 0 coframeEq
      matterEq conjugateMatterEq
  unfold NewActual fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
    ProfileRestartActual completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  change
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        NewCartanInput 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        InputActual 0
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeFieldEq, spinEq]

theorem newActual_matterCoordinateSpatialDerivative_origin
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          (ProfileRestartActual.matter point))
        0 direction.succ := by
  rw [newActual_matterCoordinateDerivative_origin,
    canonicalTimeProjection_coordinateDirection,
    profileRestartActual_matter_eq_input]
  have spatialNe :
      direction.succ ≠ canonicalLorentzianTimeDirection := by
    fin_cases direction <;> decide
  simp [spatialNe]

theorem newActual_matterCovariantDerivative_time_origin :
    holonomicMatterCovariantDerivative NewActual 0
        canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        ProfileRestartActual 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [newActual_matterCoordinateTimeDerivative_origin,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    matterCoordinateEquiv.symm_apply_apply]
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    holonomicMatterConnectionAction
  rw [newActual_gravityConnection_origin_eq_profileRestart,
    newActual_gaugeConnection_origin_eq_profileRestart,
    newActual_matter_origin_eq_input,
    profileRestartActual_matter_origin_eq_input]
  module

theorem newActual_matterCovariantDerivative_spatial_origin
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative NewActual 0 direction.succ =
      holonomicMatterCovariantDerivative ProfileRestartActual 0
        direction.succ := by
  unfold holonomicMatterCovariantDerivative
  rw [newActual_matterCoordinateSpatialDerivative_origin,
    newActual_gravityConnection_origin_eq_profileRestart,
    newActual_gaugeConnection_origin_eq_profileRestart,
    newActual_matter_origin_eq_input,
    profileRestartActual_matter_origin_eq_input]

theorem newActual_matterKnownVector_origin_eq_profileRestart :
    holonomicDiracDualCurrentCoframeMatterKnownVector NewActual 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        ProfileRestartActual 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [congrFun newActual_coframe_eq_profileRestart 0,
    newActual_scalar_origin_eq_input,
    profileRestartActual_scalar_origin_eq_input,
    newActual_matter_origin_eq_input,
    profileRestartActual_matter_origin_eq_input]
  simp_rw [newActual_matterCovariantDerivative_spatial_origin]

theorem fixedP506L0CompleteJointGlobalDevelopmentActual_primalActionLaw_origin :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw NewActual 0
      (holonomicMatterCovariantDerivative NewActual 0
        canonicalLorentzianTimeDirection) := by
  have profileCoframeOne : ProfileRestartActual.coframe 0 = 1 := by
    rw [← congrFun newActual_coframe_eq_profileRestart 0,
      newActual_coframe_origin_eq_accepted]
    exact fixedP506L0FinalCommonActionActual_coframe_origin 0
  have noncharacteristic :
      coframeTemporalPrincipalScalar (ProfileRestartActual.coframe 0) ≠ 0 := by
    rw [profileCoframeOne, coframeTemporalPrincipalScalar_one]
    exact one_ne_zero
  have generated :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      ProfileRestartActual 0 noncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [congrFun newActual_coframe_eq_profileRestart 0,
    newActual_matterKnownVector_origin_eq_profileRestart,
    newActual_matterCovariantDerivative_time_origin]
  exact generated

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_matterVector_origin_zero :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField NewActual 0) =
      0 :=
  generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    positiveSmoothUnifiedSource NewActual 0
    fixedP506L0CompleteJointGlobalDevelopmentActual_primalActionLaw_origin

theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_conjugateMatter_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      NewActual 0).conjugateMatter =
      0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        NewActual direction 0 =
      0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [
    fixedP506L0CompleteJointGlobalDevelopmentActual_matterVector_origin_zero]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure

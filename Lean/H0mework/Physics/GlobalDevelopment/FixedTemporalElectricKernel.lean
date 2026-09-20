import H0mework.Physics.ActualGerms.FixedCartanRestartTemporalElectricKernel
import H0mework.Physics.GlobalDevelopment.FixedOriginAdjointDerivativeTransport

/-!
# Fixed complete-joint global temporal-electric Cartan kernel

The complete-joint global development recomputes its live primal, adjoint,
coframe, and W13 response before the final Cartan restart.  This module proves
directly from those source/action-generated profiles that the two temporal
connection first germs entering the authoritative `E03` curvature coordinate
vanish.  No curvature target, residual coordinate, or correction receipt is
an input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506ECFullCauchyLiveStressSpatialRegularity
open StageNineDiracDualFormNativeFixedP506FullOccurrenceAdjointTemporalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionSixSectorClosure
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointConnectionOriginRegularity
open StageNineEnrichedProofFreeSource
open StageNineCoframeFirstJet
open StageNineCoframeVariation
open StageNineConjugateMatterVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineMatterActionTimeVelocity
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem profileRestart_coframe_eq_fixed :
    ProfileRestartActual.coframe = FixedP506JointActual.coframe := by
  rw [profileRestartActual_coframe_eq_input,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]

private theorem profileRestart_matter_eq_fixed :
    ProfileRestartActual.matter = FixedP506JointActual.matter := by
  rw [profileRestartActual_matter_eq_input,
    fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem profileRestart_conjugateMatter_eq_fixed :
    ProfileRestartActual.conjugateMatter =
      FixedP506JointActual.conjugateMatter := by
  rw [profileRestartActual_conjugateMatter_eq_input,
    fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]

private theorem profileRestart_scalar_origin_eq_fixed :
    ProfileRestartActual.scalar 0 = FixedP506JointActual.scalar 0 := by
  rw [profileRestartActual_scalar_origin_eq_input,
    fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar]

private theorem profileRestart_gaugeConnection_origin_eq_fixed :
    ProfileRestartActual.gaugeConnection 0 =
      FixedP506JointActual.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  have restartZero :
      holonomicP286GaugeConnectionCoordinate ProfileRestartActual 0 = 0 := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [profileRestartActual_gaugeConnection_eq_input]
    exact
      fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_origin_zero
  have fixedZero :
      holonomicP286GaugeConnectionCoordinate FixedP506JointActual 0 = 0 :=
    fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
  simpa [holonomicP286GaugeConnectionCoordinate] using
    (congrFun restartZero direction).trans (congrFun fixedZero direction).symm

private theorem profileRestart_gravityConnection_origin_eq_fixed :
    ProfileRestartActual.gravityConnection 0 =
      FixedP506JointActual.gravityConnection 0 := by
  rw [profileRestartActual_eq_fixedCartan,
    fixedP506L0CartanRestartActual_gravityConnection_origin_eq_fixedJointCartan,
    fixedJointCartanConnection_zero_eq_jointActionSuccessor_origin,
    fixedP506JointActionSuccessor_gravityConnection]

private theorem profileRestart_matterCovariantDerivative_spatial_eq_fixed
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative ProfileRestartActual 0 direction.succ =
      holonomicMatterCovariantDerivative FixedP506JointActual 0
        direction.succ := by
  unfold holonomicMatterCovariantDerivative
  rw [profileRestart_matter_eq_fixed,
    profileRestart_gravityConnection_origin_eq_fixed,
    profileRestart_gaugeConnection_origin_eq_fixed]

private theorem profileRestart_knownVector_eq_fixed :
    holonomicDiracDualCurrentCoframeMatterKnownVector ProfileRestartActual 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        FixedP506JointActual 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [profileRestart_coframe_eq_fixed,
    profileRestart_scalar_origin_eq_fixed,
    profileRestart_matter_eq_fixed]
  simp_rw [profileRestart_matterCovariantDerivative_spatial_eq_fixed]

private theorem profileRestart_connectionAction_time_eq_fixed :
    holonomicMatterConnectionAction ProfileRestartActual 0
        canonicalLorentzianTimeDirection =
      holonomicMatterConnectionAction FixedP506JointActual 0
        canonicalLorentzianTimeDirection := by
  unfold holonomicMatterConnectionAction
  rw [profileRestart_gravityConnection_origin_eq_fixed,
    profileRestart_gaugeConnection_origin_eq_fixed,
    profileRestart_matter_eq_fixed]

private theorem profileRestart_actionCovariantTime_eq_fixed :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        ProfileRestartActual 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        FixedP506JointActual 0 := by
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
  rw [profileRestart_coframe_eq_fixed,
    profileRestart_knownVector_eq_fixed]

private theorem profileRestart_matterCovariantTime_eq_fixed :
    holonomicMatterCovariantDerivative ProfileRestartActual 0
        canonicalLorentzianTimeDirection =
      holonomicMatterCovariantDerivative FixedP506JointActual 0
        canonicalLorentzianTimeDirection := by
  unfold holonomicMatterCovariantDerivative
  rw [profileRestart_matter_eq_fixed,
    profileRestart_gravityConnection_origin_eq_fixed,
    profileRestart_gaugeConnection_origin_eq_fixed]

private theorem profileRestart_primalTimeResponseWrite_zero :
    diracDualCurrentCoframeMatterTimeResponseWrite ProfileRestartActual = 0 := by
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
  rw [profileRestart_actionCovariantTime_eq_fixed,
    profileRestart_matterCovariantTime_eq_fixed]
  exact fixedP506JointActual_primalTimeResponseWrite_zero

private theorem profilePrimalActual_eq_restart :
    ProfilePrimalActual = ProfileRestartActual := by
  unfold ProfilePrimalActual
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
  rw [profileRestart_primalTimeResponseWrite_zero,
    installMatterLinearTimeResponse_zero]

private theorem fixedJoint_coframeFirstJet_origin_identity :
    holonomicCoframeFirstJetAt FixedP506JointActual.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]
  have zeroSlice :=
    fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice
      (0 : StageNineSpatialPoint)
  have zeroSlicePoint :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint,
        canonicalLorentzianTimeDirection, Fin.sum_univ_three]
  rw [zeroSlicePoint] at zeroSlice
  simpa [identityCoframeMatterGeometry] using zeroSlice

private theorem profileRestart_conjugateMatterDerivative_eq_fixed
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual ProfileRestartActual 0 direction =
      holonomicConjugateMatterDerivativeDual FixedP506JointActual 0
        direction := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [profileRestart_conjugateMatter_eq_fixed]

private theorem profileRestart_liveAdjointVelocity_eq_fixed :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        ProfileRestartActual 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 := by
  apply liveCoframeActionVelocity_eq_of_pointData
  · rw [profileRestart_coframe_eq_fixed]
  · exact profileRestart_gravityConnection_origin_eq_fixed
  · exact profileRestart_gaugeConnection_origin_eq_fixed
  · exact profileRestart_scalar_origin_eq_fixed
  · exact congrFun profileRestart_conjugateMatter_eq_fixed 0
  · exact profileRestart_conjugateMatterDerivative_eq_fixed

private theorem fixedJoint_liveAdjointVelocity_zero :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        FixedP506JointActual 0 = 0 := by
  calc
    _ =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          FixedP506JointActual 0 :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        FixedP506JointActual 0 fixedJoint_coframeFirstJet_origin_identity
    _ = holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity
          FixedP506JointActual 0 :=
      (holonomicDiracDualIdentityCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity
        FixedP506JointActual 0).symm
    _ = 0 := fixedP506JointActual_diracDualAdjointActionVelocity_zero

private theorem profileRestart_liveAdjointVelocity_zero :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        ProfileRestartActual 0 = 0 := by
  rw [profileRestart_liveAdjointVelocity_eq_fixed,
    fixedJoint_liveAdjointVelocity_zero]

private theorem profileRestart_conjugateMatterDerivative_time_zero :
    holonomicConjugateMatterDerivativeDual ProfileRestartActual 0
        canonicalLorentzianTimeDirection = 0 := by
  have fixedInputZero :
      holonomicConjugateMatterDerivativeDual InputActual 0
          canonicalLorentzianTimeDirection = 0 := by
    apply LinearMap.ext
    intro matter
    rw [holonomicConjugateMatterDerivativeDual_apply InputActual
      fixedP506FormNativeJointActionSolvedSuccessor_smooth]
    rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
      fixedP506JointActionSuccessor_conjugateMatter]
    exact fixedP506JointActual_conjugateMatter_temporalDerivative_zero matter
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [profileRestartActual_conjugateMatter_eq_input]
  exact fixedInputZero

private theorem profilePrimal_adjointTimeResponseWrite_zero :
    liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual = 0 := by
  rw [profilePrimalActual_eq_restart]
  unfold liveCoframeConjugateMatterTimeResponseWrite
  rw [profileRestart_liveAdjointVelocity_zero,
    profileRestart_conjugateMatterDerivative_time_zero]
  simp

/-- At the fixed origin Cartan restart, both occurrence-native matter writes
are already exact: the primal response and the independently generated
adjoint response vanish on the same fixed lineage.  This exposes existing
source/action output for downstream time-axis consumers; it accepts no
velocity, target, equation, or settlement premise. -/
theorem
    fixedP506L0CartanRestartActual_origin_primalAdjointTimeResponseWrites_zero :
    diracDualCurrentCoframeMatterTimeResponseWrite
          (fixedP506L0CartanRestartActual (0 : StageNineSpatialPoint)) = 0 ∧
      liveCoframeConjugateMatterTimeResponseWrite
          (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
            (fixedP506L0CartanRestartActual
              (0 : StageNineSpatialPoint))) = 0 := by
  rw [← profileRestartActual_eq_fixedCartan]
  change
    diracDualCurrentCoframeMatterTimeResponseWrite ProfileRestartActual = 0 ∧
      liveCoframeConjugateMatterTimeResponseWrite ProfilePrimalActual = 0
  exact ⟨profileRestart_primalTimeResponseWrite_zero,
    profilePrimal_adjointTimeResponseWrite_zero⟩

/-- The fixed occurrence-native adjoint action profile is exactly zero at the
common origin.  This is an action-profile readout, not a supplied equation. -/
theorem fixedProfile_adjointVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      positiveSmoothUnifiedSource InputActual 0).adjointVelocity = 0 := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
  change
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        ProfilePrimalActual 0 = 0
  rw [profilePrimalActual_eq_restart,
    profileRestart_liveAdjointVelocity_zero]

/-- The fixed occurrence-native primal action profile is exactly zero at the
same common origin. -/
theorem fixedProfile_matterVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      positiveSmoothUnifiedSource InputActual 0).matterVelocity = 0 := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  change
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        ProfileRestartActual 0 = 0
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
  rw [profileRestart_coframe_eq_fixed,
    profileRestart_knownVector_eq_fixed,
    profileRestart_connectionAction_time_eq_fixed]
  exact fixedP506JointActual_primalRawVelocity_zero

/-- The source/current-only complete-joint development therefore has zero
primal matter temporal first jet at the common origin. -/
theorem newActual_matterCoordinateTimeDerivative_origin_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewActual.matter point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newActual_matterCoordinateTimeDerivative_origin,
    fixedProfile_matterVelocity_zero]
  simp

/-- The independent Dirac dual has the same exact temporal first-jet value. -/
theorem newActual_conjugateMatterTimeDerivative_origin_zero :
    holonomicConjugateMatterDerivativeDual NewActual 0
        canonicalLorentzianTimeDirection =
      0 := by
  rw [newActual_conjugateMatterTimeDerivative_origin_eq_profilePrimalActionVelocity]
  rw [profilePrimalActual_eq_restart,
    profileRestart_liveAdjointVelocity_zero]

private theorem newActual_coframe_temporalDerivative_origin_zero :
    fieldDirectionalDerivative NewActual.coframe 0
        canonicalLorentzianTimeDirection =
      0 := by
  unfold fieldDirectionalDerivative
  rw [newActual_coframe_eq_profilePrimal]
  change
    (fderiv ℝ ProfileRestartActual.coframe 0)
        (coordinateDirection canonicalLorentzianTimeDirection) = 0
  rw [profileRestart_coframe_eq_fixed,
    fixedP506JointActual_coframe_fderiv_coordinate_zero]

private theorem newCartanInput_matterCoordinates_differentiableAt :
    DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (NewCartanInput.matter point)) 0 := by
  change DifferentiableAt ℝ
    (fun point => matterCoordinateEquiv (NewActual.matter point)) 0
  exact newActual_matterCoordinates_hasFDerivAt_origin.differentiableAt

private theorem newCartanInput_conjugateMatterCoordinates_differentiableAt :
    DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates NewCartanInput) 0 := by
  change DifferentiableAt ℝ
    (holonomicConjugateMatterCoordinates NewActual) 0
  exact newActual_conjugateMatterCoordinates_differentiableAt_origin

private theorem newCartanInput_matterCoordinateTimeDerivative_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (NewCartanInput.matter point))
        0 canonicalLorentzianTimeDirection =
      0 := by
  change fieldDirectionalDerivative
      (fun point => matterCoordinateEquiv (NewActual.matter point))
      0 canonicalLorentzianTimeDirection = 0
  exact newActual_matterCoordinateTimeDerivative_origin_zero

private theorem newCartanInput_conjugateMatterTimeDerivative_zero :
    holonomicConjugateMatterDerivativeDual NewCartanInput 0
        canonicalLorentzianTimeDirection =
      0 := by
  change holonomicConjugateMatterDerivativeDual NewActual 0
      canonicalLorentzianTimeDirection = 0
  exact newActual_conjugateMatterTimeDerivative_origin_zero

private theorem newCartanInput_coframe_temporalDerivative_zero :
    fieldDirectionalDerivative NewCartanInput.coframe 0
        canonicalLorentzianTimeDirection =
      0 := by
  change fieldDirectionalDerivative NewActual.coframe 0
      canonicalLorentzianTimeDirection = 0
  exact newActual_coframe_temporalDerivative_origin_zero

private theorem fieldDirectionalDerivative_continuousBilinearAt
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (bilinear : V →L[ℝ] W →L[ℝ] X)
    (first : BasePoint → V) (second : BasePoint → W)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => bilinear (first candidate) (second candidate))
        0 direction =
      bilinear (fieldDirectionalDerivative first 0 direction) (second 0) +
        bilinear (first 0)
          (fieldDirectionalDerivative second 0 direction) := by
  have outerDerivative : HasFDerivAt
      (fun candidate => bilinear (first candidate))
      (bilinear.comp (fderiv ℝ first 0)) 0 :=
    bilinear.hasFDerivAt.comp 0 firstDifferentiable.hasFDerivAt
  have totalDerivative :
      fderiv ℝ
          (fun candidate => bilinear (first candidate) (second candidate))
          0 =
        (bilinear (first 0)).comp (fderiv ℝ second 0) +
          (bilinear.comp (fderiv ℝ first 0)).flip (second 0) :=
    (outerDerivative.clm_apply secondDifferentiable.hasFDerivAt).fderiv
  change
    fderiv ℝ
        (fun candidate => bilinear (first candidate) (second candidate))
        0 (coordinateDirection direction) = _
  rw [totalDerivative]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  change
    bilinear (first 0)
          (fieldDirectionalDerivative second 0 direction) +
        bilinear (fieldDirectionalDerivative first 0 direction)
          (second 0) = _
  abel

private def newCartanLorentzSpinCoordinateVector
    (variationDirection : LorentzianIndex) (internalPair : Fin 6)
    (point : BasePoint) : MatterCoordinateCarrier :=
  lorentzSpinCoordinateLinear variationDirection internalPair
    (matterCoordinateEquiv (NewCartanInput.matter point))

private theorem newCartanLorentzSpinCoordinateVector_differentiableAt
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (newCartanLorentzSpinCoordinateVector
        variationDirection internalPair) 0 := by
  exact
    (lorentzSpinCoordinateLinear variationDirection internalPair
      ).differentiableAt.comp 0
        newCartanInput_matterCoordinates_differentiableAt

private theorem
    newCartanLorentzSpinCoordinateVector_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (newCartanLorentzSpinCoordinateVector
          variationDirection internalPair)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let coordinates : BasePoint → MatterCoordinateCarrier := fun point =>
    matterCoordinateEquiv (NewCartanInput.matter point)
  let action :=
    lorentzSpinCoordinateLinear variationDirection internalPair
  have composed :=
    action.hasFDerivAt.comp 0
      newCartanInput_matterCoordinates_differentiableAt.hasFDerivAt
  rw [show
    newCartanLorentzSpinCoordinateVector variationDirection internalPair =
      action ∘ coordinates by rfl]
  unfold fieldDirectionalDerivative
  rw [composed.fderiv]
  change
    action
        (fieldDirectionalDerivative coordinates 0
          canonicalLorentzianTimeDirection) =
      0
  rw [show
    fieldDirectionalDerivative coordinates 0
        canonicalLorentzianTimeDirection = 0 by
      exact newCartanInput_matterCoordinateTimeDerivative_zero]
  exact map_zero action

private theorem newCartanFrozenLorentzMatterCoefficient_normalForm
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (withCoframe (toContinuumPointField NewCartanInput point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point =>
        (NewCartanInput.conjugateMatter point
          (lorentzSpinActionVector variationDirection internalPair
            (NewCartanInput.matter point))).re := by
  funext point
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField, Matrix.det_one,
    abs_one, one_mul, matterDualFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart]
  rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) =
        identityCoframeMatterGeometry by rfl]
  simp only [inverseCoframeDiracGamma_identity]
  simp [lorentzSpinActionVector, Fin.sum_univ_four]

private theorem newCartanFrozenLorentzMatterCoefficient_coordinateExpansion
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    (fun point =>
      formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
        point
        (withCoframe (toContinuumPointField NewCartanInput point) 1)
        (loweredLorentzBivectorOneFormCoordinate
          variationDirection internalPair)) =
      fun point =>
        ∑ index : MatterCoordinateIndex,
          (newCartanLorentzSpinCoordinateVector
                variationDirection internalPair point index *
            NewCartanInput.conjugateMatter point
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ)))).re := by
  rw [newCartanFrozenLorentzMatterCoefficient_normalForm]
  funext point
  have vectorFidelity :
      matterCoordinateEquiv.symm
          (newCartanLorentzSpinCoordinateVector
            variationDirection internalPair point) =
        lorentzSpinActionVector variationDirection internalPair
          (NewCartanInput.matter point) := by
    simp [newCartanLorentzSpinCoordinateVector]
  rw [← vectorFidelity, matterDual_coordinate_expansion]
  simp only [Complex.re_sum]

private theorem
    newCartanInput_conjugateMatterCoordinates_temporalDerivative_zero :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates NewCartanInput)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    holonomicConjugateMatterDerivativeCoordinates NewCartanInput 0
        canonicalLorentzianTimeDirection =
      0
  apply PiLp.ext
  intro index
  change
    holonomicConjugateMatterDerivativeCoordinates NewCartanInput 0
        canonicalLorentzianTimeDirection index =
      (0 : ℂ)
  have evaluated := LinearMap.congr_fun
    newCartanInput_conjugateMatterTimeDerivative_zero
    (matterCoordinateEquiv.symm
      (EuclideanSpace.single index (1 : ℂ)))
  unfold holonomicConjugateMatterDerivativeDual at evaluated
  simpa only [matterDualOfCoordinates_basis_apply,
    LinearMap.zero_apply] using evaluated

private theorem newCartanFrozenLorentzMatterCoefficient_differentiableAt
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (withCoframe (toContinuumPointField NewCartanInput point) 1)
          (loweredLorentzBivectorOneFormCoordinate
            variationDirection internalPair)) 0 := by
  rw [newCartanFrozenLorentzMatterCoefficient_coordinateExpansion]
  simp_rw [←
    matterCoordinateRealPairingBilinear_matterDualCoordinates]
  let bilinear :=
    matterCoordinateRealPairingBilinear.toContinuousBilinearMap
  change DifferentiableAt ℝ
    (fun point => bilinear
      (newCartanLorentzSpinCoordinateVector
        variationDirection internalPair point)
      (holonomicConjugateMatterCoordinates NewCartanInput point)) 0
  have outerDerivative : HasFDerivAt
      (fun candidate => bilinear
        (newCartanLorentzSpinCoordinateVector
          variationDirection internalPair candidate))
      (bilinear.comp
        (fderiv ℝ
          (newCartanLorentzSpinCoordinateVector
            variationDirection internalPair) 0)) 0 :=
    bilinear.hasFDerivAt.comp
      0
      (newCartanLorentzSpinCoordinateVector_differentiableAt
        variationDirection internalPair).hasFDerivAt
  exact
    (outerDerivative.clm_apply
      newCartanInput_conjugateMatterCoordinates_differentiableAt.hasFDerivAt
      ).differentiableAt

private theorem
    newCartanFrozenLorentzMatterCoefficient_temporalDerivative_zero
    (variationDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource
            0 point
            (withCoframe (toContinuumPointField NewCartanInput point) 1)
            (loweredLorentzBivectorOneFormCoordinate
              variationDirection internalPair))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newCartanFrozenLorentzMatterCoefficient_coordinateExpansion]
  simp_rw [←
    matterCoordinateRealPairingBilinear_matterDualCoordinates]
  let bilinear :=
    matterCoordinateRealPairingBilinear.toContinuousBilinearMap
  change
    fieldDirectionalDerivative
        (fun point => bilinear
          (newCartanLorentzSpinCoordinateVector
            variationDirection internalPair point)
          (holonomicConjugateMatterCoordinates NewCartanInput point))
        0 canonicalLorentzianTimeDirection =
      0
  rw [fieldDirectionalDerivative_continuousBilinearAt
    bilinear
    (newCartanLorentzSpinCoordinateVector
      variationDirection internalPair)
    (holonomicConjugateMatterCoordinates NewCartanInput)
    (newCartanLorentzSpinCoordinateVector_differentiableAt
      variationDirection internalPair)
    newCartanInput_conjugateMatterCoordinates_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanLorentzSpinCoordinateVector_temporalDerivative_zero,
    newCartanInput_conjugateMatterCoordinates_temporalDerivative_zero]
  simp

private theorem fieldDirectionalDerivative_pi_apply_of_differentiableAt
    {I V : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (field : BasePoint → I → V)
    (direction : LorentzianIndex) (index : I)
    (fieldDifferentiableAt : DifferentiableAt ℝ field 0) :
    (fieldDirectionalDerivative field 0 direction) index =
      fieldDirectionalDerivative (fun candidate => field candidate index)
        0 direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply fieldDifferentiableAt index
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] V =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem fieldDirectionalDerivative_const_mul_real_at_origin
    (field : BasePoint → ℝ)
    (fieldDifferentiable : DifferentiableAt ℝ field 0)
    (scalar : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => scalar * field point)
        0 direction =
      scalar * fieldDirectionalDerivative field 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul fieldDifferentiable scalar]
  rfl

private def newCartanFrozenSpinResponse (point : BasePoint) :
    PhysicalBivectorThreeForm :=
  diracDualFormNativeActionSpinResponsePointCoframe
    positiveSmoothUnifiedSource NewCartanInput (point, 1)

private theorem newCartanFrozenSpinResponse_coordinate
    (point : BasePoint) (internalPair : Fin 6) (triple : Fin 4) :
    newCartanFrozenSpinResponse point internalPair triple =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
          point
          (withCoframe
            (toContinuumPointField NewCartanInput point) 1)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) := by
  unfold newCartanFrozenSpinResponse
    diracDualFormNativeActionSpinResponsePointCoframe
    formNativePhysicalSpinCurrentThreeForm
  change
    -formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 point
        (withCoframe
          (toContinuumPointField NewCartanInput point) 1)
        internalPair triple =
      _
  conv_lhs =>
    rw [show triple = missingTripleOfOneForm
        (missingTripleOfOneForm triple) by
      exact (missingTripleOfOneForm_involutive triple).symm]
  rw [formNativeMatterSpinThreeForm_coordinate]

private theorem newCartanFrozenSpinResponse_differentiableAt :
    DifferentiableAt ℝ newCartanFrozenSpinResponse 0 := by
  apply differentiableAt_pi.mpr
  intro internalPair
  apply differentiableAt_pi.mpr
  intro triple
  let direction := missingTripleOfOneForm triple
  let coefficient : BasePoint → ℝ := fun point =>
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
      point
      (withCoframe
        (toContinuumPointField NewCartanInput point) 1)
      (loweredLorentzBivectorOneFormCoordinate direction internalPair)
  rw [show
    (fun point => newCartanFrozenSpinResponse point internalPair triple) =
      fun point => (-oneWedgeThreeSign direction) * coefficient point by
    funext point
    rw [newCartanFrozenSpinResponse_coordinate]
    ring]
  exact
    (newCartanFrozenLorentzMatterCoefficient_differentiableAt
      direction internalPair).const_mul (-oneWedgeThreeSign direction)

private theorem
    newCartanFrozenSpinResponse_coordinate_temporalDerivative_zero
    (internalPair : Fin 6) (triple : Fin 4) :
    fieldDirectionalDerivative
        (fun point => newCartanFrozenSpinResponse point internalPair triple)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let direction := missingTripleOfOneForm triple
  let coefficient : BasePoint → ℝ := fun point =>
    formNativeLorentzMatterFirstCoefficient positiveSmoothUnifiedSource 0
      point
      (withCoframe
        (toContinuumPointField NewCartanInput point) 1)
      (loweredLorentzBivectorOneFormCoordinate direction internalPair)
  rw [show
    (fun point => newCartanFrozenSpinResponse point internalPair triple) =
      fun point => (-oneWedgeThreeSign direction) * coefficient point by
    funext point
    rw [newCartanFrozenSpinResponse_coordinate]
    ring]
  rw [fieldDirectionalDerivative_const_mul_real_at_origin coefficient
    (newCartanFrozenLorentzMatterCoefficient_differentiableAt
      direction internalPair)
    (-oneWedgeThreeSign direction) canonicalLorentzianTimeDirection,
    newCartanFrozenLorentzMatterCoefficient_temporalDerivative_zero]
  simp

private theorem newCartanFrozenSpinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative newCartanFrozenSpinResponse 0
        canonicalLorentzianTimeDirection =
      0 := by
  funext internalPair triple
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
    newCartanFrozenSpinResponse canonicalLorentzianTimeDirection internalPair
    newCartanFrozenSpinResponse_differentiableAt]
  rw [fieldDirectionalDerivative_pi_apply_of_differentiableAt
    (fun point => newCartanFrozenSpinResponse point internalPair)
    canonicalLorentzianTimeDirection triple
    (differentiableAt_pi.mp
      newCartanFrozenSpinResponse_differentiableAt internalPair)]
  exact
    newCartanFrozenSpinResponse_coordinate_temporalDerivative_zero
      internalPair triple

private theorem newCartanInput_coframe_differentiableAt :
    DifferentiableAt ℝ NewCartanInput.coframe 0 := by
  change DifferentiableAt ℝ NewActual.coframe 0
  rw [newActual_coframe_eq_profilePrimal]
  change DifferentiableAt ℝ ProfileRestartActual.coframe 0
  rw [profileRestart_coframe_eq_fixed]
  exact fixedP506JointActual_coframe_differentiableAt

private theorem newCartanInput_coframe_origin_one :
    NewCartanInput.coframe 0 = 1 := by
  change NewActual.coframe 0 = 1
  rw [newActual_coframe_eq_profilePrimal]
  change ProfileRestartActual.coframe 0 = 1
  rw [profileRestart_coframe_eq_fixed,
    fixedP506JointActual_coframe_origin_one]

private theorem conjugateMatterBasis_differentiableAt_of_coordinates
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coordinatesDifferentiable : DifferentiableAt ℝ
      (holonomicConjugateMatterCoordinates configuration) point)
    (index : MatterCoordinateIndex) :
    DifferentiableAt ℝ
      (fun target =>
        configuration.conjugateMatter target
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) point := by
  let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj index).comp
      (EuclideanSpace.equiv MatterCoordinateIndex ℂ).toContinuousLinearMap
  have coordinateDifferentiable : DifferentiableAt ℝ
      (fun target =>
        holonomicConjugateMatterCoordinates configuration target index) point :=
    (projection.restrictScalars ℝ).differentiableAt.comp point
      coordinatesDifferentiable
  change DifferentiableAt ℝ (fun target =>
    matterDualCoordinates (configuration.conjugateMatter target) index) point
  exact coordinateDifferentiable

private theorem newCartanSpinResponsePointCoframe_differentiableAt :
    DifferentiableAt ℝ
      (diracDualFormNativeActionSpinResponsePointCoframe
        positiveSmoothUnifiedSource NewCartanInput) (0, 1) := by
  exact
    diracDualFormNativeActionSpinResponsePointCoframe_differentiableAt_of_local
      positiveSmoothUnifiedSource NewCartanInput 0 1 (by simp)
      newCartanInput_matterCoordinates_differentiableAt
      (conjugateMatterBasis_differentiableAt_of_coordinates
        NewCartanInput 0
        newCartanInput_conjugateMatterCoordinates_differentiableAt)

private theorem newCartanInput_fderiv_pointCoframe_eq_frozen :
    (fderiv ℝ
        (diracDualFormNativeActionSpinResponsePointCoframe
          positiveSmoothUnifiedSource NewCartanInput ∘
          fun point => (point, NewCartanInput.coframe point)) 0)
        (coordinateDirection canonicalLorentzianTimeDirection) =
      (fderiv ℝ
        (diracDualFormNativeActionSpinResponsePointCoframe
          positiveSmoothUnifiedSource NewCartanInput ∘
          fun point => (point, (1 : LorentzianCoframe))) 0)
        (coordinateDirection canonicalLorentzianTimeDirection) := by
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe
      positiveSmoothUnifiedSource NewCartanInput
  have actualInner : HasFDerivAt
      (fun point : BasePoint => (point, NewCartanInput.coframe point))
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (fderiv ℝ NewCartanInput.coframe 0)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      newCartanInput_coframe_differentiableAt.hasFDerivAt
  have frozenInner : HasFDerivAt
      (fun point : BasePoint => (point, (1 : LorentzianCoframe)))
      ((ContinuousLinearMap.id ℝ BasePoint).prod
        (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      (hasFDerivAt_const (x := (0 : BasePoint))
        (c := (1 : LorentzianCoframe)))
  have outerAtActual : DifferentiableAt ℝ outer
      (0, NewCartanInput.coframe 0) := by
    simpa only [newCartanInput_coframe_origin_one] using
      newCartanSpinResponsePointCoframe_differentiableAt
  have actualComposition :=
    outerAtActual.hasFDerivAt.comp 0 actualInner
  have frozenComposition :=
    newCartanSpinResponsePointCoframe_differentiableAt.hasFDerivAt.comp
      0 frozenInner
  rw [actualComposition.fderiv, frozenComposition.fderiv,
    newCartanInput_coframe_origin_one]
  change
    (fderiv ℝ outer (0, 1))
        (coordinateDirection canonicalLorentzianTimeDirection,
          (fderiv ℝ NewCartanInput.coframe 0)
            (coordinateDirection canonicalLorentzianTimeDirection)) =
      (fderiv ℝ outer (0, 1))
        (coordinateDirection canonicalLorentzianTimeDirection, 0)
  rw [show
    (fderiv ℝ NewCartanInput.coframe 0)
        (coordinateDirection canonicalLorentzianTimeDirection) = 0 by
      exact newCartanInput_coframe_temporalDerivative_zero]

private theorem newCartanInput_spinResponse_temporalDerivative_zero :
    fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt
          positiveSmoothUnifiedSource NewCartanInput)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe
      positiveSmoothUnifiedSource NewCartanInput
  rw [show
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        NewCartanInput =
      outer ∘ fun point => (point, NewCartanInput.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource NewCartanInput point]
  unfold fieldDirectionalDerivative
  rw [newCartanInput_fderiv_pointCoframe_eq_frozen]
  have frozenZero := newCartanFrozenSpinResponse_temporalDerivative_zero
  unfold fieldDirectionalDerivative newCartanFrozenSpinResponse at frozenZero
  exact frozenZero

theorem newCartanInput_coframe_eq_input :
    NewCartanInput.coframe = InputActual.coframe := by
  change NewActual.coframe = InputActual.coframe
  rw [newActual_coframe_eq_profileRestart,
    profileRestartActual_coframe_eq_input]

private theorem newCartanInput_spinResponse_differentiableAt :
    DifferentiableAt ℝ
      (diracDualFormNativeActionSpinResponseAt
        positiveSmoothUnifiedSource NewCartanInput) 0 := by
  let outer :=
    diracDualFormNativeActionSpinResponsePointCoframe
      positiveSmoothUnifiedSource NewCartanInput
  have innerDifferentiable : DifferentiableAt ℝ
      (fun point : BasePoint =>
        (point, NewCartanInput.coframe point)) 0 :=
    differentiableAt_id.prodMk newCartanInput_coframe_differentiableAt
  have outerAtActual : DifferentiableAt ℝ outer
      (0, NewCartanInput.coframe 0) := by
    simpa only [newCartanInput_coframe_origin_one] using
      newCartanSpinResponsePointCoframe_differentiableAt
  rw [show
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        NewCartanInput =
      outer ∘ fun point => (point, NewCartanInput.coframe point) by
    funext point
    exact diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
      positiveSmoothUnifiedSource NewCartanInput point]
  exact outerAtActual.comp 0 innerDifferentiable

private def newCartanInputCoframeSpinResponseCarrier (point : BasePoint) :
    LorentzianCoframe × PhysicalBivectorThreeForm :=
  (NewCartanInput.coframe point,
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      NewCartanInput point)

private theorem newCartanInputCoframeSpinResponseCarrier_differentiableAt :
    DifferentiableAt ℝ newCartanInputCoframeSpinResponseCarrier 0 :=
  newCartanInput_coframe_differentiableAt.prodMk
    newCartanInput_spinResponse_differentiableAt

private theorem
    newCartanInputCoframeSpinResponseCarrier_temporalDerivative_zero :
    fieldDirectionalDerivative newCartanInputCoframeSpinResponseCarrier 0
        canonicalLorentzianTimeDirection =
      0 := by
  have productDerivative :=
    newCartanInput_coframe_differentiableAt.fderiv_prodMk
      newCartanInput_spinResponse_differentiableAt
  unfold fieldDirectionalDerivative
    newCartanInputCoframeSpinResponseCarrier
  rw [productDerivative]
  change
    (fieldDirectionalDerivative NewCartanInput.coframe 0
        canonicalLorentzianTimeDirection,
      fieldDirectionalDerivative
        (diracDualFormNativeActionSpinResponseAt
          positiveSmoothUnifiedSource NewCartanInput)
        0 canonicalLorentzianTimeDirection) =
      0
  rw [newCartanInput_coframe_temporalDerivative_zero,
    newCartanInput_spinResponse_temporalDerivative_zero]
  rfl

theorem newCartanInput_cartanContorsion_component_differentiableAt
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        diracDualFormNativeActionCartanContorsionAt
          positiveSmoothUnifiedSource NewCartanInput point
          formDirection internalPair) 0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      NewCartanInput 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : newCartanInputCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold newCartanInputCoframeSpinResponseCarrier response
    rw [newCartanInput_coframe_origin_one]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (newCartanInputCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact cartanContorsionCoframeResponseComponent_differentiableAt
      (1 : LorentzianCoframe) response (by simp)
      formDirection internalPair
  change DifferentiableAt ℝ
    (outer ∘ newCartanInputCoframeSpinResponseCarrier) 0
  exact outerDifferentiable.comp 0
    newCartanInputCoframeSpinResponseCarrier_differentiableAt

theorem
    newCartanInput_cartanContorsion_component_temporalDerivative_zero
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point
            formDirection internalPair)
        0 canonicalLorentzianTimeDirection =
      0 := by
  let response :=
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
      NewCartanInput 0
  let outer :=
    cartanContorsionCoframeResponseComponent formDirection internalPair
  have carrierOrigin : newCartanInputCoframeSpinResponseCarrier 0 =
      ((1 : LorentzianCoframe), response) := by
    unfold newCartanInputCoframeSpinResponseCarrier response
    rw [newCartanInput_coframe_origin_one]
  have outerDifferentiable : DifferentiableAt ℝ outer
      (newCartanInputCoframeSpinResponseCarrier 0) := by
    rw [carrierOrigin]
    exact cartanContorsionCoframeResponseComponent_differentiableAt
      (1 : LorentzianCoframe) response (by simp)
      formDirection internalPair
  have composition := outerDifferentiable.hasFDerivAt.comp 0
    newCartanInputCoframeSpinResponseCarrier_differentiableAt.hasFDerivAt
  rw [show
    (fun point =>
      diracDualFormNativeActionCartanContorsionAt
        positiveSmoothUnifiedSource NewCartanInput point
        formDirection internalPair) =
      outer ∘ newCartanInputCoframeSpinResponseCarrier by rfl]
  unfold fieldDirectionalDerivative
  rw [composition.fderiv]
  change
    (fderiv ℝ outer (newCartanInputCoframeSpinResponseCarrier 0))
        (fieldDirectionalDerivative newCartanInputCoframeSpinResponseCarrier 0
          canonicalLorentzianTimeDirection) =
      0
  rw [newCartanInputCoframeSpinResponseCarrier_temporalDerivative_zero]
  simp

private theorem newCartanInput_cartanSkew131_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          1 3 1) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 1 4

private theorem newCartanInput_cartanSkew223_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          2 2 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 2 3

private theorem newCartanInput_cartanSkew031_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          0 3 1) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 0 4

private theorem newCartanInput_cartanSkew023_differentiableAt :
    DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          0 2 3) 0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_differentiableAt 0 3

private theorem newCartanInput_cartanSkew131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource NewCartanInput point)
            1 3 1)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_temporalDerivative_zero 1 4

private theorem newCartanInput_cartanSkew223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          lorentzSkewConnectionOfBivectorOneForm
            (diracDualFormNativeActionCartanContorsionAt
              positiveSmoothUnifiedSource NewCartanInput point)
            2 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  simpa [lorentzSkewConnectionOfBivectorOneForm,
    loweredLorentzBivectorMatrix,
    orientedLorentzBivectorBasisCoefficient,
    pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six] using
    newCartanInput_cartanContorsion_component_temporalDerivative_zero 2 3

private theorem newCartanInput_leviCivitaComponent_differentiableAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        identityECSpinConnectionComponentOfCarrier
          formDirection internalOut internalIn
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative)) 0 := by
  rw [newCartanInput_coframe_eq_input]
  exact
    fixedP506JointActionSolvedSuccessor_leviCivitaComponent_differentiableAt
      formDirection internalOut internalIn

private theorem newCartanInput_leviCivita131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newCartanInput_coframe_eq_input]
  exact
    fixedP506JointActionSolvedSuccessor_leviCivita131_temporalDerivative_zero

private theorem newCartanInput_leviCivita223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
            (NewCartanInput.coframe point,
              (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                ).derivative))
        0 canonicalLorentzianTimeDirection =
      0 := by
  rw [newCartanInput_coframe_eq_input]
  exact
    fixedP506JointActionSolvedSuccessor_leviCivita223_temporalDerivative_zero

private theorem fieldDirectionalDerivative_add_real_at_origin
    (first second : BasePoint → ℝ)
    (firstDifferentiable : DifferentiableAt ℝ first 0)
    (secondDifferentiable : DifferentiableAt ℝ second 0)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun point => first point + second point)
        0 direction =
      fieldDirectionalDerivative first 0 direction +
        fieldDirectionalDerivative second 0 direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add firstDifferentiable secondDifferentiable]
  rfl

private theorem newCartanInput_cartanConnection131_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource NewCartanInput point 1 3 1)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 1 3 1
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource NewCartanInput point)
              1 3 1)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fieldDirectionalDerivative_add_real_at_origin _ _
    (newCartanInput_leviCivitaComponent_differentiableAt 1 3 1)
    newCartanInput_cartanSkew131_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_leviCivita131_temporalDerivative_zero,
    newCartanInput_cartanSkew131_temporalDerivative_zero]
  norm_num

private theorem newCartanInput_cartanConnection223_temporalDerivative_zero :
    fieldDirectionalDerivative
        (fun point =>
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource NewCartanInput point 2 2 3)
        0 canonicalLorentzianTimeDirection =
      0 := by
  change
    fieldDirectionalDerivative
        (fun point =>
          identityECSpinConnectionComponentOfCarrier 2 2 3
              (NewCartanInput.coframe point,
                (holonomicCoframeFirstJetAt NewCartanInput.coframe point
                  ).derivative) +
            lorentzSkewConnectionOfBivectorOneForm
              (diracDualFormNativeActionCartanContorsionAt
                positiveSmoothUnifiedSource NewCartanInput point)
              2 2 3)
        0 canonicalLorentzianTimeDirection =
      0
  rw [fieldDirectionalDerivative_add_real_at_origin _ _
    (newCartanInput_leviCivitaComponent_differentiableAt 2 2 3)
    newCartanInput_cartanSkew223_differentiableAt
    canonicalLorentzianTimeDirection,
    newCartanInput_leviCivita223_temporalDerivative_zero,
    newCartanInput_cartanSkew223_temporalDerivative_zero]
  norm_num

/-- The authoritative fixed P506/L0 global actual has zero temporal derivative
in the Cartan connection coordinate consumed by the `131` curvature bracket. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_cartanConnection131_temporalDerivative_zero :
    gravityConnectionDerivative NewActual 0
        canonicalLorentzianTimeDirection 1 3 1 =
      0 := by
  unfold gravityConnectionDerivative NewActual
    fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact newCartanInput_cartanConnection131_temporalDerivative_zero

/-- The matching `223` Cartan connection coordinate has the same exact
fixed-lineage temporal derivative. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_cartanConnection223_temporalDerivative_zero :
    gravityConnectionDerivative NewActual 0
        canonicalLorentzianTimeDirection 2 2 3 =
      0 := by
  unfold gravityConnectionDerivative NewActual
    fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  exact newCartanInput_cartanConnection223_temporalDerivative_zero

/-- The `031` coordinate of the authoritative global Cartan connection is
differentiable at the fixed origin. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection031_differentiableAt_origin :
    DifferentiableAt ℝ
      (fun point =>
        NewActual.gravityConnection point 0 3 1) 0 := by
  unfold NewActual fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  change DifferentiableAt ℝ
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 0 3 1
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative) +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          0 3 1) 0
  exact
    (newCartanInput_leviCivitaComponent_differentiableAt 0 3 1).add
      newCartanInput_cartanSkew031_differentiableAt

/-- The `023` coordinate of the authoritative global Cartan connection is
differentiable at the fixed origin. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_gravityConnection023_differentiableAt_origin :
    DifferentiableAt ℝ
      (fun point =>
        NewActual.gravityConnection point 0 2 3) 0 := by
  unfold NewActual fixedP506L0CompleteJointGlobalDevelopmentActual
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  change DifferentiableAt ℝ
    (fun point =>
      identityECSpinConnectionComponentOfCarrier 0 2 3
          (NewCartanInput.coframe point,
            (holonomicCoframeFirstJetAt NewCartanInput.coframe point
              ).derivative) +
        lorentzSkewConnectionOfBivectorOneForm
          (diracDualFormNativeActionCartanContorsionAt
            positiveSmoothUnifiedSource NewCartanInput point)
          0 2 3) 0
  exact
    (newCartanInput_leviCivitaComponent_differentiableAt 0 2 3).add
      newCartanInput_cartanSkew023_differentiableAt

/-- The authoritative source/current-only global development has vanishing
temporal-electric connection kernel at the origin. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_temporalElectricKernel_zero :
    gravityConnectionDerivative NewActual 0
          canonicalLorentzianTimeDirection 1 3 1 +
        gravityConnectionDerivative NewActual 0
          canonicalLorentzianTimeDirection 2 2 3 =
      0 := by
  rw [
    fixedP506L0CompleteJointGlobalDevelopmentActual_cartanConnection131_temporalDerivative_zero,
    fixedP506L0CompleteJointGlobalDevelopmentActual_cartanConnection223_temporalDerivative_zero]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel

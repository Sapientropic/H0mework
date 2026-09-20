import H0mework.Physics.FullOccurrence.FixedWholeResidualReduction
import H0mework.Physics.JointVariation.P286CanonicalOccurrenceWriteProfile

/-!
# U6 writer pre-EC congruence

The pre-EC complete-joint live-electric development sees no primitive
difference between the fixed `U5` input and its full-occurrence diagonal
`U6`.  The proof follows the source/action-owned Cartan, temporal, P286,
constitutive, live-electric, and final Cartan legs.  It introduces no
successor and supplies no residual or zero-fiber premise.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWriterPreECCongruence

open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDiracDualFormNativeCompleteJointActionP286TemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineFormNativeP286RequiredExteriorActionDataCongruence
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineHolonomicGaugeCurvatureTransport
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private theorem u6_coframe_eq_u5 : U6.coframe = U5.coframe :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
    Source U5

private theorem u6_gaugeConnection_eq_u5 :
    U6.gaugeConnection = U5.gaugeConnection :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current

private theorem u6_scalar_eq_u5 : U6.scalar = U5.scalar :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
    Source U5

private theorem u6_matter_eq_u5 : U6.matter = U5.matter :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
    Source U5

private theorem u6_conjugateMatter_eq_u5 :
    U6.conjugateMatter = U5.conjugateMatter :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
    Source U5

private abbrev Recenter6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration U6 contact

private abbrev Recenter5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration U5 contact

private theorem recentered_coframe_eq (contact : BasePoint) :
    (Recenter6 contact).coframe = (Recenter5 contact).coframe := by
  unfold Recenter6 Recenter5 fullyRecenterHolonomicConfiguration
  rw [u6_coframe_eq_u5]

private theorem recentered_gaugeConnection_eq (contact : BasePoint) :
    (Recenter6 contact).gaugeConnection =
      (Recenter5 contact).gaugeConnection := by
  unfold Recenter6 Recenter5 fullyRecenterHolonomicConfiguration
  rw [u6_gaugeConnection_eq_u5]

private theorem recentered_scalar_eq (contact : BasePoint) :
    (Recenter6 contact).scalar = (Recenter5 contact).scalar := by
  unfold Recenter6 Recenter5 fullyRecenterHolonomicConfiguration
  rw [u6_scalar_eq_u5]

private theorem recentered_matter_eq (contact : BasePoint) :
    (Recenter6 contact).matter = (Recenter5 contact).matter := by
  unfold Recenter6 Recenter5 fullyRecenterHolonomicConfiguration
  rw [u6_matter_eq_u5]

private theorem recentered_conjugateMatter_eq (contact : BasePoint) :
    (Recenter6 contact).conjugateMatter =
      (Recenter5 contact).conjugateMatter := by
  unfold Recenter6 Recenter5 fullyRecenterHolonomicConfiguration
  rw [u6_conjugateMatter_eq_u5]

private theorem actionCartanConnectionAt_eq_of_coreFields
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : first.coframe = second.coframe)
    (matterEq : first.matter point = second.matter point)
    (conjugateEq :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt source first point =
      diracDualFormNativeActionCartanConnectionAt source second point := by
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      source first second point (congrFun coframeEq point)
      matterEq conjugateEq
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeEq, spinEq]

private abbrev Restart6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    Source (Recenter6 contact)

private abbrev Restart5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    Source (Recenter5 contact)

private theorem restart_coframe_eq (contact : BasePoint) :
    (Restart6 contact).coframe = (Restart5 contact).coframe := by
  exact recentered_coframe_eq contact

private theorem restart_gravityConnection_eq (contact : BasePoint) :
    (Restart6 contact).gravityConnection =
      (Restart5 contact).gravityConnection := by
  funext point
  exact actionCartanConnectionAt_eq_of_coreFields
    Source (Recenter6 contact) (Recenter5 contact) point
    (recentered_coframe_eq contact)
    (congrFun (recentered_matter_eq contact) point)
    (congrFun (recentered_conjugateMatter_eq contact) point)

private theorem restart_gravityAuxiliary_eq (contact : BasePoint) :
    (Restart6 contact).gravityAuxiliary =
      (Restart5 contact).gravityAuxiliary := by
  funext point
  exact congrArg physicalIIPlusBivector
    (congrFun (recentered_coframe_eq contact) point)

private theorem restart_gaugeConnection_eq (contact : BasePoint) :
    (Restart6 contact).gaugeConnection =
      (Restart5 contact).gaugeConnection := by
  exact recentered_gaugeConnection_eq contact

private theorem restart_scalar_eq (contact : BasePoint) :
    (Restart6 contact).scalar = (Restart5 contact).scalar := by
  exact recentered_scalar_eq contact

private theorem restart_matter_eq (contact : BasePoint) :
    (Restart6 contact).matter = (Restart5 contact).matter := by
  exact recentered_matter_eq contact

private theorem restart_conjugateMatter_eq (contact : BasePoint) :
    (Restart6 contact).conjugateMatter =
      (Restart5 contact).conjugateMatter := by
  exact recentered_conjugateMatter_eq contact

private theorem holonomicGravityCurvature_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gravityConnection = second.gravityConnection)
    (point : BasePoint) :
    holonomicGravityCurvature first point =
      holonomicGravityCurvature second point := by
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [connectionEq]

private theorem restart_gravitySimplicityMultiplier_eq
    (contact : BasePoint) :
    (Restart6 contact).gravitySimplicityMultiplier =
      (Restart5 contact).gravitySimplicityMultiplier := by
  calc
    (Restart6 contact).gravitySimplicityMultiplier =
        formNativeGravityReactionField (Restart6 contact) :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        Source (Recenter6 contact)
    _ = formNativeGravityReactionField (Restart5 contact) := by
      funext point
      unfold formNativeGravityReactionField
        holonomicContravariantGravityCurvature
      rw [congrFun (restart_gravityAuxiliary_eq contact) point,
        holonomicGravityCurvature_eq_of_connection_eq
          (Restart6 contact) (Restart5 contact)
          (restart_gravityConnection_eq contact) point]
    _ = (Restart5 contact).gravitySimplicityMultiplier :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        Source (Recenter5 contact)).symm

private abbrev ProfileRestart6 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source (Recenter6 contact) point

private abbrev ProfileRestart5 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source (Recenter5 contact) point

private theorem profileRestart_eq_restart6 (contact point : BasePoint) :
    ProfileRestart6 contact point =
      Restart6 (canonicalSpacetimeContactTranslation contact point) := by
  unfold ProfileRestart6 completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_recenter]

private theorem profileRestart_eq_restart5 (contact point : BasePoint) :
    ProfileRestart5 contact point =
      Restart5 (canonicalSpacetimeContactTranslation contact point) := by
  unfold ProfileRestart5 completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_recenter]

private theorem profileRestart_coframe_eq (contact point : BasePoint) :
    (ProfileRestart6 contact point).coframe =
      (ProfileRestart5 contact point).coframe := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_coframe_eq _

private theorem profileRestart_gravityConnection_eq
    (contact point : BasePoint) :
    (ProfileRestart6 contact point).gravityConnection =
      (ProfileRestart5 contact point).gravityConnection := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_gravityConnection_eq _

private theorem profileRestart_gravityAuxiliary_eq
    (contact point : BasePoint) :
    (ProfileRestart6 contact point).gravityAuxiliary =
      (ProfileRestart5 contact point).gravityAuxiliary := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_gravityAuxiliary_eq _

private theorem profileRestart_gravitySimplicityMultiplier_eq
    (contact point : BasePoint) :
    (ProfileRestart6 contact point).gravitySimplicityMultiplier =
      (ProfileRestart5 contact point).gravitySimplicityMultiplier := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_gravitySimplicityMultiplier_eq _

private theorem profileRestart_gaugeConnection_eq
    (contact point : BasePoint) :
    (ProfileRestart6 contact point).gaugeConnection =
      (ProfileRestart5 contact point).gaugeConnection := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_gaugeConnection_eq _

private theorem profileRestart_scalar_eq (contact point : BasePoint) :
    (ProfileRestart6 contact point).scalar =
      (ProfileRestart5 contact point).scalar := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_scalar_eq _

private theorem profileRestart_matter_eq (contact point : BasePoint) :
    (ProfileRestart6 contact point).matter =
      (ProfileRestart5 contact point).matter := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_matter_eq _

private theorem profileRestart_conjugateMatter_eq
    (contact point : BasePoint) :
    (ProfileRestart6 contact point).conjugateMatter =
      (ProfileRestart5 contact point).conjugateMatter := by
  rw [profileRestart_eq_restart6, profileRestart_eq_restart5]
  exact restart_conjugateMatter_eq _

private theorem generatedProfiles_matterVelocity_eq
    (contact point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      Source (Recenter6 contact) point).matterVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source (Recenter5 contact) point).matterVelocity := by
  change
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (ProfileRestart6 contact point) 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (ProfileRestart5 contact point) 0
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterCovariantDerivative holonomicMatterConnectionAction
  rw [profileRestart_coframe_eq contact point,
    profileRestart_gravityConnection_eq contact point,
    profileRestart_gaugeConnection_eq contact point,
    profileRestart_scalar_eq contact point,
    profileRestart_matter_eq contact point]

private theorem matterResponseWrite_eq (contact point : BasePoint) :
    diracDualCurrentCoframeMatterTimeResponseWrite
        (ProfileRestart6 contact point) =
      diracDualCurrentCoframeMatterTimeResponseWrite
        (ProfileRestart5 contact point) := by
  unfold diracDualCurrentCoframeMatterTimeResponseWrite
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
    holonomicDiracDualCurrentCoframeMatterKnownVector
    holonomicMatterCovariantDerivative
  rw [profileRestart_coframe_eq contact point,
    profileRestart_gravityConnection_eq contact point,
    profileRestart_gaugeConnection_eq contact point,
    profileRestart_scalar_eq contact point,
    profileRestart_matter_eq contact point]

private abbrev MatterResponse6 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (ProfileRestart6 contact point)

private abbrev MatterResponse5 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    (ProfileRestart5 contact point)

private theorem matterResponse_coframe_eq (contact point : BasePoint) :
    (MatterResponse6 contact point).coframe =
      (MatterResponse5 contact point).coframe := by
  exact profileRestart_coframe_eq contact point

private theorem matterResponse_gravityConnection_eq
    (contact point : BasePoint) :
    (MatterResponse6 contact point).gravityConnection =
      (MatterResponse5 contact point).gravityConnection := by
  exact profileRestart_gravityConnection_eq contact point

private theorem matterResponse_gaugeConnection_eq
    (contact point : BasePoint) :
    (MatterResponse6 contact point).gaugeConnection =
      (MatterResponse5 contact point).gaugeConnection := by
  exact profileRestart_gaugeConnection_eq contact point

private theorem matterResponse_scalar_eq (contact point : BasePoint) :
    (MatterResponse6 contact point).scalar =
      (MatterResponse5 contact point).scalar := by
  exact profileRestart_scalar_eq contact point

private theorem matterResponse_conjugateMatter_eq
    (contact point : BasePoint) :
    (MatterResponse6 contact point).conjugateMatter =
      (MatterResponse5 contact point).conjugateMatter := by
  exact profileRestart_conjugateMatter_eq contact point

private theorem matterResponse_matter_eq (contact point : BasePoint) :
    (MatterResponse6 contact point).matter =
      (MatterResponse5 contact point).matter := by
  funext localPoint
  unfold MatterResponse6 MatterResponse5
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
    installMatterLinearTimeResponse varyMatterCoordinates
  rw [profileRestart_matter_eq contact point,
    matterResponseWrite_eq contact point]

private theorem matterResponse_conjugateDerivative_eq
    (contact point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicConjugateMatterDerivativeDual
        (MatterResponse6 contact point) 0 direction =
      holonomicConjugateMatterDerivativeDual
        (MatterResponse5 contact point) 0 direction := by
  have coordinatesEq :
      holonomicConjugateMatterCoordinates
          (MatterResponse6 contact point) =
        holonomicConjugateMatterCoordinates
          (MatterResponse5 contact point) := by
    unfold holonomicConjugateMatterCoordinates
    rw [matterResponse_conjugateMatter_eq contact point]
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
  rw [coordinatesEq]

private theorem generatedProfiles_adjointVelocity_eq
    (contact point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      Source (Recenter6 contact) point).adjointVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source (Recenter5 contact) point).adjointVelocity := by
  have responseEq :
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (MatterResponse6 contact point) 0 =
        holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
          (MatterResponse5 contact point) 0 := by
    apply
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
    · rw [matterResponse_coframe_eq contact point]
    · exact congrFun (matterResponse_gravityConnection_eq contact point) 0
    · exact congrFun (matterResponse_gaugeConnection_eq contact point) 0
    · exact congrFun (matterResponse_scalar_eq contact point) 0
    · exact congrFun (matterResponse_conjugateMatter_eq contact point) 0
    · exact matterResponse_conjugateDerivative_eq contact point
  simpa only [
    sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
    using responseEq

private theorem matterResponse_liveAdjointVelocity_eq
    (contact point : BasePoint) :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (MatterResponse6 contact point) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (MatterResponse5 contact point) 0 := by
  simpa only [
    sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
    using generatedProfiles_adjointVelocity_eq contact point

private theorem liveAdjointResponseWrite_eq (contact point : BasePoint) :
    liveCoframeConjugateMatterTimeResponseWrite
        (MatterResponse6 contact point) =
      liveCoframeConjugateMatterTimeResponseWrite
        (MatterResponse5 contact point) := by
  unfold liveCoframeConjugateMatterTimeResponseWrite
  rw [matterResponse_liveAdjointVelocity_eq contact point,
    matterResponse_conjugateDerivative_eq contact point]

private abbrev JointMatterResponse6 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualRepairedMatterJointResponseActual
    (ProfileRestart6 contact point)

private abbrev JointMatterResponse5 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualRepairedMatterJointResponseActual
    (ProfileRestart5 contact point)

private theorem jointMatterResponse_coframe_eq (contact point : BasePoint) :
    (JointMatterResponse6 contact point).coframe =
      (JointMatterResponse5 contact point).coframe := by
  exact matterResponse_coframe_eq contact point

private theorem jointMatterResponse_gravityConnection_eq
    (contact point : BasePoint) :
    (JointMatterResponse6 contact point).gravityConnection =
      (JointMatterResponse5 contact point).gravityConnection := by
  exact matterResponse_gravityConnection_eq contact point

private theorem jointMatterResponse_gravityAuxiliary_eq
    (contact point : BasePoint) :
    (JointMatterResponse6 contact point).gravityAuxiliary =
      (JointMatterResponse5 contact point).gravityAuxiliary := by
  exact profileRestart_gravityAuxiliary_eq contact point

private theorem jointMatterResponse_gravitySimplicityMultiplier_eq
    (contact point : BasePoint) :
    (JointMatterResponse6 contact point).gravitySimplicityMultiplier =
      (JointMatterResponse5 contact point).gravitySimplicityMultiplier := by
  exact profileRestart_gravitySimplicityMultiplier_eq contact point

private theorem jointMatterResponse_gaugeConnection_eq
    (contact point : BasePoint) :
    (JointMatterResponse6 contact point).gaugeConnection =
      (JointMatterResponse5 contact point).gaugeConnection := by
  exact matterResponse_gaugeConnection_eq contact point

private theorem jointMatterResponse_scalar_eq (contact point : BasePoint) :
    (JointMatterResponse6 contact point).scalar =
      (JointMatterResponse5 contact point).scalar := by
  exact matterResponse_scalar_eq contact point

private theorem jointMatterResponse_matter_eq (contact point : BasePoint) :
    (JointMatterResponse6 contact point).matter =
      (JointMatterResponse5 contact point).matter := by
  exact matterResponse_matter_eq contact point

private theorem jointMatterResponse_conjugateMatter_eq
    (contact point : BasePoint) :
    (JointMatterResponse6 contact point).conjugateMatter =
      (JointMatterResponse5 contact point).conjugateMatter := by
  funext localPoint
  unfold JointMatterResponse6 JointMatterResponse5
    actionGeneratedDiracDualRepairedMatterJointResponseActual
    actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual
    installConjugateMatterLinearTimeResponse varyConjugateMatterCoordinates
  rw [matterResponse_conjugateMatter_eq contact point,
    liveAdjointResponseWrite_eq contact point]

private theorem profileRestart_constitutiveAuxiliary_eq
    (contact point : BasePoint) :
    diracDualFormNativeConstitutiveAuxiliaryField
        Source (ProfileRestart6 contact point) =
      diracDualFormNativeConstitutiveAuxiliaryField
        Source (ProfileRestart5 contact point) := by
  funext localPoint
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [congrFun (profileRestart_coframe_eq contact point) localPoint,
    holonomicGaugeCurvature_eq_of_connection_eq
      (ProfileRestart6 contact point) (ProfileRestart5 contact point)
      (profileRestart_gaugeConnection_eq contact point) localPoint]

private abbrev Repaired6 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointRepairedConstitutiveCurrent
    Source (ProfileRestart6 contact point)

private abbrev Repaired5 (contact point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointRepairedConstitutiveCurrent
    Source (ProfileRestart5 contact point)

private theorem repaired_eq (contact point : BasePoint) :
    Repaired6 contact point = Repaired5 contact point := by
  apply StageNineHolonomicConfiguration.ext
  · exact jointMatterResponse_coframe_eq contact point
  · exact jointMatterResponse_gravityConnection_eq contact point
  · exact jointMatterResponse_gravityAuxiliary_eq contact point
  · exact jointMatterResponse_gravitySimplicityMultiplier_eq contact point
  · exact jointMatterResponse_gaugeConnection_eq contact point
  · exact profileRestart_constitutiveAuxiliary_eq contact point
  · exact jointMatterResponse_scalar_eq contact point
  · exact jointMatterResponse_matter_eq contact point
  · exact jointMatterResponse_conjugateMatter_eq contact point

private theorem generatedProfiles_scalarAcceleration_eq
    (contact point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      Source (Recenter6 contact) point).scalarAcceleration =
      (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source (Recenter5 contact) point).scalarAcceleration := by
  have accelerationEq := congrArg
    (genericDiracDualScalarGeneratedAcceleration Source)
    (repaired_eq contact point)
  simpa only [
    sourceActionGeneratedDiracDualCompleteJointProfiles_scalarAcceleration]
    using accelerationEq

private theorem matterTemporalCorrection_eq (contact : BasePoint) :
    completeJointMatterTemporalCoordinateCorrection
        Source (Recenter6 contact) =
      completeJointMatterTemporalCoordinateCorrection
        Source (Recenter5 contact) := by
  funext point
  unfold completeJointMatterTemporalCoordinateCorrection
  rw [generatedProfiles_matterVelocity_eq contact point,
    recentered_matter_eq contact]

private theorem adjointTemporalCorrection_eq (contact : BasePoint) :
    completeJointAdjointTemporalCoordinateCorrection
        Source (Recenter6 contact) =
      completeJointAdjointTemporalCoordinateCorrection
        Source (Recenter5 contact) := by
  funext point
  unfold completeJointAdjointTemporalCoordinateCorrection
    holonomicConjugateMatterCoordinates
  rw [generatedProfiles_adjointVelocity_eq contact point,
    recentered_conjugateMatter_eq contact]

private theorem scalarAccelerationProfile_eq (contact : BasePoint) :
    completeJointScalarAccelerationProfile Source (Recenter6 contact) =
      completeJointScalarAccelerationProfile Source (Recenter5 contact) := by
  funext point
  exact generatedProfiles_scalarAcceleration_eq contact point

private abbrev Temporal6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (Recenter6 contact)

private abbrev Temporal5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source (Recenter5 contact)

private theorem temporal_coframe_eq (contact : BasePoint) :
    (Temporal6 contact).coframe = (Temporal5 contact).coframe := by
  exact recentered_coframe_eq contact

private theorem temporal_gaugeConnection_eq (contact : BasePoint) :
    (Temporal6 contact).gaugeConnection =
      (Temporal5 contact).gaugeConnection := by
  exact recentered_gaugeConnection_eq contact

private theorem temporal_scalar_eq (contact : BasePoint) :
    (Temporal6 contact).scalar = (Temporal5 contact).scalar := by
  funext point
  unfold Temporal6 Temporal5 completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (Recenter6 contact).scalar point +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source (Recenter6 contact))
          point =
      (Recenter5 contact).scalar point +
        canonicalTimeSecondPrimitive
          (completeJointScalarAccelerationProfile Source (Recenter5 contact))
          point
  rw [congrFun (recentered_scalar_eq contact) point,
    scalarAccelerationProfile_eq contact]

private theorem temporal_matter_eq (contact : BasePoint) :
    (Temporal6 contact).matter = (Temporal5 contact).matter := by
  funext point
  unfold Temporal6 Temporal5 completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (Recenter6 contact).matter point +
        matterCoordinateEquiv.symm
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection
              Source (Recenter6 contact)) point) =
      (Recenter5 contact).matter point +
        matterCoordinateEquiv.symm
          (canonicalTimePrimitive
            (completeJointMatterTemporalCoordinateCorrection
              Source (Recenter5 contact)) point)
  rw [congrFun (recentered_matter_eq contact) point,
    matterTemporalCorrection_eq contact]

private theorem temporal_conjugateMatter_eq (contact : BasePoint) :
    (Temporal6 contact).conjugateMatter =
      (Temporal5 contact).conjugateMatter := by
  funext point
  unfold Temporal6 Temporal5 completeJointGlobalTemporalCurrent
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
  change
    (Recenter6 contact).conjugateMatter point +
        matterDualOfCoordinates
          (canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection
              Source (Recenter6 contact)) point) =
      (Recenter5 contact).conjugateMatter point +
        matterDualOfCoordinates
          (canonicalTimePrimitive
            (completeJointAdjointTemporalCoordinateCorrection
              Source (Recenter5 contact)) point)
  rw [congrFun (recentered_conjugateMatter_eq contact) point,
    adjointTemporalCorrection_eq contact]

private theorem temporal_scalarCovariantDerivative_eq
    (contact : BasePoint) :
    holonomicScalarCovariantDerivative (Temporal6 contact) 0 =
      holonomicScalarCovariantDerivative (Temporal5 contact) 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [temporal_scalar_eq contact, temporal_gaugeConnection_eq contact]

private abbrev P286Write6 (contact : BasePoint) : P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalGeneratedWrite Source (Temporal6 contact)

private abbrev P286Write5 (contact : BasePoint) : P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalGeneratedWrite Source (Temporal5 contact)

private theorem p286Write_eq (contact : BasePoint) :
    P286Write6 contact = P286Write5 contact := by
  apply diracDualFormNativeP286CanonicalGeneratedWrite_eq_of_actionData_eq
  · exact temporal_coframe_eq contact
  · exact temporal_gaugeConnection_eq contact
  · exact congrFun (temporal_scalar_eq contact) 0
  · exact temporal_scalarCovariantDerivative_eq contact
  · exact congrFun (temporal_matter_eq contact) 0
  · exact congrFun (temporal_conjugateMatter_eq contact) 0

/-- The authoritative occurrence P286 write generated from `U6` is exactly
the one generated from `U5` at every contact.  This is an action-data
congruence theorem; it consumes no residual coordinate or zero receipt. -/
theorem fixedP506L0_U6_U5_completeJointP286OccurrenceWriteProfile_eq
    (contact : BasePoint) :
    completeJointP286CanonicalOccurrenceWriteProfile
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
        contact =
      completeJointP286CanonicalOccurrenceWriteProfile
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
        contact := by
  change P286Write6 contact = P286Write5 contact
  exact p286Write_eq contact

/-- Consequently `U6` and `U5` generate the same canonical occurrence
connection second jet at every contact. -/
theorem fixedP506L0_U6_U5_completeJointP286OccurrenceSecondJetProfile_eq
    (contact : BasePoint) :
    completeJointP286CanonicalOccurrenceSecondJetProfile
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual
        contact =
      completeJointP286CanonicalOccurrenceSecondJetProfile
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual
        contact := by
  unfold completeJointP286CanonicalOccurrenceSecondJetProfile
  rw [fixedP506L0_U6_U5_completeJointP286OccurrenceWriteProfile_eq contact]

private theorem canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gaugeConnection = second.gaugeConnection)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalConnectionCandidate first write
      ).gaugeConnection =
      (diracDualFormNativeP286CanonicalConnectionCandidate second write
        ).gaugeConnection := by
  funext point direction
  simp only [diracDualFormNativeP286CanonicalConnectionCandidate,
    installP286HolonomicConnectionSecondJet,
    varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]
  rw [connectionEq]

private abbrev P286Candidate6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (Temporal6 contact) (P286Write6 contact)

private abbrev P286Candidate5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (Temporal5 contact) (P286Write5 contact)

private theorem p286Candidate_gaugeConnection_eq (contact : BasePoint) :
    (P286Candidate6 contact).gaugeConnection =
      (P286Candidate5 contact).gaugeConnection := by
  unfold P286Candidate6 P286Candidate5
  rw [p286Write_eq contact]
  exact canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (Temporal6 contact) (Temporal5 contact)
    (temporal_gaugeConnection_eq contact) (P286Write5 contact)

private abbrev Algebraic6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source (Recenter6 contact)

private abbrev Algebraic5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source (Recenter5 contact)

private theorem algebraic_coframe_eq (contact : BasePoint) :
    (Algebraic6 contact).coframe = (Algebraic5 contact).coframe := by
  exact temporal_coframe_eq contact

private theorem algebraic_gaugeConnection_eq (contact : BasePoint) :
    (Algebraic6 contact).gaugeConnection =
      (Algebraic5 contact).gaugeConnection := by
  exact p286Candidate_gaugeConnection_eq contact

private theorem algebraic_gaugeAuxiliary_eq (contact : BasePoint) :
    (Algebraic6 contact).gaugeAuxiliary =
      (Algebraic5 contact).gaugeAuxiliary := by
  funext point
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        ((Temporal6 contact).coframe point)
        (holonomicGaugeCurvature (P286Candidate6 contact) point) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        ((Temporal5 contact).coframe point)
        (holonomicGaugeCurvature (P286Candidate5 contact) point)
  rw [congrFun (temporal_coframe_eq contact) point,
    holonomicGaugeCurvature_eq_of_connection_eq
      (P286Candidate6 contact) (P286Candidate5 contact)
      (p286Candidate_gaugeConnection_eq contact) point]

private theorem algebraic_scalar_eq (contact : BasePoint) :
    (Algebraic6 contact).scalar = (Algebraic5 contact).scalar := by
  exact temporal_scalar_eq contact

private theorem algebraic_matter_eq (contact : BasePoint) :
    (Algebraic6 contact).matter = (Algebraic5 contact).matter := by
  exact temporal_matter_eq contact

private theorem algebraic_conjugateMatter_eq (contact : BasePoint) :
    (Algebraic6 contact).conjugateMatter =
      (Algebraic5 contact).conjugateMatter := by
  exact temporal_conjugateMatter_eq contact

private theorem algebraic_scalarCovariantDerivative_eq
    (contact point : BasePoint) :
    holonomicScalarCovariantDerivative (Algebraic6 contact) point =
      holonomicScalarCovariantDerivative (Algebraic5 contact) point := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [algebraic_scalar_eq contact, algebraic_gaugeConnection_eq contact]

private theorem algebraic_pointwiseDirectRequiredExterior_eq
    (contact point : BasePoint) :
    pointwiseDirectP286RequiredExteriorDerivative
        Source (Algebraic6 contact) point =
      pointwiseDirectP286RequiredExteriorDerivative
        Source (Algebraic5 contact) point := by
  have chargedEq :=
    formNativeChargedGaugeThreeForm_eq_of_actionData_eq
      Source (Algebraic6 contact) (Algebraic5 contact) point
      (congrFun (algebraic_coframe_eq contact) point)
      (congrFun (algebraic_scalar_eq contact) point)
      (algebraic_scalarCovariantDerivative_eq contact point)
      (congrFun (algebraic_matter_eq contact) point)
      (congrFun (algebraic_conjugateMatter_eq contact) point)
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
  rw [chargedEq]
  unfold holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [algebraic_gaugeConnection_eq contact,
    algebraic_gaugeAuxiliary_eq contact]

private theorem algebraic_requiredExteriorProfile_eq
    (contact point : BasePoint) :
    completeJointP286RequiredExteriorProfile
        Source (Algebraic6 contact) point =
      completeJointP286RequiredExteriorProfile
        Source (Algebraic5 contact) point := by
  calc
    completeJointP286RequiredExteriorProfile
        Source (Algebraic6 contact) point =
        pointwiseDirectP286RequiredExteriorDerivative
          Source (Algebraic6 contact) point :=
      completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
        Source (Algebraic6 contact) point
        (completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
          Source (Recenter6 contact) point)
    _ = pointwiseDirectP286RequiredExteriorDerivative
          Source (Algebraic5 contact) point :=
      algebraic_pointwiseDirectRequiredExterior_eq contact point
    _ = completeJointP286RequiredExteriorProfile
          Source (Algebraic5 contact) point :=
      (completeJointP286RequiredExteriorProfile_eq_pointwiseDirect_of_constitutiveAt
        Source (Algebraic5 contact) point
        (completeJointGlobalP286AlgebraicCurrent_constitutiveAuxiliary
          Source (Recenter5 contact) point)).symm

private theorem algebraic_eq_readout6 (contact : BasePoint) :
    Algebraic6 contact =
      formNativeP286GaugeConstitutiveReadout Source
        (P286Candidate6 contact) :=
  rfl

private theorem algebraic_eq_readout5 (contact : BasePoint) :
    Algebraic5 contact =
      formNativeP286GaugeConstitutiveReadout Source
        (P286Candidate5 contact) :=
  rfl

private theorem algebraic_p286AuxiliaryProfile_eq
    (contact point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointProfiles
      Source (Algebraic6 contact) point).p286AuxiliaryOrigin =
      (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source (Algebraic5 contact) point).p286AuxiliaryOrigin := by
  have value6 :=
    completeJointP286FullOccurrenceGlobalActionJet_value_constitutiveReadout
      Source (P286Candidate6 contact) point
  have value5 :=
    completeJointP286FullOccurrenceGlobalActionJet_value_constitutiveReadout
      Source (P286Candidate5 contact) point
  rw [algebraic_eq_readout6, algebraic_eq_readout5]
  calc
    (sourceActionGeneratedDiracDualCompleteJointProfiles
        Source
          (formNativeP286GaugeConstitutiveReadout Source
            (P286Candidate6 contact)) point).p286AuxiliaryOrigin =
        holonomicP286GaugeAuxiliaryCoordinate
          (formNativeP286GaugeConstitutiveReadout Source
            (P286Candidate6 contact)) point := by
      simpa only [completeJointP286FullOccurrenceGlobalActionJet] using value6
    _ = holonomicP286GaugeAuxiliaryCoordinate
          (formNativeP286GaugeConstitutiveReadout Source
            (P286Candidate5 contact)) point := by
      unfold holonomicP286GaugeAuxiliaryCoordinate
      rw [← algebraic_eq_readout6 contact, ← algebraic_eq_readout5 contact,
        algebraic_gaugeAuxiliary_eq contact]
    _ = (sourceActionGeneratedDiracDualCompleteJointProfiles
          Source
            (formNativeP286GaugeConstitutiveReadout Source
              (P286Candidate5 contact)) point).p286AuxiliaryOrigin := by
      simpa only [completeJointP286FullOccurrenceGlobalActionJet] using
        value5.symm

private theorem algebraic_zeroSliceAnchor_eq (contact : BasePoint) :
    completeJointP286ZeroSliceAnchor Source (Algebraic6 contact) =
      completeJointP286ZeroSliceAnchor Source (Algebraic5 contact) := by
  funext space
  exact algebraic_p286AuxiliaryProfile_eq contact
    (canonicalCauchySlicePoint 0 space)

private theorem liveBaseCoordinate_eq (contact : BasePoint) :
    completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
        Source (Algebraic6 contact) =
      completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
        Source (Algebraic5 contact) := by
  funext point
  unfold completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [algebraic_gaugeAuxiliary_eq contact,
    algebraic_zeroSliceAnchor_eq contact]

private abbrev LiveBase6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointP286LiveElectricZeroSliceMagneticBase
    Source (Algebraic6 contact)

private abbrev LiveBase5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointP286LiveElectricZeroSliceMagneticBase
    Source (Algebraic5 contact)

private theorem liveBase_gaugeAuxiliary_eq (contact : BasePoint) :
    (LiveBase6 contact).gaugeAuxiliary =
      (LiveBase5 contact).gaugeAuxiliary := by
  funext point pair
  unfold LiveBase6 LiveBase5
    completeJointP286LiveElectricZeroSliceMagneticBase
  rw [liveBaseCoordinate_eq contact]

private theorem gaugeAuxiliaryExteriorDerivative_eq_of_auxiliary_eq
    (first second : StageNineHolonomicConfiguration)
    (auxiliaryEq : first.gaugeAuxiliary = second.gaugeAuxiliary)
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative first point =
      holonomicP286GaugeAuxiliaryExteriorDerivative second point := by
  have coordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate first =
        holonomicP286GaugeAuxiliaryCoordinate second := by
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [auxiliaryEq]
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    p286GaugeAuxiliaryDirectionalDerivative
  rw [coordinateEq]

private theorem liveActionTemporalWriteProfile_eq (contact : BasePoint) :
    completeJointP286LiveElectricActionTemporalWriteProfile
        Source (Algebraic6 contact) =
      completeJointP286LiveElectricActionTemporalWriteProfile
        Source (Algebraic5 contact) := by
  funext point
  unfold completeJointP286LiveElectricActionTemporalWriteProfile
  rw [algebraic_requiredExteriorProfile_eq contact point,
    gaugeAuxiliaryExteriorDerivative_eq_of_auxiliary_eq
      (LiveBase6 contact) (LiveBase5 contact)
      (liveBase_gaugeAuxiliary_eq contact) point]

private theorem liveActionTemporalWritePrimitive_eq (contact : BasePoint) :
    completeJointP286LiveElectricActionTemporalWritePrimitive
        Source (Algebraic6 contact) =
      completeJointP286LiveElectricActionTemporalWritePrimitive
        Source (Algebraic5 contact) := by
  funext point pair
  unfold completeJointP286LiveElectricActionTemporalWritePrimitive
  rw [liveActionTemporalWriteProfile_eq contact]

private abbrev LiveP2866 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current Source (Recenter6 contact)

private abbrev LiveP2865 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current Source (Recenter5 contact)

private theorem liveP286_coframe_eq (contact : BasePoint) :
    (LiveP2866 contact).coframe = (LiveP2865 contact).coframe := by
  exact algebraic_coframe_eq contact

private theorem liveP286_gaugeConnection_eq (contact : BasePoint) :
    (LiveP2866 contact).gaugeConnection =
      (LiveP2865 contact).gaugeConnection := by
  exact algebraic_gaugeConnection_eq contact

private theorem liveP286_gaugeAuxiliary_eq (contact : BasePoint) :
    (LiveP2866 contact).gaugeAuxiliary =
      (LiveP2865 contact).gaugeAuxiliary := by
  funext point pair
  unfold LiveP2866 LiveP2865 completeJointLiveElectricGlobalP286Current
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
  change
    p286CoordinateEquiv.symm
        (completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
            Source (Algebraic6 contact) point pair +
          completeJointP286LiveElectricActionTemporalWritePrimitive
            Source (Algebraic6 contact) point pair) =
      p286CoordinateEquiv.symm
        (completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
            Source (Algebraic5 contact) point pair +
          completeJointP286LiveElectricActionTemporalWritePrimitive
            Source (Algebraic5 contact) point pair)
  rw [liveBaseCoordinate_eq contact,
    liveActionTemporalWritePrimitive_eq contact]

private theorem liveP286_scalar_eq (contact : BasePoint) :
    (LiveP2866 contact).scalar = (LiveP2865 contact).scalar := by
  exact algebraic_scalar_eq contact

private theorem liveP286_matter_eq (contact : BasePoint) :
    (LiveP2866 contact).matter = (LiveP2865 contact).matter := by
  exact algebraic_matter_eq contact

private theorem liveP286_conjugateMatter_eq (contact : BasePoint) :
    (LiveP2866 contact).conjugateMatter =
      (LiveP2865 contact).conjugateMatter := by
  exact algebraic_conjugateMatter_eq contact

private abbrev PreEC6 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    Source (Recenter6 contact)

private abbrev PreEC5 (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    Source (Recenter5 contact)

private theorem preEC_coframe_eq (contact : BasePoint) :
    (PreEC6 contact).coframe = (PreEC5 contact).coframe := by
  exact liveP286_coframe_eq contact

private theorem preEC_gravityConnection_eq (contact : BasePoint) :
    (PreEC6 contact).gravityConnection =
      (PreEC5 contact).gravityConnection := by
  funext point
  exact actionCartanConnectionAt_eq_of_coreFields
    Source (LiveP2866 contact) (LiveP2865 contact) point
    (liveP286_coframe_eq contact)
    (congrFun (liveP286_matter_eq contact) point)
    (congrFun (liveP286_conjugateMatter_eq contact) point)

private theorem preEC_gravityAuxiliary_eq (contact : BasePoint) :
    (PreEC6 contact).gravityAuxiliary =
      (PreEC5 contact).gravityAuxiliary := by
  funext point
  exact congrArg physicalIIPlusBivector
    (congrFun (liveP286_coframe_eq contact) point)

private theorem preEC_gravitySimplicityMultiplier_eq
    (contact : BasePoint) :
    (PreEC6 contact).gravitySimplicityMultiplier =
      (PreEC5 contact).gravitySimplicityMultiplier := by
  calc
    (PreEC6 contact).gravitySimplicityMultiplier =
        formNativeGravityReactionField (PreEC6 contact) :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        Source (LiveP2866 contact)
    _ = formNativeGravityReactionField (PreEC5 contact) := by
      funext point
      unfold formNativeGravityReactionField
        holonomicContravariantGravityCurvature
      rw [congrFun (preEC_gravityAuxiliary_eq contact) point,
        holonomicGravityCurvature_eq_of_connection_eq
          (PreEC6 contact) (PreEC5 contact)
          (preEC_gravityConnection_eq contact) point]
    _ = (PreEC5 contact).gravitySimplicityMultiplier :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        Source (LiveP2865 contact)).symm

private theorem preEC_gaugeConnection_eq (contact : BasePoint) :
    (PreEC6 contact).gaugeConnection =
      (PreEC5 contact).gaugeConnection := by
  exact liveP286_gaugeConnection_eq contact

private theorem preEC_gaugeAuxiliary_eq (contact : BasePoint) :
    (PreEC6 contact).gaugeAuxiliary =
      (PreEC5 contact).gaugeAuxiliary := by
  exact liveP286_gaugeAuxiliary_eq contact

private theorem preEC_scalar_eq (contact : BasePoint) :
    (PreEC6 contact).scalar = (PreEC5 contact).scalar := by
  exact liveP286_scalar_eq contact

private theorem preEC_matter_eq (contact : BasePoint) :
    (PreEC6 contact).matter = (PreEC5 contact).matter := by
  exact liveP286_matter_eq contact

private theorem preEC_conjugateMatter_eq (contact : BasePoint) :
    (PreEC6 contact).conjugateMatter =
      (PreEC5 contact).conjugateMatter := by
  exact liveP286_conjugateMatter_eq contact

/-- The fixed P506/L0 pre-EC live-electric development is insensitive to the
full-occurrence rewrite once the five retained primitive whole fields are
identified. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentOperator_recentered_U6_eq_U5
    (contact : BasePoint) :
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration U6 contact) =
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration U5 contact) := by
  apply StageNineHolonomicConfiguration.ext
  · exact preEC_coframe_eq contact
  · exact preEC_gravityConnection_eq contact
  · exact preEC_gravityAuxiliary_eq contact
  · exact preEC_gravitySimplicityMultiplier_eq contact
  · exact preEC_gaugeConnection_eq contact
  · exact preEC_gaugeAuxiliary_eq contact
  · exact preEC_scalar_eq contact
  · exact preEC_matter_eq contact
  · exact preEC_conjugateMatter_eq contact

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalWriterPreECCongruence

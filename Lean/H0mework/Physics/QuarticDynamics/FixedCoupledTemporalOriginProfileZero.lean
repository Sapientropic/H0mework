import H0mework.Physics.QuarticDynamics.FixedCoupledTemporalDevelopment
import H0mework.Physics.GlobalDevelopment.FixedTemporalElectricKernel

/-!
# Fixed P506/L0 coupled temporal origin profile zero

The source/current-only radial-plus-scalar-carry temporal producer recomputes
its primal and independent-adjoint action profiles at the common origin.  The
radial gauge field vanishes at that contact, while the scalar momentum carry
changes no point data read by either profile.  Their generated velocities are
therefore exactly the already proved fixed P506/L0 velocities, hence zero.

These are concrete producer/read-after-write profile theorems.  No residual,
support coordinate, target derivative, demand, successor, or equation receipt
is supplied to the producer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalOriginProfileZero

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506CartanRestartTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginAdjointDerivativeTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentTemporalElectricKernel
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalDevelopment
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit
open StageNineP286RadialQuarticActionPrincipal
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance coupledProfileP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance coupledProfileP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance coupledProfileP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev CurrentRestart : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source Current 0

private abbrev OldRestart : StageNineHolonomicConfiguration :=
  ProfileRestartActual

private abbrev OldGlobal : StageNineHolonomicConfiguration :=
  NewActual

private theorem current_coframe_eq_input :
    Current.coframe = FixedInput.coframe := by
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic]
  simp [completeJointGlobalP286AlgebraicCurrent,
    completeJointGlobalTemporalCurrent]

private theorem current_matter_eq_oldGlobal :
    Current.matter = OldGlobal.matter := by
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic,
    newActual_matter_eq_algebraic]

private theorem current_conjugateMatter_eq_oldGlobal :
    Current.conjugateMatter = OldGlobal.conjugateMatter := by
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic,
    newActual_conjugateMatter_eq_algebraic]

private theorem current_scalar_origin_eq_input :
    Current.scalar 0 = FixedInput.scalar 0 := by
  calc
    Current.scalar 0 = Algebraic.scalar 0 := by
      simpa only [canonicalCauchySlicePoint_zero_zero] using
        (fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
          0)
    _ = OldGlobal.scalar 0 := by
      rw [newActual_scalar_eq_algebraic]
    _ = FixedInput.scalar 0 := newActual_scalar_origin_eq_input

private theorem algebraic_gaugeConnection_eq_input :
    Algebraic.gaugeConnection = FixedInput.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source FixedInput) 0 by
    exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem current_gaugeConnection_origin_eq_input :
    Current.gaugeConnection 0 = FixedInput.gaugeConnection 0 := by
  funext direction
  rw [fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_normalForm,
    congrFun algebraic_gaugeConnection_eq_input 0]
  simp [p286RadialQuarticTemporalConnection,
    p286SpatialRadialQuarticCoefficient, p286SpatialRadiusSquared,
    p286SpatialMetricCovectorOperator]

private theorem current_matter_origin_eq_input :
    Current.matter 0 = FixedInput.matter 0 := by
  rw [congrFun current_matter_eq_oldGlobal 0,
    newActual_matter_origin_eq_input]

private theorem current_conjugateMatter_origin_eq_input :
    Current.conjugateMatter 0 = FixedInput.conjugateMatter 0 := by
  rw [congrFun current_conjugateMatter_eq_oldGlobal 0,
    newActual_conjugateMatter_origin_eq_input]

private theorem currentRestart_coframe_eq_oldRestart :
    CurrentRestart.coframe = OldRestart.coframe := by
  unfold CurrentRestart OldRestart ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero,
    current_coframe_eq_input]

private theorem currentRestart_scalar_origin_eq_oldRestart :
    CurrentRestart.scalar 0 = OldRestart.scalar 0 := by
  unfold CurrentRestart OldRestart ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    fullyRecenterHolonomicConfiguration_scalar_origin,
    current_scalar_origin_eq_input]

private theorem currentRestart_matter_eq_oldGlobal :
    CurrentRestart.matter = OldGlobal.matter := by
  unfold CurrentRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_zero,
    current_matter_eq_oldGlobal]

private theorem currentRestart_conjugateMatter_eq_oldGlobal :
    CurrentRestart.conjugateMatter = OldGlobal.conjugateMatter := by
  unfold CurrentRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_zero,
    current_conjugateMatter_eq_oldGlobal]

private theorem currentRestart_gaugeConnection_origin_eq_oldRestart :
    CurrentRestart.gaugeConnection 0 = OldRestart.gaugeConnection 0 := by
  unfold CurrentRestart OldRestart ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero,
    current_gaugeConnection_origin_eq_input]

private theorem currentRestart_gravityConnection_origin_eq_oldRestart :
    CurrentRestart.gravityConnection 0 = OldRestart.gravityConnection 0 := by
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at Source Current
      FixedInput 0 (congrFun current_coframe_eq_input 0)
      current_matter_origin_eq_input current_conjugateMatter_origin_eq_input
  unfold CurrentRestart OldRestart ProfileRestartActual
    completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero]
  change
    diracDualFormNativeActionCartanConnectionAt Source Current 0 =
      diracDualFormNativeActionCartanConnectionAt Source FixedInput 0
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [current_coframe_eq_input, spinEq]

private theorem currentRestart_matter_origin_eq_oldRestart :
    CurrentRestart.matter 0 = OldRestart.matter 0 := by
  rw [congrFun currentRestart_matter_eq_oldGlobal 0,
    newActual_matter_origin_eq_input,
    profileRestartActual_matter_origin_eq_input]

private theorem currentRestart_conjugateMatter_origin_eq_oldRestart :
    CurrentRestart.conjugateMatter 0 = OldRestart.conjugateMatter 0 := by
  rw [congrFun currentRestart_conjugateMatter_eq_oldGlobal 0,
    newActual_conjugateMatter_origin_eq_input,
    profileRestartActual_conjugateMatter_origin_eq_input]

private theorem currentRestart_gravityConnection_origin_eq_oldGlobal :
    CurrentRestart.gravityConnection 0 = OldGlobal.gravityConnection 0 :=
  currentRestart_gravityConnection_origin_eq_oldRestart.trans
    newActual_gravityConnection_origin_eq_profileRestart.symm

private theorem currentRestart_gaugeConnection_origin_eq_oldGlobal :
    CurrentRestart.gaugeConnection 0 = OldGlobal.gaugeConnection 0 :=
  currentRestart_gaugeConnection_origin_eq_oldRestart.trans
    newActual_gaugeConnection_origin_eq_profileRestart.symm

private theorem currentRestart_matterCovariantDerivative_spatial_eq_oldRestart
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative CurrentRestart 0 direction.succ =
      holonomicMatterCovariantDerivative OldRestart 0 direction.succ := by
  calc
    holonomicMatterCovariantDerivative CurrentRestart 0 direction.succ =
        holonomicMatterCovariantDerivative OldGlobal 0 direction.succ := by
      unfold holonomicMatterCovariantDerivative
      rw [currentRestart_matter_eq_oldGlobal,
        currentRestart_gravityConnection_origin_eq_oldGlobal,
        currentRestart_gaugeConnection_origin_eq_oldGlobal]
    _ = holonomicMatterCovariantDerivative OldRestart 0 direction.succ :=
      newActual_matterCovariantDerivative_spatial_origin direction

private theorem currentRestart_knownVector_eq_oldRestart :
    holonomicDiracDualCurrentCoframeMatterKnownVector CurrentRestart 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector OldRestart 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [congrFun currentRestart_coframe_eq_oldRestart 0,
    currentRestart_scalar_origin_eq_oldRestart,
    currentRestart_matter_origin_eq_oldRestart]
  simp_rw [currentRestart_matterCovariantDerivative_spatial_eq_oldRestart]

private theorem currentRestart_connectionAction_time_eq_oldRestart :
    holonomicMatterConnectionAction CurrentRestart 0
        canonicalLorentzianTimeDirection =
      holonomicMatterConnectionAction OldRestart 0
        canonicalLorentzianTimeDirection := by
  unfold holonomicMatterConnectionAction
  rw [currentRestart_gravityConnection_origin_eq_oldRestart,
    currentRestart_gaugeConnection_origin_eq_oldRestart,
    currentRestart_matter_origin_eq_oldRestart]

private theorem coupledProfile_matterVelocity_eq_fixedProfile :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).matterVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source FixedInput 0
        ).matterVelocity := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  change
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        CurrentRestart 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        OldRestart 0
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
  rw [congrFun currentRestart_coframe_eq_oldRestart 0,
    currentRestart_knownVector_eq_oldRestart,
    currentRestart_connectionAction_time_eq_oldRestart]

theorem fixedP506L0U6RadialQuarticCoupledTemporalProfile_matterVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).matterVelocity = 0 := by
  rw [coupledProfile_matterVelocity_eq_fixedProfile,
    fixedProfile_matterVelocity_zero]

theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_matterTemporalDerivative_origin_zero :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          (fixedP506L0U6RadialQuarticCoupledTemporalActual.matter point))
        0 canonicalLorentzianTimeDirection = 0 := by
  rw [fixedP506L0U6RadialQuarticCoupledTemporalActual_matterTemporalDerivative_origin,
    fixedP506L0U6RadialQuarticCoupledTemporalProfile_matterVelocity_zero]
  simp

private theorem currentRestart_coframe_eq_oldGlobal :
    CurrentRestart.coframe = OldGlobal.coframe :=
  currentRestart_coframe_eq_oldRestart.trans
    newActual_coframe_eq_profileRestart.symm

private theorem currentRestart_scalar_origin_eq_oldGlobal :
    CurrentRestart.scalar 0 = OldGlobal.scalar 0 := by
  calc
    CurrentRestart.scalar 0 = OldRestart.scalar 0 :=
      currentRestart_scalar_origin_eq_oldRestart
    _ = FixedInput.scalar 0 := profileRestartActual_scalar_origin_eq_input
    _ = OldGlobal.scalar 0 := newActual_scalar_origin_eq_input.symm

private theorem currentRestart_liveAdjointVelocity_eq_oldGlobal :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        CurrentRestart 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        OldGlobal 0 := by
  apply holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rw [currentRestart_coframe_eq_oldGlobal]
  · exact currentRestart_gravityConnection_origin_eq_oldGlobal
  · exact currentRestart_gaugeConnection_origin_eq_oldGlobal
  · exact currentRestart_scalar_origin_eq_oldGlobal
  · exact congrFun currentRestart_conjugateMatter_eq_oldGlobal 0
  · intro direction
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [currentRestart_conjugateMatter_eq_oldGlobal]

private theorem oldGlobal_coframe_origin_one :
    OldGlobal.coframe 0 = 1 := by
  rw [newActual_coframe_origin_eq_accepted]
  exact fixedP506L0FinalCommonActionActual_coframe_origin 0

private theorem oldGlobal_liveAdjointVelocity_zero :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        OldGlobal 0 = 0 := by
  have nondegenerate : Matrix.det (OldGlobal.coframe 0) ≠ 0 := by
    rw [oldGlobal_coframe_origin_one]
    norm_num
  have noncharacteristic :
      coframeTemporalPrincipalScalar (OldGlobal.coframe 0) ≠ 0 := by
    rw [oldGlobal_coframe_origin_one, coframeTemporalPrincipalScalar_one]
    norm_num
  have law :=
    fixedP506L0CompleteJointGlobalDevelopmentActual_liveAdjointActionLaw_origin
  rw [newActual_conjugateMatterTimeDerivative_origin_zero] at law
  exact
    (holonomicDiracDualLiveCoframeConjugateMatterTimeActionLaw_iff
      OldGlobal 0 nondegenerate noncharacteristic 0).mp law |>.symm

private theorem currentRestart_liveAdjointVelocity_zero :
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        CurrentRestart 0 = 0 := by
  rw [currentRestart_liveAdjointVelocity_eq_oldGlobal,
    oldGlobal_liveAdjointVelocity_zero]

private theorem coupledProfile_adjointVelocity_eq_currentRestart :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).adjointVelocity =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        CurrentRestart 0 := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
  change
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        (actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual
          CurrentRestart) 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity
        CurrentRestart 0
  apply holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_of_pointData
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro direction
    rfl

theorem fixedP506L0U6RadialQuarticCoupledTemporalProfile_adjointVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).adjointVelocity = 0 := by
  rw [coupledProfile_adjointVelocity_eq_currentRestart,
    currentRestart_liveAdjointVelocity_zero]

private theorem coupledProfile_adjointVelocity_eq_fixedProfile :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Current 0
        ).adjointVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source FixedInput 0
        ).adjointVelocity := by
  rw [fixedP506L0U6RadialQuarticCoupledTemporalProfile_adjointVelocity_zero,
    fixedProfile_adjointVelocity_zero]

theorem
    fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatterTemporalDerivative_origin_zero :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates
          fixedP506L0U6RadialQuarticCoupledTemporalActual)
        0 canonicalLorentzianTimeDirection = 0 := by
  rw [fixedP506L0U6RadialQuarticCoupledTemporalActual_conjugateMatterTemporalDerivative_origin,
    fixedP506L0U6RadialQuarticCoupledTemporalProfile_adjointVelocity_zero]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalOriginProfileZero

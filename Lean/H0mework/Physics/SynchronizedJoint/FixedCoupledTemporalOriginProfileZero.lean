import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessorP286Readback
import H0mework.Physics.QuarticDynamics.FixedCoupledTemporalOriginProfileZero

/-!
# Fixed P506/L0 action-selected coupled temporal origin profile zero

The action-selected carry and the earlier radial-quartic carry are generated
from the same fixed P506/L0 source lineage.  Their scalar and P286 connection
primitives agree globally, while their coframe and primal/adjoint matter data
agree on the canonical zero slice.  Direct differentiation of that slice and
the complete origin coframe jet therefore identify the two action-generated
Cartan profile restarts.

The already proved radial-quartic primal and independent-adjoint velocities
then transport to the action-selected carry and remain exactly zero.  This is
a fixed-lineage primitive/profile transporter and producer-soundness readout:
no residual, support coordinate, target derivative, closure receipt, demand,
or branch selector is supplied to either action profile constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedCoupledTemporalOriginProfileZero

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineConjugateMatterVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointGlobalDevelopmentOriginPrimalAdjointClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessorP286Readback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticCoupledTemporalOriginProfileZero
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286ActionCauchySplit

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev OldCarry : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source Input

private abbrev CarryRestart : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source Carry 0

private abbrev OldRestart : StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent Source OldCarry 0

private abbrev CarryPrimal : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual CarryRestart

private abbrev OldPrimal : StageNineHolonomicConfiguration :=
  actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual OldRestart

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem oldCarry_coframe_eq_fixedJoint :
    OldCarry.coframe = FixedP506JointActual.coframe := by
  calc
    OldCarry.coframe = Algebraic.coframe :=
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic
    _ = Input.coframe := by
      change
        (diracDualFormNativeP286CanonicalGeneratedActual Source
          (completeJointGlobalTemporalCurrent Source Input)).coframe =
          Input.coframe
      rw [diracDualFormNativeP286CanonicalGeneratedActual_coframe]
      unfold completeJointGlobalTemporalCurrent
      rw [
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_coframe]
    _ = FixedP506JointActual.coframe := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
        fixedP506JointActionSuccessor_coframe]

private theorem carry_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt Carry.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [actionSelectedCarry_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem oldCarry_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt OldCarry.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [oldCarry_coframe_eq_fixedJoint]
  apply coframeJet_eq_of_fields_eq
  · exact fixedP506JointActual_coframe_origin_one
  · funext derivativeDirection internal coordinate
    let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj coordinate :
          (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj internal :
          LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
    have evaluationDerivative :
        HasFDerivAt evaluation evaluation
          (FixedP506JointActual.coframe 0) :=
      evaluation.hasFDerivAt
    have evaluatedDerivative :=
      evaluationDerivative.comp (f := FixedP506JointActual.coframe)
        (0 : BasePoint)
        fixedP506JointActual_coframe_differentiableAt.hasFDerivAt
    have applied := congrArg
      (fun derivative : BasePoint →L[ℝ] ℝ =>
        derivative (coordinateDirection derivativeDirection))
      evaluatedDerivative.fderiv
    have evaluatedFunctionEquality :
        (fun point : BasePoint =>
          evaluation (FixedP506JointActual.coframe point)) =
        (fun point : BasePoint =>
          FixedP506JointActual.coframe point internal coordinate) := by
      funext point
      rfl
    have evaluatedCompositionEquality :
        (evaluation ∘ FixedP506JointActual.coframe) =
          (fun point : BasePoint =>
            FixedP506JointActual.coframe point internal coordinate) := by
      funext point
      rfl
    rw [evaluatedCompositionEquality] at applied
    change
      fderiv ℝ
          (fun point : BasePoint =>
            FixedP506JointActual.coframe point internal coordinate) 0
          (coordinateDirection derivativeDirection) = 0
    rw [applied]
    change
      evaluation
          ((fderiv ℝ FixedP506JointActual.coframe 0)
            (coordinateDirection derivativeDirection)) = 0
    rw [fixedP506JointActual_coframe_fderiv_coordinate_zero]
    exact map_zero evaluation

private theorem carry_core_origin :
    Carry.coframe 0 = OldCarry.coframe 0 ∧
      Carry.matter 0 = OldCarry.matter 0 ∧
      Carry.conjugateMatter 0 = OldCarry.conjugateMatter 0 := by
  simpa [canonicalCauchySlicePoint_zero_zero_local] using
    actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry
      (0 : StageNineSpatialPoint)

private theorem oldCarry_matter_eq_newActual :
    OldCarry.matter = NewActual.matter :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic.trans
    newActual_matter_eq_algebraic.symm

private theorem oldCarry_conjugateMatter_eq_newActual :
    OldCarry.conjugateMatter = NewActual.conjugateMatter :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic.trans
    newActual_conjugateMatter_eq_algebraic.symm

private theorem carry_matterCoordinates_spatialDerivative_eq_old
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point)) 0
        direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (OldCarry.matter point)) 0
        direction.succ := by
  let carryField : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (Carry.matter point)
  let oldField : BasePoint → MatterCoordinateCarrier :=
    fun point => matterCoordinateEquiv (OldCarry.matter point)
  have restrictedEq :
      carryField ∘ canonicalCauchySlicePoint 0 =
        oldField ∘ canonicalCauchySlicePoint 0 := by
    funext space
    unfold carryField oldField
    change
      matterCoordinateEquiv
          (Carry.matter (canonicalCauchySlicePoint 0 space)) =
        matterCoordinateEquiv
          (OldCarry.matter (canonicalCauchySlicePoint 0 space))
    rw [(actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry space).2.1]
  have carryDifferentiable : DifferentiableAt ℝ carryField 0 := by
    exact actionSelectedCarry_matterCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt
  have oldDifferentiable : DifferentiableAt ℝ oldField 0 := by
    unfold oldField
    rw [oldCarry_matter_eq_newActual]
    exact newActual_matterCoordinates_hasFDerivAt_origin.differentiableAt
  calc
    fieldDirectionalDerivative carryField 0 direction.succ =
        fderiv ℝ (carryField ∘ canonicalCauchySlicePoint 0) 0
          _ := by
      symm
      simpa [canonicalCauchySlicePoint_zero_zero_local] using
        fderiv_canonicalCauchySlicePoint_spatial_local carryField 0 0
          direction (by
            simpa [canonicalCauchySlicePoint_zero_zero_local] using
              carryDifferentiable)
    _ = fderiv ℝ (oldField ∘ canonicalCauchySlicePoint 0) 0 _ := by
      rw [restrictedEq]
    _ = fieldDirectionalDerivative oldField 0 direction.succ := by
      simpa [canonicalCauchySlicePoint_zero_zero_local] using
        fderiv_canonicalCauchySlicePoint_spatial_local oldField 0 0
          direction (by
            simpa [canonicalCauchySlicePoint_zero_zero_local] using
              oldDifferentiable)

/-- The action-selected carry retains the fixed P506/L0 primal spatial
first jet at the canonical origin.  This is the public field-level seam used
by downstream action-density transport. -/
theorem actionSelectedCarry_matterCoordinates_spatialDerivative_eq_u6RadialQuarticCarry
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (Carry.matter point)) 0
        direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (OldCarry.matter point)) 0
        direction.succ :=
  carry_matterCoordinates_spatialDerivative_eq_old direction

private theorem carry_conjugateMatterCoordinates_spatialDerivative_eq_old
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates Carry) 0 direction.succ =
      fieldDirectionalDerivative
        (holonomicConjugateMatterCoordinates OldCarry) 0 direction.succ := by
  let carryField : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates Carry
  let oldField : BasePoint → MatterCoordinateCarrier :=
    holonomicConjugateMatterCoordinates OldCarry
  have restrictedEq :
      carryField ∘ canonicalCauchySlicePoint 0 =
        oldField ∘ canonicalCauchySlicePoint 0 := by
    funext space
    unfold carryField oldField holonomicConjugateMatterCoordinates
    change
      matterDualCoordinates
          (Carry.conjugateMatter (canonicalCauchySlicePoint 0 space)) =
        matterDualCoordinates
          (OldCarry.conjugateMatter (canonicalCauchySlicePoint 0 space))
    rw [(actionSelectedCarry_zeroSlice_core_eq_u6RadialQuarticCarry space).2.2]
  have carryDifferentiable : DifferentiableAt ℝ carryField 0 := by
    exact actionSelectedCarry_conjugateMatterCoordinates_contDiff.differentiable
      (by simp) |>.differentiableAt
  have oldDifferentiable : DifferentiableAt ℝ oldField 0 := by
    unfold oldField holonomicConjugateMatterCoordinates
    rw [oldCarry_conjugateMatter_eq_newActual]
    exact newActual_conjugateMatterCoordinates_differentiableAt_origin
  calc
    fieldDirectionalDerivative carryField 0 direction.succ =
        fderiv ℝ (carryField ∘ canonicalCauchySlicePoint 0) 0
          _ := by
      symm
      simpa [canonicalCauchySlicePoint_zero_zero_local] using
        fderiv_canonicalCauchySlicePoint_spatial_local carryField 0 0
          direction (by
            simpa [canonicalCauchySlicePoint_zero_zero_local] using
              carryDifferentiable)
    _ = fderiv ℝ (oldField ∘ canonicalCauchySlicePoint 0) 0 _ := by
      rw [restrictedEq]
    _ = fieldDirectionalDerivative oldField 0 direction.succ := by
      simpa [canonicalCauchySlicePoint_zero_zero_local] using
        fderiv_canonicalCauchySlicePoint_spatial_local oldField 0 0
          direction (by
            simpa [canonicalCauchySlicePoint_zero_zero_local] using
              oldDifferentiable)

private theorem carryRestart_coframe_eq_carry :
    CarryRestart.coframe = Carry.coframe := by
  unfold CarryRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_zero]

private theorem oldRestart_coframe_eq_oldCarry :
    OldRestart.coframe = OldCarry.coframe := by
  unfold OldRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe,
    fullyRecenterHolonomicConfiguration_zero]

private theorem carryRestart_scalar_eq_carry :
    CarryRestart.scalar = Carry.scalar := by
  unfold CarryRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_zero]

private theorem oldRestart_scalar_eq_oldCarry :
    OldRestart.scalar = OldCarry.scalar := by
  unfold OldRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    fullyRecenterHolonomicConfiguration_zero]

private theorem carryRestart_matter_eq_carry :
    CarryRestart.matter = Carry.matter := by
  unfold CarryRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_zero]

private theorem oldRestart_matter_eq_oldCarry :
    OldRestart.matter = OldCarry.matter := by
  unfold OldRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
    fullyRecenterHolonomicConfiguration_zero]

private theorem carryRestart_conjugateMatter_eq_carry :
    CarryRestart.conjugateMatter = Carry.conjugateMatter := by
  unfold CarryRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_zero]

private theorem oldRestart_conjugateMatter_eq_oldCarry :
    OldRestart.conjugateMatter = OldCarry.conjugateMatter := by
  unfold OldRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
    fullyRecenterHolonomicConfiguration_zero]

private theorem carryRestart_gaugeConnection_eq_carry :
    CarryRestart.gaugeConnection = Carry.gaugeConnection := by
  unfold CarryRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_zero]

private theorem oldRestart_gaugeConnection_eq_oldCarry :
    OldRestart.gaugeConnection = OldCarry.gaugeConnection := by
  unfold OldRestart completeJointGeneratedProfileRestartCurrent
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection,
    fullyRecenterHolonomicConfiguration_zero]

private theorem carryRestart_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt CarryRestart.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [carryRestart_coframe_eq_carry]
  exact carry_coframeFirstJet_origin

private theorem oldRestart_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt OldRestart.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [oldRestart_coframe_eq_oldCarry]
  exact oldCarry_coframeFirstJet_origin

private theorem carryRestart_coframe_origin_eq_old :
    CarryRestart.coframe 0 = OldRestart.coframe 0 := by
  exact congrArg PointwiseLorentzianCoframeJet.coframe
    (carryRestart_coframeFirstJet_origin.trans
      oldRestart_coframeFirstJet_origin.symm)

private theorem carryRestart_scalar_origin_eq_old :
    CarryRestart.scalar 0 = OldRestart.scalar 0 := by
  rw [congrFun carryRestart_scalar_eq_carry 0,
    congrFun oldRestart_scalar_eq_oldCarry 0,
    congrFun actionSelectedCarry_scalar_eq_u6RadialQuarticCarry 0]

private theorem carryRestart_matter_origin_eq_old :
    CarryRestart.matter 0 = OldRestart.matter 0 := by
  rw [congrFun carryRestart_matter_eq_carry 0,
    congrFun oldRestart_matter_eq_oldCarry 0]
  exact carry_core_origin.2.1

private theorem carryRestart_conjugateMatter_origin_eq_old :
    CarryRestart.conjugateMatter 0 = OldRestart.conjugateMatter 0 := by
  rw [congrFun carryRestart_conjugateMatter_eq_carry 0,
    congrFun oldRestart_conjugateMatter_eq_oldCarry 0]
  exact carry_core_origin.2.2

private theorem carryRestart_gaugeConnection_origin_eq_old :
    CarryRestart.gaugeConnection 0 = OldRestart.gaugeConnection 0 := by
  rw [congrFun carryRestart_gaugeConnection_eq_carry 0,
    congrFun oldRestart_gaugeConnection_eq_oldCarry 0,
    congrFun actionSelectedCarry_gaugeConnection_eq_u6RadialQuarticCarry 0]

private theorem actionCartanConnectionAt_eq_of_jet_and_fields_at
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (jetEqual :
      holonomicCoframeFirstJetAt first.coframe point =
        holonomicCoframeFirstJetAt second.coframe point)
    (coframeEqual : first.coframe point = second.coframe point)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt Source first point =
      diracDualFormNativeActionCartanConnectionAt Source second point := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source first second point coframeEqual matterEqual conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEqual, coframeEqual, spinEqual]

private theorem carryRestart_gravityConnection_origin_eq_old :
    CarryRestart.gravityConnection 0 = OldRestart.gravityConnection 0 := by
  unfold CarryRestart OldRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero,
    fullyRecenterHolonomicConfiguration_zero]
  change
    diracDualFormNativeActionCartanConnectionAt Source Carry 0 =
      diracDualFormNativeActionCartanConnectionAt Source OldCarry 0
  apply actionCartanConnectionAt_eq_of_jet_and_fields_at
  · exact carry_coframeFirstJet_origin.trans
      oldCarry_coframeFirstJet_origin.symm
  · exact carry_core_origin.1
  · exact carry_core_origin.2.1
  · exact carry_core_origin.2.2

private theorem carryRestart_matterCovariantDerivative_spatial_eq_old
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative CarryRestart 0 direction.succ =
      holonomicMatterCovariantDerivative OldRestart 0 direction.succ := by
  unfold holonomicMatterCovariantDerivative
  rw [carryRestart_matter_eq_carry, oldRestart_matter_eq_oldCarry,
    carry_matterCoordinates_spatialDerivative_eq_old direction,
    carryRestart_gravityConnection_origin_eq_old,
    carryRestart_gaugeConnection_origin_eq_old,
    carry_core_origin.2.1]

private theorem carryRestart_knownVector_eq_old :
    holonomicDiracDualCurrentCoframeMatterKnownVector CarryRestart 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector OldRestart 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [carryRestart_coframe_origin_eq_old,
    carryRestart_scalar_origin_eq_old,
    carryRestart_matter_origin_eq_old]
  simp_rw [carryRestart_matterCovariantDerivative_spatial_eq_old]

private theorem carryRestart_connectionAction_time_eq_old :
    holonomicMatterConnectionAction CarryRestart 0
        canonicalLorentzianTimeDirection =
      holonomicMatterConnectionAction OldRestart 0
        canonicalLorentzianTimeDirection := by
  unfold holonomicMatterConnectionAction
  rw [carryRestart_gravityConnection_origin_eq_old,
    carryRestart_gaugeConnection_origin_eq_old,
    carryRestart_matter_origin_eq_old]

private theorem actionSelectedProfile_matterVelocity_eq_old :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry 0
      ).matterVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source OldCarry 0
      ).matterVelocity := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity]
  change
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        CarryRestart 0 =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        OldRestart 0
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
  rw [carryRestart_coframe_origin_eq_old,
    carryRestart_knownVector_eq_old,
    carryRestart_connectionAction_time_eq_old]

/-- The source/action-generated primal profile selected by the final carry has
zero origin velocity. -/
theorem fixedP506L0ActionSelectedCoupledTemporalProfile_matterVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry 0
      ).matterVelocity = 0 := by
  rw [actionSelectedProfile_matterVelocity_eq_old,
    fixedP506L0U6RadialQuarticCoupledTemporalProfile_matterVelocity_zero]

private theorem carryRestart_conjugateMatterSpatialDerivative_eq_old
    (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual CarryRestart 0 direction.succ =
      holonomicConjugateMatterDerivativeDual OldRestart 0 direction.succ := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [carryRestart_conjugateMatter_eq_carry,
    oldRestart_conjugateMatter_eq_oldCarry]
  apply congrArg matterDualOfCoordinates
  exact carry_conjugateMatterCoordinates_spatialDerivative_eq_old direction

private theorem carryPrimal_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt CarryPrimal.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [show CarryPrimal.coframe = CarryRestart.coframe by
    exact
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe
        CarryRestart]
  exact carryRestart_coframeFirstJet_origin

private theorem oldPrimal_coframeFirstJet_origin :
    holonomicCoframeFirstJetAt OldPrimal.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [show OldPrimal.coframe = OldRestart.coframe by
    exact
      actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_coframe
        OldRestart]
  exact oldRestart_coframeFirstJet_origin

private theorem carryPrimal_gravityConnection_eq_restart :
    CarryPrimal.gravityConnection = CarryRestart.gravityConnection := by
  unfold CarryPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_gravityConnection]

private theorem oldPrimal_gravityConnection_eq_restart :
    OldPrimal.gravityConnection = OldRestart.gravityConnection := by
  unfold OldPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_gravityConnection]

private theorem carryPrimal_gaugeConnection_eq_restart :
    CarryPrimal.gaugeConnection = CarryRestart.gaugeConnection := by
  unfold CarryPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_gaugeConnection]

private theorem oldPrimal_gaugeConnection_eq_restart :
    OldPrimal.gaugeConnection = OldRestart.gaugeConnection := by
  unfold OldPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_gaugeConnection]

private theorem carryPrimal_scalar_eq_restart :
    CarryPrimal.scalar = CarryRestart.scalar := by
  exact
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar
      CarryRestart

private theorem oldPrimal_scalar_eq_restart :
    OldPrimal.scalar = OldRestart.scalar := by
  exact
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_scalar
      OldRestart

private theorem carryPrimal_conjugateMatter_eq_restart :
    CarryPrimal.conjugateMatter = CarryRestart.conjugateMatter := by
  unfold CarryPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_conjugateMatter]

private theorem oldPrimal_conjugateMatter_eq_restart :
    OldPrimal.conjugateMatter = OldRestart.conjugateMatter := by
  unfold OldPrimal
  rw [actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual,
    installMatterLinearTimeResponse_conjugateMatter]

private theorem carryPrimal_conjugateMatterSpatialDerivative_eq_old
    (direction : Fin 3) :
    holonomicConjugateMatterDerivativeDual CarryPrimal 0 direction.succ =
      holonomicConjugateMatterDerivativeDual OldPrimal 0 direction.succ := by
  unfold holonomicConjugateMatterDerivativeDual
    holonomicConjugateMatterDerivativeCoordinates
    holonomicConjugateMatterCoordinates
  rw [carryPrimal_conjugateMatter_eq_restart,
    oldPrimal_conjugateMatter_eq_restart]
  exact carryRestart_conjugateMatterSpatialDerivative_eq_old direction

private theorem actionSelectedProfile_adjointVelocity_eq_old :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry 0
      ).adjointVelocity =
      (sourceActionGeneratedDiracDualCompleteJointProfiles Source OldCarry 0
      ).adjointVelocity := by
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity,
    sourceActionGeneratedDiracDualCompleteJointProfiles_adjointVelocity]
  change
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity CarryPrimal 0 =
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity OldPrimal 0
  calc
    holonomicDiracDualLiveCoframeConjugateMatterActionVelocity CarryPrimal 0 =
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          CarryPrimal 0 :=
      holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ carryPrimal_coframeFirstJet_origin
    _ = holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity
          OldPrimal 0 := by
      apply
        holonomicDiracDualRightChiralIdentityCoframeConjugateMatterActionVelocity_eq_of_pointData
      · rw [congrFun carryPrimal_gravityConnection_eq_restart 0,
          congrFun oldPrimal_gravityConnection_eq_restart 0]
        exact carryRestart_gravityConnection_origin_eq_old
      · rw [congrFun carryPrimal_gaugeConnection_eq_restart 0,
          congrFun oldPrimal_gaugeConnection_eq_restart 0]
        exact carryRestart_gaugeConnection_origin_eq_old
      · rw [congrFun carryPrimal_scalar_eq_restart 0,
          congrFun oldPrimal_scalar_eq_restart 0]
        exact carryRestart_scalar_origin_eq_old
      · rw [congrFun carryPrimal_conjugateMatter_eq_restart 0,
          congrFun oldPrimal_conjugateMatter_eq_restart 0]
        exact carryRestart_conjugateMatter_origin_eq_old
      · exact carryPrimal_conjugateMatterSpatialDerivative_eq_old
    _ = holonomicDiracDualLiveCoframeConjugateMatterActionVelocity OldPrimal 0 :=
      (holonomicDiracDualLiveCoframeConjugateMatterActionVelocity_eq_rightChiralIdentity_of_firstJet
        _ _ oldPrimal_coframeFirstJet_origin).symm

/-- The independently generated adjoint profile on the same carry and origin
also has zero velocity. -/
theorem fixedP506L0ActionSelectedCoupledTemporalProfile_adjointVelocity_zero :
    (sourceActionGeneratedDiracDualCompleteJointProfiles Source Carry 0
      ).adjointVelocity = 0 := by
  rw [actionSelectedProfile_adjointVelocity_eq_old,
    fixedP506L0U6RadialQuarticCoupledTemporalProfile_adjointVelocity_zero]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506ActionSelectedCoupledTemporalOriginProfileZero

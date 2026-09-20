import H0mework.Physics.JointVariation.LiveElectricGlobalDevelopmentOperator
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.DualVariation.JointResidualCarrier
import H0mework.Physics.DualVariation.RepairedMatterEquationReadout

/-!
# Complete-joint live-electric Cartan primal origin closure

The global temporal producer installs the action-selected matter velocity in
the actual first jet at its canonical origin.  The P286 algebraic and
live-electric legs preserve that matter jet, and the Cartan leg recomputes
the connection from the same coframe and matter values.  Consequently the
resulting Cartan actual satisfies the primal Dirac action law and its
conjugate-matter Euler reader vanishes.

Regularity below is used only to differentiate the already generated time
primitive.  No residual coordinate, target derivative, branch receipt, or
zero-fiber certificate enters a writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricCartanPrimalOriginClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeRepairedMatterEquationReadout
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Temporal
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent source current

private abbrev Algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent source current

private abbrev LiveP286
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current source current

private abbrev Cartan
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    source current

private abbrev ProfileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  completeJointGeneratedProfileRestartCurrent source current 0

private theorem canonicalZeroSliceOrigin :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem cartan_coframe_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).coframe =
      (ProfileRestart source current).coframe := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  rfl

private theorem cartan_scalar_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).scalar 0 =
      (ProfileRestart source current).scalar 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar]
  change (Temporal source current).scalar 0 = current.scalar 0
  simpa [Temporal, completeJointGlobalTemporalCurrent,
    canonicalZeroSliceOrigin] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
      source current (0 : StageNineSpatialPoint)

private theorem cartan_matter_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).matter 0 =
      (ProfileRestart source current).matter 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  change (Temporal source current).matter 0 = current.matter 0
  simpa [Temporal, completeJointGlobalTemporalCurrent,
    canonicalZeroSliceOrigin] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      source current (0 : StageNineSpatialPoint)

private theorem cartan_conjugateMatter_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).conjugateMatter 0 =
      (ProfileRestart source current).conjugateMatter 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]
  change (Temporal source current).conjugateMatter 0 =
    current.conjugateMatter 0
  simpa [Temporal, completeJointGlobalTemporalCurrent,
    canonicalZeroSliceOrigin] using
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      source current (0 : StageNineSpatialPoint)

private theorem algebraic_gaugeConnection_origin_eq_current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Algebraic source current).gaugeConnection 0 =
      current.gaugeConnection 0 := by
  have coordinateEquality :
      holonomicP286GaugeConnectionCoordinate
        (diracDualFormNativeP286CanonicalGeneratedActual source
          (Temporal source current)) 0 =
        holonomicP286GaugeConnectionCoordinate current 0 := by
    calc
      holonomicP286GaugeConnectionCoordinate
          (diracDualFormNativeP286CanonicalGeneratedActual source
            (Temporal source current)) 0 =
        holonomicP286GaugeConnectionCoordinate (Temporal source current) 0 := by
        exact
          installP286HolonomicConnectionSecondJet_connection_origin
            (Temporal source current)
            (p286CanonicalDiagonalResponseSecondJet
              (diracDualFormNativeP286CanonicalGeneratedWrite source
                (Temporal source current))) 1
      _ = holonomicP286GaugeConnectionCoordinate current 0 := by
        rfl
  funext direction
  apply p286CoordinateEquiv.injective
  exact congrFun coordinateEquality direction

private theorem cartan_gaugeConnection_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).gaugeConnection 0 =
      (ProfileRestart source current).gaugeConnection 0 := by
  unfold Cartan ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection]
  exact algebraic_gaugeConnection_origin_eq_current source current

private theorem cartan_gravityConnection_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (Cartan source current).gravityConnection 0 =
      (ProfileRestart source current).gravityConnection 0 := by
  have coframeFieldEq :
      (LiveP286 source current).coframe = current.coframe := by
    rfl
  have matterEq :
      (LiveP286 source current).matter 0 = current.matter 0 := by
    change (Temporal source current).matter 0 = current.matter 0
    simpa [Temporal, completeJointGlobalTemporalCurrent,
      canonicalZeroSliceOrigin] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
        source current (0 : StageNineSpatialPoint)
  have conjugateMatterEq :
      (LiveP286 source current).conjugateMatter 0 =
        current.conjugateMatter 0 := by
    change (Temporal source current).conjugateMatter 0 =
      current.conjugateMatter 0
    simpa [Temporal, completeJointGlobalTemporalCurrent,
      canonicalZeroSliceOrigin] using
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
        source current (0 : StageNineSpatialPoint)
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      source (LiveP286 source current) current 0
      (congrFun coframeFieldEq 0) matterEq conjugateMatterEq
  unfold Cartan
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero]
  change
    diracDualFormNativeActionCartanConnectionAt source
        (LiveP286 source current) 0 =
      diracDualFormNativeActionCartanConnectionAt source current 0
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeFieldEq, spinEq]

private theorem cartan_matterCoordinateSpatialDerivative_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0)
    (direction : Fin 3) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((Cartan source current).matter point)) 0 direction.succ =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((ProfileRestart source current).matter point)) 0 direction.succ := by
  have generatedDerivative :=
    completeJointTemporalMatterCoordinates_hasFDerivAt_zero_of_contDiffAt
      source current currentDifferentiable correctionRegular
  unfold fieldDirectionalDerivative
  rw [show
    (fun point => matterCoordinateEquiv
      ((Cartan source current).matter point)) =
      fun point => matterCoordinateEquiv
        ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
          source current).matter point)
    by rfl]
  rw [generatedDerivative.fderiv]
  unfold ProfileRestart completeJointGeneratedProfileRestartCurrent
  rw [fullyRecenterHolonomicConfiguration_zero,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply]
  have spatialProjection :
      canonicalTimeProjection (coordinateDirection direction.succ) = 0 := by
    fin_cases direction <;>
      simp [canonicalTimeProjection, canonicalLorentzianTimeDirection,
        coordinateDirection, localBaseCoordinate_apply]
  rw [spatialProjection, zero_smul, add_zero]

private theorem cartan_matterCoordinateTimeDerivative_eq_profileVelocity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((Cartan source current).matter point))
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv
        (sourceActionGeneratedDiracDualCompleteJointProfiles
          source current 0).matterVelocity := by
  change
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            source current).matter point))
        0 canonicalLorentzianTimeDirection = _
  exact completeJointGlobalTemporalCurrent_matterTimeDerivative_zero
    source current currentDifferentiable correctionRegular

private theorem cartan_matterCovariantDerivative_spatial_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0)
    (direction : Fin 3) :
    holonomicMatterCovariantDerivative (Cartan source current) 0 direction.succ =
      holonomicMatterCovariantDerivative
        (ProfileRestart source current) 0 direction.succ := by
  unfold holonomicMatterCovariantDerivative
  rw [cartan_matterCoordinateSpatialDerivative_eq_profileRestart
      source current currentDifferentiable correctionRegular direction,
    cartan_gravityConnection_origin_eq_profileRestart,
    cartan_gaugeConnection_origin_eq_profileRestart,
    cartan_matter_origin_eq_profileRestart]

private theorem cartan_knownVector_origin_eq_profileRestart
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
        (Cartan source current) 0 =
      holonomicDiracDualCurrentCoframeMatterKnownVector
        (ProfileRestart source current) 0 := by
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  rw [congrFun (cartan_coframe_eq_profileRestart source current) 0,
    cartan_scalar_origin_eq_profileRestart,
    cartan_matter_origin_eq_profileRestart]
  simp_rw [cartan_matterCovariantDerivative_spatial_eq_profileRestart
    source current currentDifferentiable correctionRegular]

private theorem cartan_matterCovariantDerivative_time_eq_generated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0) :
    holonomicMatterCovariantDerivative (Cartan source current) 0
        canonicalLorentzianTimeDirection =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
        (ProfileRestart source current) 0 := by
  unfold holonomicMatterCovariantDerivative
  rw [cartan_matterCoordinateTimeDerivative_eq_profileVelocity
      source current currentDifferentiable correctionRegular,
    sourceActionGeneratedDiracDualCompleteJointProfiles_matterVelocity,
    matterCoordinateEquiv.symm_apply_apply]
  unfold
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    holonomicMatterConnectionAction
  rw [cartan_gravityConnection_origin_eq_profileRestart,
    cartan_gaugeConnection_origin_eq_profileRestart,
    cartan_matter_origin_eq_profileRestart]
  module

/-- The complete temporal/P286/live-electric/Cartan composition satisfies
the primal action law at its own origin. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_primalActionLaw_origin
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    HolonomicDiracDualCurrentCoframeMatterTimeActionLaw
      (Cartan source current) 0
      (holonomicMatterCovariantDerivative (Cartan source current) 0
        canonicalLorentzianTimeDirection) := by
  have profileNoncharacteristic :
      coframeTemporalPrincipalScalar
          ((ProfileRestart source current).coframe 0) ≠ 0 := by
    simpa [ProfileRestart, completeJointGeneratedProfileRestartCurrent] using
      noncharacteristic
  have generated :=
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
      (ProfileRestart source current) 0 profileNoncharacteristic
  unfold HolonomicDiracDualCurrentCoframeMatterTimeActionLaw at generated ⊢
  rw [congrFun (cartan_coframe_eq_profileRestart source current) 0,
    cartan_knownVector_origin_eq_profileRestart source current
      currentDifferentiable correctionRegular,
    cartan_matterCovariantDerivative_time_eq_generated source current
      currentDifferentiable correctionRegular]
  exact generated

/-- Direct zero-fiber readout of the primal action law on the same generated
Cartan actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatterResidual_origin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (current.matter point)) 0)
    (correctionRegular : ContDiffAt ℝ 0
      (completeJointMatterTemporalCoordinateCorrection source current) 0)
    (noncharacteristic :
      coframeTemporalPrincipalScalar (current.coframe 0) ≠ 0) :
    (diracDualFormNativePointwiseJointResidual source
      (Cartan source current) 0).conjugateMatter = 0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient source
        (Cartan source current) direction 0 = 0
  unfold diracDualConjugateMatterDirectionalCoefficient
  rw [generatedContinuumDiracDualMatterVector_zero_of_repairedActionLaw
    source (Cartan source current) 0
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_primalActionLaw_origin
      source current currentDifferentiable correctionRegular
      noncharacteristic)]
  simp

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricCartanPrimalOriginClosure

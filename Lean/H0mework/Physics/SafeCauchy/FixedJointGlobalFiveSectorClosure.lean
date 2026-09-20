import H0mework.Physics.SafeCauchy.FixedJointGlobalDevelopment
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessor
import H0mework.Physics.SynchronizedJoint.FixedLorentzGlobalActual
import H0mework.Physics.FixedJoint.FixedConstitutivePhysicalClosure
import H0mework.Physics.FixedJoint.FixedOriginPhysicalClosure

/-!
# SafeFinal non-gravity five-sector closure

This module reads the five non-gravity teeth of the repaired, contact-accurate
S9-C sector package from the exact Cauchy-safe `SafeFinal` occurrence:

* nonzero P286 gauge curvature;
* nonzero generated breaking vacuum and Yukawa mass;
* nonzero matter current;
* nonzero matter spin, hence `StressOrSpinNonzeroAt`.

The matter and adjoint values are transported only along the defining
zero-slice stages of this occurrence.  The gauge-curvature proof follows the
same action-selected radial write and uses its public zero-slice curvature
normal form; the radial increment vanishes at the origin.  No sibling actual,
residual receipt, gravity target, stationarity theorem, or completed S9-C
package is supplied.
-/

open SaturationMonoid

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalFiveSectorClosure

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCClassicalWorldAcceptance
open StageNineCanonicalCauchyState
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual
open StageNineDiracDualFormNativeFixedP506JointActionConstitutivePhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineConnectionSectorSourceBalance
open StageNineLorentzActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev Base : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source Prepared

private abbrev ECPath : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source Base

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev PriorPath : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev PriorCarry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source PriorPath

private abbrev PriorCoupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source PriorPath

private abbrev Input : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalInput

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

private abbrev QuadraticPrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

private abbrev ConstitutiveSuccessor : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private theorem canonicalSlice_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe_origin_one :
    Final.coframe 0 = 1 := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe]
  change Prepared.coframe 0 = 1
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin

private theorem final_matter_origin_eq_prepared :
    Final.matter 0 = Prepared.matter 0 := by
  change
    (actionGeneratedGlobalFrameMatterDualActual ECPath).matter 0 =
      Prepared.matter 0
  rw [(actionGeneratedGlobalFrameMatterDualActual_fieldInventory ECPath
    ).2.2.2.2.2.2.2.1,
    actionGeneratedGlobalFrameTimeMatterActual_matter_origin]
  change
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      Source Base).matter 0 = Prepared.matter 0
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source Base).matter 0 = Prepared.matter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source Base (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at generated
  exact generated

private theorem final_conjugateMatter_origin_eq_prepared :
    Final.conjugateMatter 0 = Prepared.conjugateMatter 0 := by
  change
    (actionGeneratedGlobalFrameMatterDualActual ECPath).conjugateMatter 0 =
      Prepared.conjugateMatter 0
  rw [(actionGeneratedGlobalFrameMatterDualActual_fieldInventory ECPath
    ).2.2.2.2.2.2.2.2]
  change
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      Source Base).conjugateMatter 0 = Prepared.conjugateMatter 0
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source Base).conjugateMatter 0 = Prepared.conjugateMatter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source Base (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at generated
  exact generated

private theorem priorPath_matter_origin_probe :
    PriorPath.matter 0 = diracSpinTwoMatterProbe := by
  change
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.matter
        0 = diracSpinTwoMatterProbe
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_matter]
  exact fixedP506L0CompleteJointActionSpacetimeSection_matter_origin

private theorem priorPath_conjugateMatter_origin_probe :
    PriorPath.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
  change
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.conjugateMatter
        0 = diracSpinZeroMatterCoordinate
  rw [
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite,
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_conjugateMatter]
  exact fixedP506L0CompleteJointActionSpacetimeSection_conjugateMatter_origin

private theorem prepared_matter_origin_probe :
    Prepared.matter 0 = diracSpinTwoMatterProbe := by
  calc
    Prepared.matter 0 = CartanBase.matter 0 := by rfl
    _ = Input.matter 0 := by rfl
    _ = PriorCoupled.matter 0 := by rfl
    _ = PriorCarry.matter 0 := by
      have generated :=
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
          Source PriorCarry (0 : StageNineSpatialPoint)
      rw [canonicalSlice_zero] at generated
      exact generated
    _ = PriorPath.matter 0 := by rfl
    _ = diracSpinTwoMatterProbe := priorPath_matter_origin_probe

private theorem prepared_conjugateMatter_origin_probe :
    Prepared.conjugateMatter 0 = diracSpinZeroMatterCoordinate := by
  calc
    Prepared.conjugateMatter 0 = CartanBase.conjugateMatter 0 := by rfl
    _ = Input.conjugateMatter 0 := by rfl
    _ = PriorCoupled.conjugateMatter 0 := by rfl
    _ = PriorCarry.conjugateMatter 0 := by
      have generated :=
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
          Source PriorCarry (0 : StageNineSpatialPoint)
      rw [canonicalSlice_zero] at generated
      exact generated
    _ = PriorPath.conjugateMatter 0 := by rfl
    _ = diracSpinZeroMatterCoordinate := priorPath_conjugateMatter_origin_probe

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe :
    Final.matter 0 = diracSpinTwoMatterProbe :=
  final_matter_origin_eq_prepared.trans prepared_matter_origin_probe

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe :
    Final.conjugateMatter 0 = diracSpinZeroMatterCoordinate :=
  final_conjugateMatter_origin_eq_prepared.trans
    prepared_conjugateMatter_origin_probe

private theorem algebraic_gaugeConnection_eq_fixedInput :
    Algebraic.gaugeConnection = FixedInput.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source FixedInput) 0 by
    exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem priorPath_gaugeConnection_eq_u6 :
    PriorPath.gaugeConnection = U6.gaugeConnection := by
  calc
    PriorPath.gaugeConnection =
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalActual.gaugeConnection := by
      change
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual.gaugeConnection = _
      rw [
        fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_eq_actionWrite,
        sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gaugeConnection]
      rfl
    _ = fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeConnection := by
      change
        (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
          Source fixedP506L0CompleteJointActionSpacetimeSectionActual 0
          ).gaugeConnection =
        fixedP506L0CompleteJointActionSpacetimeSectionActual.gaugeConnection
      exact
        sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_gaugeConnection
          Source fixedP506L0CompleteJointActionSpacetimeSectionActual 0
    _ = FixedInput.gaugeConnection :=
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        Source FixedInput
    _ = Algebraic.gaugeConnection := algebraic_gaugeConnection_eq_fixedInput.symm
    _ = U6.gaugeConnection := fixedP506L0U6_gaugeConnection_eq_algebraic.symm

private abbrev FixedRadial : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConnectionActual

private theorem priorCarry_gaugeConnection_eq_fixedRadial :
    PriorCarry.gaugeConnection = FixedRadial.gaugeConnection := by
  rw [show PriorCarry.gaugeConnection =
      (completeJointActionSelectedRadialConnectionActual Source PriorPath
        ).gaugeConnection by rfl]
  unfold completeJointActionSelectedRadialConnectionActual
    completeJointActionSelectedRadialConnection
  change
    (varyP286GaugeConnectionCoordinate PriorPath
      (p286RadialQuarticTemporalConnection
        (completeJointActionSelectedRadialCharge Source PriorPath)) 1
      ).gaugeConnection =
    (varyP286GaugeConnectionCoordinate U6
      (p286RadialQuarticTemporalConnection Charge) 1).gaugeConnection
  have chargeEq :
      completeJointActionSelectedRadialCharge Source PriorPath = Charge := by
    change fixedP506L0LorentzPathActionSelectedRadialCharge =
      fixedP506L0U6OccurrenceP286MotherActionCharge
    exact
      fixedP506L0LorentzPathActionSelectedRadialCharge_eq_motherActionCharge
  rw [chargeEq]
  funext point direction
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    gaugeConnection_varyP286GaugeConnectionCoordinate,
    priorPath_gaugeConnection_eq_u6]

private theorem final_gaugeConnection_eq_fixedRadial :
    Final.gaugeConnection = FixedRadial.gaugeConnection := by
  calc
    Final.gaugeConnection = Base.gaugeConnection := by rfl
    _ = PriorCoupled.gaugeConnection := by rfl
    _ = PriorCarry.gaugeConnection := by rfl
    _ = FixedRadial.gaugeConnection :=
      priorCarry_gaugeConnection_eq_fixedRadial

private theorem fixedRadial_gaugeCurvature_origin_eq_algebraic :
    holonomicGaugeCurvature FixedRadial 0 =
      holonomicGaugeCurvature Algebraic 0 := by
  have curvatureCoordinates :=
    fixedP506L0U6RadialQuarticConnection_curvature_zeroSlice
      (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at curvatureCoordinates
  have incrementZero :
      fixedP506L0U6RadialQuarticCurvatureIncrement 0 = 0 := by
    funext pair
    fin_cases pair <;>
      simp [fixedP506L0U6RadialQuarticCurvatureIncrement,
        p286SpatialRadiusSquared, p286SpatialMetricCovectorOperator,
        p286BaseCoordinate_apply, Fin.sum_univ_three]
  rw [incrementZero, add_zero] at curvatureCoordinates
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun curvatureCoordinates pair

private theorem fixedRadial_gaugeCurvature_origin_eq_u6 :
    holonomicGaugeCurvature FixedRadial 0 =
      holonomicGaugeCurvature U6 0 := by
  calc
    holonomicGaugeCurvature FixedRadial 0 =
        holonomicGaugeCurvature Algebraic 0 :=
      fixedRadial_gaugeCurvature_origin_eq_algebraic
    _ = holonomicGaugeCurvature U6 0 :=
      (holonomicGaugeCurvature_eq_of_connection_eq U6 Algebraic
        fixedP506L0U6_gaugeConnection_eq_algebraic 0).symm

private theorem u6_gaugeConnection_eq_constitutiveSuccessor :
    U6.gaugeConnection = ConstitutiveSuccessor.gaugeConnection := by
  calc
    U6.gaugeConnection = Algebraic.gaugeConnection :=
      fixedP506L0U6_gaugeConnection_eq_algebraic
    _ = FixedInput.gaugeConnection := algebraic_gaugeConnection_eq_fixedInput
    _ = ConstitutiveSuccessor.gaugeConnection := by
      rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_gaugeCurvature_origin_ne_zero :
    holonomicGaugeCurvature Final 0 ≠ 0 := by
  rw [holonomicGaugeCurvature_eq_of_connection_eq Final FixedRadial
    final_gaugeConnection_eq_fixedRadial 0,
    fixedRadial_gaugeCurvature_origin_eq_u6,
    holonomicGaugeCurvature_eq_of_connection_eq U6 ConstitutiveSuccessor
      u6_gaugeConnection_eq_constitutiveSuccessor 0]
  exact
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeCurvature_origin_ne_zero

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_temporalHyperchargeMatterCurrent :
    p286MatterCurrentCoefficient Source Final
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 = -1 := by
  calc
    _ = p286MatterCurrentCoefficient Source FixedP506JointActionSuccessor
          (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 := by
      apply p286MatterCurrentCoefficient_eq_of_origin_contacts
      · exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe_origin_one.trans
          fixedP506JointActionSuccessor_coframe_origin.symm
      · exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe.trans
          fixedP506JointActionSuccessor_matter_origin.symm
      · exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe.trans
          fixedP506JointActionSuccessor_conjugateMatter_origin.symm
    _ = -1 := fixedP506JointActionSuccessor_temporalHyperchargeMatterCurrent

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterCurrentNonzeroAt_origin :
    MatterCurrentNonzeroAt Source Final 0 := by
  refine ⟨p286TemporalGaugeOneForm hyperchargeCoordinate, ?_⟩
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_temporalHyperchargeMatterCurrent]
  norm_num

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient Source Final
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  exact spinProbeResponse_eq_half_of_origin Final
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe_origin_one
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterSpinNonzeroAt_origin :
    MatterSpinNonzeroAt Source Final 0 := by
  refine
    ⟨canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1), ?_⟩
  rw [fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterSpin_eq_half]
  norm_num

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_stressOrSpinNonzeroAt_origin :
    StressOrSpinNonzeroAt Source Final 0 :=
  Or.inr
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterSpinNonzeroAt_origin

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_breakingVacuum :
    sourceGeneratedVacuumBase Source ≠ 0 :=
  positive_sourceGeneratedVacuumBase_nonzero

theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_yukawaMass :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase Source) ≠ 0 :=
  positiveP506L0_sourceGeneratedYukawaMass_ne_zero

/-- The five non-gravity teeth of the repaired contact-accurate S9-C
six-sector payload, all read from the exact SafeFinal occurrence. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nonGravityFiveSectorClosure :
    (∃ point, holonomicGaugeCurvature Final point ≠ 0) ∧
      sourceGeneratedVacuumBase Source ≠ 0 ∧
      exteriorYukawaMassMap (sourceGeneratedVacuumBase Source) ≠ 0 ∧
      (∃ point, MatterCurrentNonzeroAt Source Final point) ∧
      (∃ point, StressOrSpinNonzeroAt Source Final point) := by
  exact
    ⟨⟨0,
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_gaugeCurvature_origin_ne_zero⟩,
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_breakingVacuum,
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_yukawaMass,
      ⟨0,
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterCurrentNonzeroAt_origin⟩,
      ⟨0,
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_stressOrSpinNonzeroAt_origin⟩⟩

#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_gaugeCurvature_origin_ne_zero
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matterCurrentNonzeroAt_origin
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nonGravityFiveSectorClosure

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalFiveSectorClosure
end PhysicsCore
end SaturationMonoid

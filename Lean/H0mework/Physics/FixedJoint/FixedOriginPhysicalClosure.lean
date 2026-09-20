import H0mework.Physics.Geometry.CClassicalAcceptance
import H0mework.Physics.FixedJoint.FixedZeroFiber
import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# Fixed P506/L0 joint-action origin physical closure

The source-native joint action write already puts the complete nine-coordinate
residual on its zero fiber at the fixed contact.  This module reads the
physical content retained by that *same* successor:

* exact P506/L0 lineage and all-field smoothness;
* the generated scalar vacuum and nonzero P286 curvature;
* nonzero matter current and spin at the common contact;
* the physical Cartan torsion--spin equality at that contact.

These are acceptance readouts of one actual.  They neither split the complete
residual into new hard gates nor promote a local Hodge convention seam into a
route decision.  In particular, the theorem below remains explicitly an
origin/contact closure; it does not claim a global residual section is zero.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCartanTangentSimplicityResponse
open StageNineCClassicalWorldAcceptance
open StageNineCoframeFirstJet
open StageNineConnectionSectorSourceBalance
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalLorentzThreeFormDuality
open SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedP506JointActionCurrent :
    StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual

theorem fixedP506JointActionSuccessor_coframe_origin :
    FixedP506JointActionSuccessor.coframe 0 = 1 := by
  rw [fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe_origin]

theorem fixedP506JointActionSuccessor_matter_origin :
    FixedP506JointActionSuccessor.matter 0 =
      diracSpinTwoMatterProbe := by
  rw [fixedP506JointActionSuccessor_matter,
    fixedP506JointActual_matter_origin]

theorem fixedP506JointActionSuccessor_conjugateMatter_origin :
    FixedP506JointActionSuccessor.conjugateMatter 0 =
      diracSpinZeroMatterCoordinate := by
  rw [fixedP506JointActionSuccessor_conjugateMatter,
    fixedP506JointActual_conjugateMatter_origin]

private theorem positive_generatedLocalVacuumCoordinates_zero :
    generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  rw [generatedLocalVacuumCoordinates, generatedScalarFrame,
    generatedTransition_normalized]
  exact scalarCoordinateAction_one _

theorem fixedP506JointActionSuccessor_scalarGeneratedVacuum :
    FixedP506JointActionSuccessor.scalar =
      generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 := by
  calc
    _ = FixedP506JointActual.scalar :=
      fixedP506JointActionSuccessor_scalar
    _ = (fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) :=
      fixedP506JointActual_scalar_vacuum
    _ = generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 :=
      positive_generatedLocalVacuumCoordinates_zero.symm

theorem fixedP506JointActionSuccessor_gaugeCurvature_origin_ne_zero :
    holonomicGaugeCurvature FixedP506JointActionSuccessor 0 ≠ 0 := by
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    FixedP506JointActionSuccessor FixedP506JointActual
    fixedP506JointActionSuccessor_gaugeConnection 0]
  exact fixedP506JointActual_gaugeCurvature_origin_ne_zero

theorem p286MatterCurrentCoefficient_eq_of_origin_contacts
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe 0 = second.coframe 0)
    (matterEq : first.matter 0 = second.matter 0)
    (conjugateEq :
      first.conjugateMatter 0 = second.conjugateMatter 0)
    (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource first direction 0 =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource second direction
        0 := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [coframeEq, matterEq, conjugateEq]

private theorem
    positiveP506MatterCurrentGravityCoupledP286Momentum_coframe_origin :
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift.coframe
        0 =
      1 := by
  change positiveP506MatterCurrentGravityCoupledLocalActualLift.coframe 0 = 1
  exact positiveP506MatterCurrentGravityCoupledLocalActualLift_coframe_one 0

private theorem
    positiveP506MatterCurrentGravityCoupledP286Momentum_matter_origin :
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift.matter
        0 =
      diracSpinTwoMatterProbe := by
  change
    positiveP506MatterCurrentGravityCoupledLocalActualLift.matter 0 =
      diracSpinTwoMatterProbe
  exact positiveP506MatterCurrentGravityCoupledLocalActualLift_matter_origin

private theorem
    positiveP506MatterCurrentGravityCoupledP286Momentum_conjugate_origin :
    positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift.conjugateMatter
        0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    positiveP506MatterCurrentGravityCoupledLocalActualLift.conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  exact
    positiveP506MatterCurrentGravityCoupledLocalActualLift_conjugate_origin

private theorem
    positiveP506MatterCurrentGravityCoupledP286Momentum_temporalHyperchargeMatterCurrent :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 =
      -1 := by
  unfold p286MatterCurrentCoefficient
  rw [temporalHyperchargeMatterFirstVariationDensity]
  simp [generatedVolumeDensity, toContinuumPointField,
    positiveP506MatterCurrentGravityCoupledP286Momentum_coframe_origin]

theorem
    fixedP506JointActionSuccessor_temporalHyperchargeMatterCurrent :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 =
      -1 := by
  calc
    _ =
        p286MatterCurrentCoefficient positiveSmoothUnifiedSource
          positiveP506MatterCurrentGravityCoupledP286MomentumLocalActualLift
          (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 := by
      apply p286MatterCurrentCoefficient_eq_of_origin_contacts
      · rw [fixedP506JointActionSuccessor_coframe_origin,
          positiveP506MatterCurrentGravityCoupledP286Momentum_coframe_origin]
      · rw [fixedP506JointActionSuccessor_matter_origin,
          positiveP506MatterCurrentGravityCoupledP286Momentum_matter_origin]
      · rw [fixedP506JointActionSuccessor_conjugateMatter_origin,
          positiveP506MatterCurrentGravityCoupledP286Momentum_conjugate_origin]
    _ = -1 :=
      positiveP506MatterCurrentGravityCoupledP286Momentum_temporalHyperchargeMatterCurrent

theorem fixedP506JointActionSuccessor_matterCurrentNonzeroAt :
    MatterCurrentNonzeroAt positiveSmoothUnifiedSource
      FixedP506JointActionSuccessor 0 := by
  refine ⟨p286TemporalGaugeOneForm hyperchargeCoordinate, ?_⟩
  rw [fixedP506JointActionSuccessor_temporalHyperchargeMatterCurrent]
  norm_num

theorem fixedP506JointActionSuccessor_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor
        (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
      1 / 2 := by
  exact
    spinProbeResponse_eq_half_of_origin FixedP506JointActionSuccessor
      fixedP506JointActionSuccessor_coframe_origin
      fixedP506JointActionSuccessor_matter_origin
      fixedP506JointActionSuccessor_conjugateMatter_origin

theorem fixedP506JointActionSuccessor_matterSpinNonzeroAt :
    MatterSpinNonzeroAt positiveSmoothUnifiedSource
      FixedP506JointActionSuccessor 0 := by
  refine
    ⟨canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1), ?_⟩
  rw [fixedP506JointActionSuccessor_matterSpin_eq_half]
  norm_num

theorem fixedP506JointActionSuccessor_stressOrSpinNonzeroAt :
    StressOrSpinNonzeroAt positiveSmoothUnifiedSource
      FixedP506JointActionSuccessor 0 :=
  Or.inr fixedP506JointActionSuccessor_matterSpinNonzeroAt

theorem fixedP506JointActionSuccessor_torsionSpin_origin :
    internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (FixedP506JointActionSuccessor.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                FixedP506JointActionSuccessor.coframe 0)
              (FixedP506JointActionSuccessor.gravityConnection 0))) =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus
              FixedP506JointActionSuccessor) 0) := by
  have coframeEq :
      FixedP506JointActionSuccessor.coframe =
        FixedP506JointActionCurrent.coframe := by
    calc
      _ = FixedP506JointActual.coframe :=
        fixedP506JointActionSuccessor_coframe
      _ = FixedP506JointActionCurrent.coframe :=
        currentP286CompleteActionResponseOperator_coframe
          positiveSmoothUnifiedSource FixedP506JointActionCurrent
  have gravityConnectionEq :
      FixedP506JointActionSuccessor.gravityConnection =
        FixedP506JointActionCurrent.gravityConnection := by
    calc
      _ = FixedP506JointActual.gravityConnection :=
        fixedP506JointActionSuccessor_gravityConnection
      _ = FixedP506JointActionCurrent.gravityConnection :=
        currentP286CompleteActionResponseOperator_gravityConnection
          positiveSmoothUnifiedSource FixedP506JointActionCurrent
  have pointFieldEq :
      toContinuumPointField FixedP506JointActionSuccessor 0 =
        toContinuumPointField FixedP506JointActionCurrent 0 := by
    exact
      fixedP506JointActionSuccessor_pointField_origin.trans
        (currentP286CompleteActionResponseOperator_pointField_origin
          positiveSmoothUnifiedSource FixedP506JointActionCurrent)
  have restrictedPointFieldEq :
      toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            FixedP506JointActionSuccessor) 0 =
        toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            FixedP506JointActionCurrent) 0 := by
    rw [
      toContinuumPointField_restrictHolonomicConfigurationToIIPlus,
      toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
    exact congrArg restrictContinuumPointFieldToIIPlus pointFieldEq
  calc
    _ =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            (FixedP506JointActionCurrent.coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                FixedP506JointActionCurrent.coframe 0)
              (FixedP506JointActionCurrent.gravityConnection 0))) := by
      rw [coframeEq, gravityConnectionEq]
    _ =
        formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus
              FixedP506JointActionCurrent) 0) :=
      fixedGlobalMatterDualFullCauchy_torsionSpin_origin
    _ = _ := by rw [restrictedPointFieldEq]

theorem positiveP506L0_sourceGeneratedYukawaMass_ne_zero :
    exteriorYukawaMassMap
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) ≠
      0 := by
  rw [positive_sourceGeneratedVacuumBase]
  exact finiteGenerationJointMassMap_ne_zero

/-- Positive fixed-contact checkpoint: one same-source successor is smooth,
lies on the complete nine-coordinate origin zero fiber, and retains the
generated vacuum, nonzero P286/matter sectors, and Cartan torsion--spin
balance.  No local convention readout is used as a premise. -/
theorem fixedP506JointActionSuccessor_originPhysicalClosure :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      FixedP506JointActionSuccessor.Smooth ∧
      fixedP506JointActionSuccessorResidualSection 0 = 0 ∧
      FixedP506JointActionSuccessor.scalar =
        generatedLocalVacuumCoordinates positiveSmoothUnifiedSource 0 ∧
      holonomicGaugeCurvature FixedP506JointActionSuccessor 0 ≠ 0 ∧
      sourceGeneratedVacuumBase positiveSmoothUnifiedSource ≠ 0 ∧
      exteriorYukawaMassMap
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) ≠ 0 ∧
      MatterCurrentNonzeroAt positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor 0 ∧
      MatterSpinNonzeroAt positiveSmoothUnifiedSource
        FixedP506JointActionSuccessor 0 ∧
      internalBivectorDualThreeForm
            (torsionCoframeWedgeThreeForm
              (FixedP506JointActionSuccessor.coframe 0)
              (pointwiseCartanTorsion
                (holonomicCoframeFirstJetAt
                  FixedP506JointActionSuccessor.coframe 0)
                (FixedP506JointActionSuccessor.gravityConnection 0))) =
          formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
            (toContinuumPointField
              (restrictHolonomicConfigurationToIIPlus
                FixedP506JointActionSuccessor) 0) := by
  exact
    ⟨fixedP506JointActionSuccessor_exactLineage,
      fixedP506JointActionSuccessor_smooth,
      fixedP506JointActionSuccessorResidual_origin_zero,
      fixedP506JointActionSuccessor_scalarGeneratedVacuum,
      fixedP506JointActionSuccessor_gaugeCurvature_origin_ne_zero,
      positive_sourceGeneratedVacuumBase_nonzero,
      positiveP506L0_sourceGeneratedYukawaMass_ne_zero,
      fixedP506JointActionSuccessor_matterCurrentNonzeroAt,
      fixedP506JointActionSuccessor_matterSpinNonzeroAt,
      fixedP506JointActionSuccessor_torsionSpin_origin⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure

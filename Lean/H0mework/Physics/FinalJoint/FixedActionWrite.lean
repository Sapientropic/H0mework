import H0mework.Physics.DualVariation.RecenteredScalarSecondJetActionPrincipal
import H0mework.Physics.GaugeAction.P286CompleteActionResponseOperator
import H0mework.Physics.ConstrainedCauchy.LocalActualLift
import H0mework.Physics.DualVariation.JointResidualCarrier

/-!
# Fixed P506/L0 dependency-ordered common action write

The fixed matching contact is advanced by one source/action-owned composite:

```text
Cartan restart
  -> repaired primal/adjoint matter and constitutive write
  -> action-generated scalar second jet
  -> form-native P286 auxiliary first jet
  -> full Einstein--Cartan Cauchy write.
```

Every leg consumes only the same fixed source and the current produced by the
preceding leg.  No residual coordinate, residual support, target actual,
branch, field equation, or zero-fiber witness enters either constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeIIPlusJetKinematics
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineScalarPointwiseEquation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! ## One dependency-ordered action write -/

/-- The fixed P506/L0 contact translated to the selected spatial occurrence. -/
def fixedP506L0RecenteredInput
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  spatiallyRecenterHolonomicConfiguration
    FixedP506FormNativeJointActionSolvedSuccessor space

/-- The first leg is the source/action-native Cartan restart. -/
def fixedP506L0CartanRestartActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource (fixedP506L0RecenteredInput space)

theorem recenteredCartanRepairedConstitutiveCurrent_eq_repairedCartan
    (space : StageNineSpatialPoint) :
    recenteredCartanRepairedConstitutiveCurrent space =
      diracDualFormNativeRepairedConstitutiveWrittenCurrent
        positiveSmoothUnifiedSource (fixedP506L0CartanRestartActual space) :=
  rfl

@[simp] theorem recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).coframe =
      (fixedP506L0CartanRestartActual space).coframe :=
  rfl

@[simp] theorem
    recenteredCartanRepairedConstitutiveCurrent_gravityConnection_eq_cartan
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).gravityConnection =
      (fixedP506L0CartanRestartActual space).gravityConnection :=
  rfl

theorem recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).matter 0 =
      (fixedP506L0CartanRestartActual space).matter 0 := by
  rw [recenteredCartanRepairedConstitutiveCurrent_eq_repairedCartan]
  change
    (actionGeneratedDiracDualRepairedMatterJointResponseActual
      (fixedP506L0CartanRestartActual space)).matter 0 = _
  unfold actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_matter,
    actionGeneratedDiracDualCurrentCoframeMatterTimeResponseActual_matter_origin]

theorem
    recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter 0 =
      (fixedP506L0CartanRestartActual space).conjugateMatter 0 := by
  rw [recenteredCartanRepairedConstitutiveCurrent_eq_repairedCartan]
  change
    (actionGeneratedDiracDualRepairedMatterJointResponseActual
      (fixedP506L0CartanRestartActual space)).conjugateMatter 0 = _
  unfold actionGeneratedDiracDualRepairedMatterJointResponseActual
  rw [actionGeneratedDiracDualLiveCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin]
  rfl

private theorem
    recenteredCartanRepairedConstitutiveCurrent_actionCartanConnection_origin_eq_cartan
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0CartanRestartActual space) 0 := by
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      (recenteredCartanRepairedConstitutiveCurrent space)
      (fixedP506L0CartanRestartActual space) 0
      (congrFun
        (recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan space) 0)
      (recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan
        space)
      (recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan
        space)
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan, spinEq]

theorem
    recenteredCartanRepairedConstitutiveCurrent_connection_selfGenerated_origin
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
  calc
    (recenteredCartanRepairedConstitutiveCurrent space).gravityConnection 0 =
        (fixedP506L0CartanRestartActual space).gravityConnection 0 := by
      rw [recenteredCartanRepairedConstitutiveCurrent_gravityConnection_eq_cartan]
    _ = diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          (fixedP506L0CartanRestartActual space) 0 := by
      exact
        sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
          positiveSmoothUnifiedSource (fixedP506L0RecenteredInput space) 0
    _ = diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) 0 :=
      (recenteredCartanRepairedConstitutiveCurrent_actionCartanConnection_origin_eq_cartan
        space).symm

/-- The pre-EC current after the scalar and P286 action legs. -/
def fixedP506L0FinalCommonPreECActionActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  formNativeCurrentP286CompleteActionResponseOperator
    positiveSmoothUnifiedSource
    (recenteredCartanRepairedScalarSecondJetActual space)

@[simp] theorem fixedP506L0FinalCommonPreECActionActual_coframe_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).coframe =
      (recenteredCartanRepairedConstitutiveCurrent space).coframe :=
  rfl

@[simp] theorem
    fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).gravityConnection =
      (recenteredCartanRepairedConstitutiveCurrent space).gravityConnection :=
  rfl

@[simp] theorem fixedP506L0FinalCommonPreECActionActual_matter_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).matter =
      (recenteredCartanRepairedConstitutiveCurrent space).matter :=
  rfl

@[simp] theorem
    fixedP506L0FinalCommonPreECActionActual_conjugateMatter_eq_recentered
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).conjugateMatter =
      (recenteredCartanRepairedConstitutiveCurrent space).conjugateMatter :=
  rfl

/-- One common fixed-lineage successor.  The final EC write is deliberately
last because it recomputes the coframe/gravity response from every earlier
matter, scalar, and gauge action write. -/
def fixedP506L0FinalCommonActionActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonPreECActionActual space)

/-! ## Literal primitive-field dependency ledger -/

@[simp] theorem fixedP506L0FinalCommonActionActual_coframe
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).coframe =
      (recenteredCartanRepairedScalarSecondJetActual space).coframe := by
  unfold fixedP506L0FinalCommonActionActual
    fixedP506L0FinalCommonPreECActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    formNativeCurrentP286CompleteActionResponseOperator_coframe]

@[simp] theorem fixedP506L0FinalCommonActionActual_gaugeConnection
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gaugeConnection =
      (recenteredCartanRepairedScalarSecondJetActual space).gaugeConnection := by
  unfold fixedP506L0FinalCommonActionActual
    fixedP506L0FinalCommonPreECActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection,
    formNativeCurrentP286CompleteActionResponseOperator_gaugeConnection]

@[simp] theorem fixedP506L0FinalCommonActionActual_gaugeAuxiliary
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gaugeAuxiliary =
      (fixedP506L0FinalCommonPreECActionActual space).gaugeAuxiliary := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary]

@[simp] theorem fixedP506L0FinalCommonActionActual_scalar
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).scalar =
      (recenteredCartanRepairedScalarSecondJetActual space).scalar := by
  unfold fixedP506L0FinalCommonActionActual
    fixedP506L0FinalCommonPreECActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    formNativeCurrentP286CompleteActionResponseOperator_scalar]

@[simp] theorem fixedP506L0FinalCommonActionActual_matter
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).matter =
      (recenteredCartanRepairedScalarSecondJetActual space).matter := by
  unfold fixedP506L0FinalCommonActionActual
    fixedP506L0FinalCommonPreECActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    formNativeCurrentP286CompleteActionResponseOperator_matter]

@[simp] theorem fixedP506L0FinalCommonActionActual_conjugateMatter
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).conjugateMatter =
      (recenteredCartanRepairedScalarSecondJetActual space).conjugateMatter := by
  unfold fixedP506L0FinalCommonActionActual
    fixedP506L0FinalCommonPreECActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    formNativeCurrentP286CompleteActionResponseOperator_conjugateMatter]

@[simp] theorem fixedP506L0FinalCommonActionActual_coframe_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).coframe =
      (fixedP506L0FinalCommonPreECActionActual space).coframe := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe]

@[simp] theorem fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gaugeConnection =
      (fixedP506L0FinalCommonPreECActionActual space).gaugeConnection := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]

@[simp] theorem fixedP506L0FinalCommonActionActual_scalar_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).scalar =
      (fixedP506L0FinalCommonPreECActionActual space).scalar := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar]

@[simp] theorem fixedP506L0FinalCommonActionActual_matter_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).matter =
      (fixedP506L0FinalCommonPreECActionActual space).matter := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter]

@[simp] theorem fixedP506L0FinalCommonActionActual_conjugateMatter_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).conjugateMatter =
      (fixedP506L0FinalCommonPreECActionActual space).conjugateMatter := by
  unfold fixedP506L0FinalCommonActionActual
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter]

theorem fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gravityConnection 0 =
      (fixedP506L0FinalCommonPreECActionActual space).gravityConnection 0 := by
  exact sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
    positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonPreECActionActual space)

theorem fixedP506L0FinalCommonPreECActionActual_coframe_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).coframe 0 = 1 := by
  unfold fixedP506L0FinalCommonPreECActionActual
  rw [formNativeCurrentP286CompleteActionResponseOperator_coframe]
  exact recenteredCartanRepairedConstitutiveCurrent_coframe_origin space

theorem fixedP506L0FinalCommonActionActual_coframe_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).coframe 0 = 1 := by
  rw [fixedP506L0FinalCommonActionActual_coframe]
  exact recenteredCartanRepairedConstitutiveCurrent_coframe_origin space

/-! ## Direct producer-soundness already supplied by the component actions -/

theorem fixedP506L0FinalCommonPreECActionActual_p286ConnectionEquation_origin
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        (fixedP506L0FinalCommonPreECActionActual space) 0 = 0 := by
  exact formNativeCurrentP286CompleteActionResponseOperator_connectionEquation_origin
    positiveSmoothUnifiedSource
    (recenteredCartanRepairedScalarSecondJetActual space)

private theorem
    fixedP506L0FinalCommonPreECActionActual_actionCartanConnection_origin_eq_recentered
    (space : StageNineSpatialPoint) :
    diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space) 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (recenteredCartanRepairedConstitutiveCurrent space) 0 := by
  have spinEq :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual space)
      (recenteredCartanRepairedConstitutiveCurrent space) 0
      (congrFun
        (fixedP506L0FinalCommonPreECActionActual_coframe_eq_recentered space) 0)
      (congrFun
        (fixedP506L0FinalCommonPreECActionActual_matter_eq_recentered space) 0)
      (congrFun
        (fixedP506L0FinalCommonPreECActionActual_conjugateMatter_eq_recentered
          space) 0)
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [fixedP506L0FinalCommonPreECActionActual_coframe_eq_recentered, spinEq]

theorem fixedP506L0FinalCommonPreECActionActual_connection_selfGenerated_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonPreECActionActual space).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space) 0 := by
  calc
    (fixedP506L0FinalCommonPreECActionActual space).gravityConnection 0 =
        (recenteredCartanRepairedConstitutiveCurrent space
          ).gravityConnection 0 := by
      rw [
        fixedP506L0FinalCommonPreECActionActual_gravityConnection_eq_recentered]
    _ = diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent space) 0 :=
      recenteredCartanRepairedConstitutiveCurrent_connection_selfGenerated_origin
        space
    _ = diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonPreECActionActual space) 0 :=
      (fixedP506L0FinalCommonPreECActionActual_actionCartanConnection_origin_eq_recentered
        space).symm

theorem fixedP506L0FinalCommonActionActual_connection_selfGenerated_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) 0 := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connectionSelfGenerated_zero
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual space)
      (fixedP506L0FinalCommonPreECActionActual_connection_selfGenerated_origin
        space)

theorem fixedP506L0FinalCommonActionActual_torsionSpin_origin
    (space : StageNineSpatialPoint) :
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          ((fixedP506L0FinalCommonActionActual space).coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              (fixedP506L0FinalCommonActionActual space).coframe 0)
            ((fixedP506L0FinalCommonActionActual space
              ).gravityConnection 0))) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            (fixedP506L0FinalCommonActionActual space)) 0) := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_torsionSpin_zero
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual space)
      (by
        rw [fixedP506L0FinalCommonPreECActionActual_coframe_origin]
        norm_num)
      (fixedP506L0FinalCommonPreECActionActual_connection_selfGenerated_origin
        space)

theorem fixedP506L0FinalCommonActionActual_coframe_contDiff
    (space : StageNineSpatialPoint) :
    ContDiff ℝ ∞ (fixedP506L0FinalCommonActionActual space).coframe := by
  rw [fixedP506L0FinalCommonActionActual_coframe,
    recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_coframe]
  exact recenteredCartanRepairedConstitutiveCurrent_coframe_contDiff space

private theorem
    gravityAuxiliaryDirectionalDerivative_restrictToIIPlus_of_coframeContDiff
    (configuration : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ configuration.coframe)
    (point : BasePoint) (direction : LorentzianIndex) :
    gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction =
      physicalIIPlusCoframeTangent (configuration.coframe point)
        ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
          direction) := by
  have iiPlusSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate) :=
    physicalIIPlusBivector_contDiff.comp coframeSmooth
  have componentSmooth :
      ∀ internal coordinate,
        ContDiff ℝ ∞ fun candidate =>
          configuration.coframe candidate internal coordinate := by
    intro internal coordinate
    exact contDiff_pi.mp (contDiff_pi.mp coframeSmooth internal) coordinate
  funext internalPair spacetimePair
  have internalPairSmooth : ContDiff ℝ ∞ fun candidate =>
      physicalIIPlusBivector (configuration.coframe candidate)
        internalPair :=
    contDiff_pi.mp iiPlusSmooth internalPair
  calc
    (gravityAuxiliaryDirectionalDerivative
        (restrictHolonomicConfigurationToIIPlus configuration)
        point direction) internalPair spacetimePair =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate))
        point direction) internalPair spacetimePair := rfl
    _ =
      (fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair)
        point direction) spacetimePair := by
      rw [fieldDirectionalDerivative_pi_apply
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate))
        iiPlusSmooth point direction internalPair]
    _ = fieldDirectionalDerivative
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair spacetimePair)
        point direction := by
      rw [fieldDirectionalDerivative_pi_apply
        (fun candidate =>
          physicalIIPlusBivector (configuration.coframe candidate)
            internalPair)
        internalPairSmooth point direction spacetimePair]
    _ = physicalIIPlusCoframeTangent (configuration.coframe point)
          (coframeFieldDirectionalTangent configuration.coframe point
            direction)
        internalPair spacetimePair :=
      physicalIIPlusBivector_fieldDirectionalDerivative
        configuration.coframe componentSmooth point direction internalPair
          spacetimePair
    _ = physicalIIPlusCoframeTangent (configuration.coframe point)
          ((holonomicCoframeFirstJetAt configuration.coframe point).derivative
            direction)
        internalPair spacetimePair := by
      rfl

private theorem pointwisePhysicalBivectorJet_eq_of_fields_eq_local
    (first second : PointwisePhysicalBivectorJet)
    (value : first.value = second.value)
    (derivative : first.derivative = second.derivative) :
    first = second := by
  cases first with
  | mk firstValue firstDerivative =>
      cases second with
      | mk secondValue secondDerivative =>
          change firstValue = secondValue at value
          change firstDerivative = secondDerivative at derivative
          subst secondValue
          subst secondDerivative
          rfl

private theorem
    holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
    (configuration : StageNineHolonomicConfiguration)
    (coframeSmooth : ContDiff ℝ ∞ configuration.coframe)
    (point : BasePoint) :
    holonomicGravityAuxiliaryJet
        (restrictHolonomicConfigurationToIIPlus configuration) point =
      pointwisePhysicalIIPlusJet
        (holonomicCoframeFirstJetAt configuration.coframe point) := by
  apply pointwisePhysicalBivectorJet_eq_of_fields_eq_local
  · rfl
  · funext direction
    exact
      gravityAuxiliaryDirectionalDerivative_restrictToIIPlus_of_coframeContDiff
        configuration coframeSmooth point direction

private theorem fixedP506L0FinalCommonActionActual_restrictToIIPlus
    (space : StageNineSpatialPoint) :
    restrictHolonomicConfigurationToIIPlus
        (fixedP506L0FinalCommonActionActual space) =
      fixedP506L0FinalCommonActionActual space := by
  exact
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      (fixedP506L0FinalCommonActionActual space)).2
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonPreECActionActual space))

private theorem fixedP506L0FinalCommonActionActual_lorentzSkew_origin
    (space : StageNineSpatialPoint) :
    LorentzSkew
      ((fixedP506L0FinalCommonActionActual space).gravityConnection 0) := by
  rw [fixedP506L0FinalCommonActionActual_connection_selfGenerated_origin]
  apply diracDualFormNativeActionCartanConnectionAt_lorentzSkew
  rw [fixedP506L0FinalCommonActionActual_coframe_origin]
  norm_num

private theorem
    fixedP506L0FinalCommonActionActual_gravityAuxiliaryExteriorCovariantDerivative_origin_eq_torsion
    (space : StageNineSpatialPoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) 0 =
      internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          ((fixedP506L0FinalCommonActionActual space).coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              (fixedP506L0FinalCommonActionActual space).coframe 0)
            ((fixedP506L0FinalCommonActionActual space
              ).gravityConnection 0))) := by
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative
          (fixedP506L0FinalCommonActionActual space) 0 =
        holonomicGravityAuxiliaryExteriorCovariantDerivative
          (restrictHolonomicConfigurationToIIPlus
            (fixedP506L0FinalCommonActionActual space)) 0 := by
      rw [fixedP506L0FinalCommonActionActual_restrictToIIPlus]
    _ = internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            ((fixedP506L0FinalCommonActionActual space).coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                (fixedP506L0FinalCommonActionActual space).coframe 0)
              ((fixedP506L0FinalCommonActionActual space
                ).gravityConnection 0))) := by
      change
        pointwisePhysicalBivectorExteriorCovariantDerivative
            ((fixedP506L0FinalCommonActionActual space).gravityConnection 0)
            (holonomicGravityAuxiliaryJet
              (restrictHolonomicConfigurationToIIPlus
                (fixedP506L0FinalCommonActionActual space)) 0) = _
      rw [
        holonomicGravityAuxiliaryJet_restrictToIIPlus_of_coframeContDiff
          (fixedP506L0FinalCommonActionActual space)
          (fixedP506L0FinalCommonActionActual_coframe_contDiff space) 0]
      exact
        pointwisePhysicalIIPlus_exteriorCovariantDerivative_eq_torsionCoframe
          (holonomicCoframeFirstJetAt
            (fixedP506L0FinalCommonActionActual space).coframe 0)
          ((fixedP506L0FinalCommonActionActual space).gravityConnection 0)
          (fixedP506L0FinalCommonActionActual_lorentzSkew_origin space)

theorem fixedP506L0FinalCommonActionActual_lorentzEquation_origin_zero
    (space : StageNineSpatialPoint) :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        (fixedP506L0FinalCommonActionActual space) 0 = 0 := by
  apply
    (holonomicFormNativeLorentzEulerThreeForm_eq_zero_iff_current
      positiveSmoothUnifiedSource 0
      (fixedP506L0FinalCommonActionActual space) 0).2
  calc
    holonomicGravityAuxiliaryExteriorCovariantDerivative
          (fixedP506L0FinalCommonActionActual space) 0 =
        internalBivectorDualThreeForm
          (torsionCoframeWedgeThreeForm
            ((fixedP506L0FinalCommonActionActual space).coframe 0)
            (pointwiseCartanTorsion
              (holonomicCoframeFirstJetAt
                (fixedP506L0FinalCommonActionActual space).coframe 0)
              ((fixedP506L0FinalCommonActionActual space
                ).gravityConnection 0))) :=
      fixedP506L0FinalCommonActionActual_gravityAuxiliaryExteriorCovariantDerivative_origin_eq_torsion
        space
    _ = formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus
              (fixedP506L0FinalCommonActionActual space)) 0) :=
      fixedP506L0FinalCommonActionActual_torsionSpin_origin space
    _ = formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            (fixedP506L0FinalCommonActionActual space) 0) := by
      rw [fixedP506L0FinalCommonActionActual_restrictToIIPlus]

theorem fixedP506L0FinalCommonActionActual_simplicity
    (space : StageNineSpatialPoint) :
    FormNativeGravitySimplicityEquation
      (fixedP506L0FinalCommonActionActual space) := by
  exact sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
    positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonPreECActionActual space)

theorem fixedP506L0FinalCommonActionActual_gravityAuxiliaryEquation
    (space : StageNineSpatialPoint) :
    FormNativeGravityAuxiliaryEquation
      (fixedP506L0FinalCommonActionActual space) := by
  exact sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
    positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonPreECActionActual space)

theorem fixedP506L0FinalCommonActionActual_ECCovector_zero
    (space : StageNineSpatialPoint) :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            (fixedP506L0FinalCommonActionActual space) 0) +
        diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
          (fixedP506L0FinalCommonActionActual space) = 0 := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_EC_covector_zero
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual space)

theorem fixedP506L0FinalCommonActionActual_fullCoframeEuler_zero
    (space : StageNineSpatialPoint) :
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0) =
      0 := by
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_fullCoframeEuler_zero
      positiveSmoothUnifiedSource
      (fixedP506L0FinalCommonPreECActionActual space)
      (fixedP506L0FinalCommonPreECActionActual_coframe_origin space)

/-! ## Scalar action leg after the later gauge and EC writes -/

private theorem fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_eq
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) =
      holonomicScalarCovariantDerivative
        (recenteredCartanRepairedScalarSecondJetActual space) := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [fixedP506L0FinalCommonActionActual_scalar,
    fixedP506L0FinalCommonActionActual_gaugeConnection]

private theorem fixedP506L0FinalCommonActionActual_scalarMomentum_eq
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction
        derivativeDirection =
      scalarDifferentialMomentum positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) direction
        derivativeDirection := by
  funext point
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_coframe,
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_eq]

private theorem fixedP506L0FinalCommonActionActual_scalarDivergence_eq
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) direction := by
  funext point
  unfold scalarDifferentialMomentumDivergence
  simp_rw [fixedP506L0FinalCommonActionActual_scalarMomentum_eq]

private theorem fixedP506L0FinalCommonActionActual_scalarAlgebraic_origin_eq
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 =
      diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space) direction 0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarVariationAlgebraicDirection
    generatedVolumeDensity
    StageNineScalarVariation.scalarPotentialFirstVariation
    diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_coframe,
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_eq,
    fixedP506L0FinalCommonActionActual_gaugeConnection,
    fixedP506L0FinalCommonActionActual_scalar,
    fixedP506L0FinalCommonActionActual_matter,
    fixedP506L0FinalCommonActionActual_conjugateMatter]

theorem fixedP506L0FinalCommonActionActual_scalarEuler_origin_zero
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        (fixedP506L0FinalCommonActionActual space) direction 0 = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [fixedP506L0FinalCommonActionActual_scalarAlgebraic_origin_eq,
    congrFun (fixedP506L0FinalCommonActionActual_scalarDivergence_eq
      space direction) 0]
  exact
    recenteredCartanRepairedScalarSecondJetActual_diracDualScalarEulerLagrange_origin_zero
      space direction

/-! ## Algebraic and gauge action preservation at the common contact -/

theorem recenteredCartanRepairedConstitutiveCurrent_liveGaugeAuxiliary_origin
    (space : StageNineSpatialPoint) :
    (recenteredCartanRepairedConstitutiveCurrent space).gaugeAuxiliary 0 =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        ((recenteredCartanRepairedConstitutiveCurrent space).coframe 0)
        (holonomicGaugeCurvature
          (recenteredCartanRepairedConstitutiveCurrent space) 0) := by
  rfl

theorem fixedP506L0FinalCommonActionActual_liveGaugeAuxiliary_origin
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).gaugeAuxiliary 0 =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        ((fixedP506L0FinalCommonActionActual space).coframe 0)
        (holonomicGaugeCurvature
          (fixedP506L0FinalCommonActionActual space) 0) := by
  calc
    (fixedP506L0FinalCommonActionActual space).gaugeAuxiliary 0 =
        (fixedP506L0FinalCommonPreECActionActual space).gaugeAuxiliary 0 := by
      rw [fixedP506L0FinalCommonActionActual_gaugeAuxiliary]
    _ = (recenteredCartanRepairedScalarSecondJetActual space
        ).gaugeAuxiliary 0 :=
      formNativeCurrentP286CompleteActionResponseOperator_gaugeAuxiliary_origin
        positiveSmoothUnifiedSource
        (recenteredCartanRepairedScalarSecondJetActual space)
    _ = (recenteredCartanRepairedConstitutiveCurrent space
        ).gaugeAuxiliary 0 := by
      rw [recenteredCartanRepairedScalarSecondJetActual,
        installScalarQuadraticTimeCorrection_gaugeAuxiliary]
    _ = formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          ((recenteredCartanRepairedConstitutiveCurrent space).coframe 0)
          (holonomicGaugeCurvature
            (recenteredCartanRepairedConstitutiveCurrent space) 0) :=
      recenteredCartanRepairedConstitutiveCurrent_liveGaugeAuxiliary_origin
        space
    _ = formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          ((fixedP506L0FinalCommonActionActual space).coframe 0)
          (holonomicGaugeCurvature
            (fixedP506L0FinalCommonActionActual space) 0) := by
      rw [fixedP506L0FinalCommonActionActual_coframe,
        recenteredCartanRepairedScalarSecondJetActual,
        installScalarQuadraticTimeCorrection_coframe]
      rw [holonomicGaugeCurvature_eq_of_connection_eq_current
        (fixedP506L0FinalCommonActionActual space)
        (recenteredCartanRepairedScalarSecondJetActual space)
        (fixedP506L0FinalCommonActionActual_gaugeConnection space) 0]
      rw [holonomicGaugeCurvature_eq_of_connection_eq_current
        (recenteredCartanRepairedScalarSecondJetActual space)
        (recenteredCartanRepairedConstitutiveCurrent space)
        (installScalarQuadraticTimeCorrection_gaugeConnection _ _) 0]

theorem fixedP506L0FinalCommonActionActual_p286GaugeAuxiliaryEquation_origin
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0) := by
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)
      (by
        change Matrix.det
          ((fixedP506L0FinalCommonActionActual space).coframe 0) ≠ 0
        rw [fixedP506L0FinalCommonActionActual_coframe_origin]
        norm_num)).2
  exact fixedP506L0FinalCommonActionActual_liveGaugeAuxiliary_origin space

private theorem
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_origin_eq_preEC
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) 0 =
      holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual space) 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [fixedP506L0FinalCommonActionActual_scalar_eq_preEC,
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_matterCovariantDerivative_origin_eq_preEC
    (space : StageNineSpatialPoint) :
    holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) 0 =
      holonomicMatterCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual space) 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [fixedP506L0FinalCommonActionActual_matter_eq_preEC,
    fixedP506L0FinalCommonActionActual_gravityConnection_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]

private theorem fixedP506L0FinalCommonActionActual_volume_origin_eq_preEC
    (space : StageNineSpatialPoint) :
    generatedVolumeDensity
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0) =
      generatedVolumeDensity
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_scalarGaugeKinetic_origin_eq_preEC
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)
        variation =
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_preEC,
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_origin_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_pointwiseScalarGaugeVariation_origin_eq_preEC
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)
        direction =
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_scalar_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_pointwiseMatterGaugeVariation_origin_eq_preEC
    (space : StageNineSpatialPoint)
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)
        direction =
      pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_matter_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_matterGaugeKinetic_origin_eq_preEC
    (space : StageNineSpatialPoint)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)
        variation =
      matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [toContinuumPointField]
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_preEC,
    fixedP506L0FinalCommonActionActual_conjugateMatter_eq_preEC]

private theorem fixedP506L0FinalCommonActionActual_chargedGaugeThreeForm_eq_preEC
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (fixedP506L0FinalCommonPreECActionActual space) 0) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [fixedP506L0FinalCommonActionActual_volume_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_pointwiseScalarGaugeVariation_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_pointwiseMatterGaugeVariation_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_scalarGaugeKinetic_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_matterGaugeKinetic_origin_eq_preEC]

private theorem
    fixedP506L0FinalCommonActionActual_p286AuxiliaryExteriorCovariantDerivative_origin_eq_preEC
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (fixedP506L0FinalCommonActionActual space) 0 =
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        (fixedP506L0FinalCommonPreECActionActual space) 0 := by
  have connectionEq :
      holonomicP286GaugeConnectionCoordinate
          (fixedP506L0FinalCommonActionActual space) 0 =
        holonomicP286GaugeConnectionCoordinate
          (fixedP506L0FinalCommonPreECActionActual space) 0 := by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [fixedP506L0FinalCommonActionActual_gaugeConnection_eq_preEC]
  have auxiliaryEq :
      holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0FinalCommonActionActual space) =
        holonomicP286GaugeAuxiliaryCoordinate
          (fixedP506L0FinalCommonPreECActionActual space) := by
    funext point pair
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [fixedP506L0FinalCommonActionActual_gaugeAuxiliary]
  have derivativeEq :
      p286GaugeAuxiliaryDirectionalDerivative
          (fixedP506L0FinalCommonActionActual space) 0 =
        p286GaugeAuxiliaryDirectionalDerivative
          (fixedP506L0FinalCommonPreECActionActual space) 0 := by
    unfold p286GaugeAuxiliaryDirectionalDerivative
    rw [auxiliaryEq]
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  rw [connectionEq, congrFun auxiliaryEq 0, derivativeEq]

theorem fixedP506L0FinalCommonActionActual_p286ConnectionEquation_origin
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        (fixedP506L0FinalCommonActionActual space) 0 = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [
    fixedP506L0FinalCommonActionActual_p286AuxiliaryExteriorCovariantDerivative_origin_eq_preEC,
    fixedP506L0FinalCommonActionActual_chargedGaugeThreeForm_eq_preEC]
  exact fixedP506L0FinalCommonPreECActionActual_p286ConnectionEquation_origin
    space

/-! ## Authoritative whole-carrier readout -/

/-- The complete nine-channel residual is evaluated only after the common
write has generated its final actual. -/
def fixedP506L0FinalCommonActionResidual
    (space : StageNineSpatialPoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
    (fixedP506L0FinalCommonActionActual space) 0

theorem fixedP506L0FinalCommonActionResidual_gravityMultiplier_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0) = 0
  apply
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField (fixedP506L0FinalCommonActionActual space) 0)).2
  exact fixedP506L0FinalCommonActionActual_simplicity space 0

theorem fixedP506L0FinalCommonActionResidual_gravityAuxiliary_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).gravityAuxiliary = 0 := by
  change
    holonomicFormNativeGravityAuxiliaryEulerResidual
      (fixedP506L0FinalCommonActionActual space) 0 = 0
  exact congrFun (fixedP506L0FinalCommonActionActual_gravityAuxiliaryEquation space) 0

theorem fixedP506L0FinalCommonActionResidual_lorentzConnection_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).lorentzConnection = 0 := by
  exact fixedP506L0FinalCommonActionActual_lorentzEquation_origin_zero space

theorem fixedP506L0FinalCommonActionResidual_p286GaugeAuxiliary_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).p286GaugeAuxiliary = 0 := by
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        (fixedP506L0FinalCommonActionActual space) 0)).2
  exact
    fixedP506L0FinalCommonActionActual_p286GaugeAuxiliaryEquation_origin space

theorem fixedP506L0FinalCommonActionResidual_p286GaugeConnection_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).p286GaugeConnection = 0 := by
  exact fixedP506L0FinalCommonActionActual_p286ConnectionEquation_origin space

theorem fixedP506L0FinalCommonActionResidual_scalar_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).scalar = 0 := by
  funext direction
  exact fixedP506L0FinalCommonActionActual_scalarEuler_origin_zero
    space direction

theorem fixedP506L0FinalCommonActionResidual_coframe_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionResidual space).coframe = 0 := by
  exact fixedP506L0FinalCommonActionActual_fullCoframeEuler_zero space

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite

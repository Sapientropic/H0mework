import H0mework.Physics.FinalJoint.FixedPointwiseJointResidualNormalForm
import H0mework.Physics.FixedJoint.FixedConstitutiveZeroFiber

/-!
# Fixed P506/L0 final P286 affine identification

At the fixed `space = 0` P506/L0 lineage, this module identifies the
action-generated final P286 auxiliary affine field with the already generated
solved auxiliary field.  The chain is

```text
same-source contact action current
→ required exterior target `![Q, 0, 0, -Q]`
→ canonical affine auxiliary write
→ literal equality with the solved auxiliary normal form
→ reuse of the solved auxiliary Euler residual coordinate.
```

This is an action-provenance identification/readout.  No residual coordinate,
support, sign, branch, target field, zero-fiber certificate, or endpoint is
accepted by a producer, and no residual is inverted into a write.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveZeroFiber
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionRecenterPointFieldNaturality
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286CompleteActionResponseOperator
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaussRadialSecondJetLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev Q : P286CoordinateCarrier :=
  positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge

private abbrev InputActual : StageNineHolonomicConfiguration :=
  recenteredCartanRepairedScalarSecondJetActual 0

private abbrev OldActual : StageNineHolonomicConfiguration :=
  FixedP506FormNativeConstitutiveJointActionSuccessor

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem input_coframe_eq_old :
    InputActual.coframe = OldActual.coframe := by
  unfold InputActual
  rw [recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_coframe,
    recenteredCartanRepairedConstitutiveCurrent_coframe,
    recenteredContactActual,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_coframe,
    spatiallyRecenterHolonomicConfiguration_zero,
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe]

private theorem input_gaugeConnection_eq_old :
    InputActual.gaugeConnection = OldActual.gaugeConnection := by
  unfold InputActual
  rw [recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_gaugeConnection,
    recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
    recenteredContactActual,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
    spatiallyRecenterHolonomicConfiguration_zero,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

private theorem input_scalar_origin_eq_old :
    InputActual.scalar 0 = OldActual.scalar 0 := by
  unfold InputActual
  rw [recenteredCartanRepairedScalarSecondJetActual,
    installScalarQuadraticTimeCorrection_scalar_origin,
    recenteredCartanRepairedConstitutiveCurrent_scalar,
    recenteredContactActual,
    diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
    spatiallyRecenterHolonomicConfiguration_zero,
    fixedP506FormNativeConstitutiveJointActionSuccessor_scalar]

private theorem input_scalarCovariantDerivative_origin_eq_old :
    holonomicScalarCovariantDerivative InputActual 0 =
      holonomicScalarCovariantDerivative OldActual 0 := by
  calc
    holonomicScalarCovariantDerivative InputActual 0 =
        holonomicScalarCovariantDerivative
          (recenteredCartanRepairedConstitutiveCurrent 0) 0 := by
      exact congrArg StageNineContinuumPointField.scalarCovariantDerivative
        (recenteredCartanRepairedScalarSecondJetActual_pointField_origin 0)
    _ = holonomicScalarCovariantDerivative OldActual 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [recenteredCartanRepairedConstitutiveCurrent_scalar,
        recenteredCartanRepairedConstitutiveCurrent_gaugeConnection,
        recenteredContactActual,
        diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_scalar,
        diracDualFormNativeRepairedConstitutiveJointActionResponseOperator_gaugeConnection,
        spatiallyRecenterHolonomicConfiguration_zero,
        fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

private theorem input_matter_origin_eq_old :
    InputActual.matter 0 = OldActual.matter 0 := by
  calc
    InputActual.matter 0 =
        (recenteredCartanRepairedConstitutiveCurrent 0).matter 0 := by
      unfold InputActual recenteredCartanRepairedScalarSecondJetActual
      rw [installScalarQuadraticTimeCorrection_matter]
    _ = (fixedP506L0CartanRestartActual 0).matter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_matter_origin_eq_cartan 0
    _ = FixedP506FormNativeJointActionSolvedSuccessor.matter 0 := by
      unfold fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter,
        spatiallyRecenterHolonomicConfiguration_zero]
    _ = OldActual.matter 0 := by
      exact
        fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin.symm

private theorem input_conjugateMatter_origin_eq_old :
    InputActual.conjugateMatter 0 = OldActual.conjugateMatter 0 := by
  calc
    InputActual.conjugateMatter 0 =
        (recenteredCartanRepairedConstitutiveCurrent 0).conjugateMatter 0 := by
      unfold InputActual recenteredCartanRepairedScalarSecondJetActual
      rw [installScalarQuadraticTimeCorrection_conjugateMatter]
    _ = (fixedP506L0CartanRestartActual 0).conjugateMatter 0 :=
      recenteredCartanRepairedConstitutiveCurrent_conjugateMatter_origin_eq_cartan 0
    _ = FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter 0 := by
      unfold fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
      rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter,
        spatiallyRecenterHolonomicConfiguration_zero]
    _ = OldActual.conjugateMatter 0 := by
      exact
        fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin.symm

private theorem input_volume_origin_eq_old :
    generatedVolumeDensity (toContinuumPointField InputActual 0) =
      generatedVolumeDensity (toContinuumPointField OldActual 0) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [input_coframe_eq_old]

private theorem input_scalarGaugeKinetic_origin_eq_old
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField InputActual 0) variation =
      scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField OldActual 0) variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [toContinuumPointField]
  rw [input_coframe_eq_old,
    input_scalarCovariantDerivative_origin_eq_old]

private theorem input_pointwiseScalarGaugeVariation_origin_eq_old
    (direction : P286GaugeOneForm) :
    pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField InputActual 0) direction =
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField OldActual 0) direction := by
  funext formDirection
  unfold pointwiseScalarP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [input_scalar_origin_eq_old]

private theorem input_pointwiseMatterGaugeVariation_origin_eq_old
    (direction : P286GaugeOneForm) :
    pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField InputActual 0) direction =
      pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField OldActual 0) direction := by
  funext formDirection
  unfold pointwiseMatterP286GaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [input_matter_origin_eq_old]

private theorem input_matterGaugeKinetic_origin_eq_old
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField InputActual 0) variation =
      matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 0
        (toContinuumPointField OldActual 0) variation := by
  unfold matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [toContinuumPointField]
  rw [input_coframe_eq_old, input_conjugateMatter_origin_eq_old]

private theorem input_chargedGaugeThreeForm_origin_eq_old :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField InputActual 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField OldActual 0) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [input_volume_origin_eq_old,
    input_pointwiseScalarGaugeVariation_origin_eq_old,
    input_pointwiseMatterGaugeVariation_origin_eq_old,
    input_scalarGaugeKinetic_origin_eq_old,
    input_matterGaugeKinetic_origin_eq_old]

private theorem input_physicalChargedGaugeCurrent_origin_eq_old :
    formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField InputActual 0) =
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField OldActual 0) := by
  unfold formNativePhysicalChargedGaugeCurrentThreeForm
  rw [input_chargedGaugeThreeForm_origin_eq_old]

private theorem input_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate InputActual 0 = 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [input_gaugeConnection_eq_old]
  exact
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero

private theorem zeroConnectionExteriorAction
    (value : P286GaugeTwoForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction 0 value = 0 := by
  have adjointZero : p286GaugeTwoFormAdjoint 0 value = 0 := by
    funext pair
    simp [p286GaugeTwoFormAdjoint]
  funext triple
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  rw [adjointZero]
  simp

private theorem oldExteriorDerivative_eq_physicalCurrent :
    holonomicP286GaugeAuxiliaryExteriorDerivative OldActual 0 =
      formNativePhysicalChargedGaugeCurrentThreeForm
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField OldActual 0) := by
  have equationZero :
      holonomicFormNativeP286GaugeEulerThreeForm
          positiveSmoothUnifiedSource 0 OldActual 0 = 0 := by
    change
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
        ).p286GaugeConnection = 0
    exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_origin_zero
  have covariant :=
    (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_current
      positiveSmoothUnifiedSource 0 OldActual 0).1 equationZero
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero,
    zeroConnectionExteriorAction, add_zero] at covariant
  exact covariant

private theorem oldFirstJet_eq_canonicalQ :
    (fun direction =>
      fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
        (coordinateDirection direction)) =
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm
        ![Q, 0, 0, -Q] := by
  funext direction pair
  fin_cases direction <;> fin_cases pair <;>
    simp [fixedP506FormNativeJointActionAuxiliaryFirstJetLinear,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      fixedP506FormNativeSpatialVelocity_eq_neg_U7,
      fixedP506FormNativeGaussCharge_eq_neg_U7,
      currentSpatialAuxiliaryVelocity_eq_thirdNegCharge,
      p286SpatialAuxiliaryVelocityEmbedding, p286SpatialThirdOnly,
      p286GaussRadialAuxiliaryFirstJetLinear,
      p286GaussAuxiliaryAxisEmbedding, p286BaseCoordinate_apply,
      localBaseCoordinate_apply, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three,
      canonicalP286EqualAxisCoefficient_eq_one_third]

/-- Exact pure P286 exterior derivative carried by the fixed constitutive
successor at the common source-owned origin. -/
theorem fixedP506L0ConstitutiveP286ExteriorDerivative_origin_normalForm :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      ![Q, 0, 0, -Q] := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      fun direction =>
        fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
          (coordinateDirection direction) by
    funext direction
    exact
      fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative
        direction]
  rw [oldFirstJet_eq_canonicalQ]
  exact
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_canonical _

private theorem fixedP506L0RequiredExteriorDerivative_origin_normalForm :
    formNativeCurrentP286RequiredExteriorDerivative
        positiveSmoothUnifiedSource InputActual =
      ![Q, 0, 0, -Q] := by
  calc
    formNativeCurrentP286RequiredExteriorDerivative
          positiveSmoothUnifiedSource InputActual =
        formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField InputActual 0) := by
      unfold formNativeCurrentP286RequiredExteriorDerivative
      rw [input_gaugeConnectionCoordinate_origin_zero,
        zeroConnectionExteriorAction, sub_zero]
    _ = formNativePhysicalChargedGaugeCurrentThreeForm
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField OldActual 0) :=
      input_physicalChargedGaugeCurrent_origin_eq_old
    _ = holonomicP286GaugeAuxiliaryExteriorDerivative OldActual 0 :=
      oldExteriorDerivative_eq_physicalCurrent.symm
    _ = ![Q, 0, 0, -Q] :=
      fixedP506L0ConstitutiveP286ExteriorDerivative_origin_normalForm

theorem fixedP506L0FinalCommonActionActual_p286ExteriorDerivative_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (fixedP506L0FinalCommonActionActual 0) point =
      ![Q, 0, 0, -Q] := by
  rw [StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm.fixedP506L0FinalCommonActionActual_p286ExteriorDerivative_normalForm]
  exact fixedP506L0RequiredExteriorDerivative_origin_normalForm

private theorem input_gaugeAuxiliary_origin_eq_solved :
    InputActual.gaugeAuxiliary 0 =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary 0 := by
  unfold InputActual recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_gaugeAuxiliary]
  change
    diracDualFormNativeConstitutiveAuxiliaryField
        positiveSmoothUnifiedSource
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
          positiveSmoothUnifiedSource
          (spatiallyRecenterHolonomicConfiguration
            FixedP506FormNativeJointActionSolvedSuccessor 0)) 0 = _
  rw [spatiallyRecenterHolonomicConfiguration_zero]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor)
    FixedP506FormNativeJointActionSolvedSuccessor
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_gaugeConnection
      positiveSmoothUnifiedSource
      FixedP506FormNativeJointActionSolvedSuccessor) 0]
  change fixedP506FormNativeConstitutiveAuxiliaryField 0 = _
  simpa only [canonicalCauchySlicePoint_zero_zero_local] using
      (fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice
        (0 : StageNineSpatialPoint))

private theorem input_originAuxiliaryCoordinate_normalForm :
    currentP286OriginAuxiliaryCoordinate InputActual =
      c3h181FullAuxiliaryCoordinateNormalForm 0 := by
  change
    holonomicP286GaugeAuxiliaryCoordinate InputActual 0 =
      c3h181FullAuxiliaryCoordinateNormalForm 0
  calc
    holonomicP286GaugeAuxiliaryCoordinate InputActual 0 =
        holonomicP286GaugeAuxiliaryCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor 0 := by
      funext pair
      unfold holonomicP286GaugeAuxiliaryCoordinate
      rw [input_gaugeAuxiliary_origin_eq_solved]
    _ = c3h181FullAuxiliaryCoordinateNormalForm 0 :=
      by
        simpa only [neg_zero] using
          (fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm
            0)

private theorem canonicalQIncrement_eq_reflectedOldIncrement
    (point : BasePoint) :
    c3h181FullAuxiliaryCoordinateNormalForm 0 +
        formNativeP286CanonicalAuxiliaryIncrement ![Q, 0, 0, -Q] point =
      c3h181FullAuxiliaryCoordinateNormalForm (-point) := by
  funext pair
  fin_cases pair <;>
    simp [c3h181FullAuxiliaryCoordinateNormalForm,
      formNativeP286CanonicalAuxiliaryIncrement,
      formNativeP286CanonicalAuxiliaryDerivativeOfThreeForm,
      localBaseCoordinate_apply, canonicalLorentzianTimeDirection,
      canonicalP286EqualAxisCoefficient_eq_one_third,
      Fin.sum_univ_four] <;>
    module

private theorem fixedP506L0FinalCommonActionActual_auxiliaryCoordinate_eq_solved
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (fixedP506L0FinalCommonActionActual 0) point =
      holonomicP286GaugeAuxiliaryCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point := by
  rw [StageNineDiracDualFormNativeFixedP506FinalCommonPointwiseJointResidualNormalForm.fixedP506L0FinalCommonActionActual_gaugeAuxiliaryCoordinate_normalForm]
  rw [fixedP506L0RequiredExteriorDerivative_origin_normalForm,
    input_originAuxiliaryCoordinate_normalForm,
    canonicalQIncrement_eq_reflectedOldIncrement,
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm]

theorem fixedP506L0FinalCommonActionActual_gaugeAuxiliary_eq_solved :
    (fixedP506L0FinalCommonActionActual 0).gaugeAuxiliary =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary := by
  funext point pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (fixedP506L0FinalCommonActionActual_auxiliaryCoordinate_eq_solved point)
    pair

theorem fixedP506L0FinalCommonActionActual_coframe_eq_solved :
    (fixedP506L0FinalCommonActionActual 0).coframe =
      FixedP506FormNativeJointActionSolvedSuccessor.coframe := by
  calc
    (fixedP506L0FinalCommonActionActual 0).coframe =
        InputActual.coframe :=
      fixedP506L0FinalCommonActionActual_coframe 0
    _ = OldActual.coframe := input_coframe_eq_old
    _ = FixedP506FormNativeJointActionSolvedSuccessor.coframe :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe

theorem
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved :
    (fixedP506L0FinalCommonActionActual 0).gaugeConnection =
      FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection := by
  calc
    (fixedP506L0FinalCommonActionActual 0).gaugeConnection =
        InputActual.gaugeConnection :=
      fixedP506L0FinalCommonActionActual_gaugeConnection 0
    _ = OldActual.gaugeConnection := input_gaugeConnection_eq_old
    _ = FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection

/-- The complete scalar first jet seen by the P286 charged-current channel is
also the one already carried by the solved same-lineage current. -/
theorem
    fixedP506L0FinalCommonActionActual_scalarCovariantDerivative_origin_eq_solved :
    holonomicScalarCovariantDerivative
        (fixedP506L0FinalCommonActionActual 0) 0 =
      holonomicScalarCovariantDerivative
        FixedP506FormNativeJointActionSolvedSuccessor 0 := by
  calc
    holonomicScalarCovariantDerivative
          (fixedP506L0FinalCommonActionActual 0) 0 =
        holonomicScalarCovariantDerivative InputActual 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [fixedP506L0FinalCommonActionActual_scalar,
        fixedP506L0FinalCommonActionActual_gaugeConnection]
    _ = holonomicScalarCovariantDerivative OldActual 0 :=
      input_scalarCovariantDerivative_origin_eq_old
    _ = holonomicScalarCovariantDerivative
          FixedP506FormNativeJointActionSolvedSuccessor 0 := by
      funext direction
      unfold holonomicScalarCovariantDerivative
      rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
        fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

theorem fixedP506L0FinalCommonActionActual_p286AuxiliaryResidualCoordinate_eq_solved
    (point : BasePoint) :
    holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (fixedP506L0FinalCommonActionActual 0) point =
      fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
        point := by
  rw [holonomicFormNativeP286GaugeAuxiliaryEulerResidualCoordinate_eq]
  change
    (fun pair => p286CoordinateEquiv
        (holonomicGaugeCurvature
          (fixedP506L0FinalCommonActionActual 0) point pair)) -
        formNativeP286CoordinateBlockwiseConstitutive
          ((fixedP506L0FinalCommonActionActual 0).coframe point)
          _ _ _
          (holonomicP286GaugeAuxiliaryCoordinate
            (fixedP506L0FinalCommonActionActual 0) point) = _
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    (fixedP506L0FinalCommonActionActual 0)
    FixedP506FormNativeJointActionSolvedSuccessor
    fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved point,
    fixedP506L0FinalCommonActionActual_coframe_eq_solved,
    fixedP506L0FinalCommonActionActual_auxiliaryCoordinate_eq_solved]
  change
    holonomicP286GaugeCurvatureCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor point -
        formNativeP286CoordinateBlockwiseConstitutive
          (FixedP506FormNativeJointActionSolvedSuccessor.coframe point)
          _ _ _
          (holonomicP286GaugeAuxiliaryCoordinate
            FixedP506FormNativeJointActionSolvedSuccessor point) = _
  unfold
    fixedP506FormNativeJointActionSolvedP286AuxiliaryResidualCoordinateNormalForm
  rw [fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm,
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm]

/-! ## Final-common provenance on the fixed contact -/

/-- The later scalar/P286/EC action legs preserve the complete coframe field
of the already source-generated constitutive successor. -/
theorem fixedP506L0FinalCommonActionActual_coframe_eq_constitutive :
    (fixedP506L0FinalCommonActionActual 0).coframe =
      FixedP506FormNativeConstitutiveJointActionSuccessor.coframe := by
  calc
    _ = FixedP506FormNativeJointActionSolvedSuccessor.coframe :=
      fixedP506L0FinalCommonActionActual_coframe_eq_solved
    _ = FixedP506FormNativeConstitutiveJointActionSuccessor.coframe :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_coframe.symm

/-- The complete final-common P286 connection is the same source-owned
canonical primitive as on the constitutive successor. -/
theorem fixedP506L0FinalCommonActionActual_gaugeConnection_eq_constitutive :
    (fixedP506L0FinalCommonActionActual 0).gaugeConnection =
      FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection := by
  calc
    _ = FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection :=
      fixedP506L0FinalCommonActionActual_gaugeConnection_eq_solved
    _ = FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection.symm

/-- The scalar second-jet write changes the global time profile but preserves
the source-generated scalar value at the common contact. -/
theorem fixedP506L0FinalCommonActionActual_scalar_origin_eq_constitutive :
    (fixedP506L0FinalCommonActionActual 0).scalar 0 =
      FixedP506FormNativeConstitutiveJointActionSuccessor.scalar 0 := by
  rw [fixedP506L0FinalCommonActionActual_scalar]
  exact input_scalar_origin_eq_old

/-- The repaired primal write preserves its generated matter value at the
common contact through the later scalar/P286/EC legs. -/
theorem fixedP506L0FinalCommonActionActual_matter_origin_eq_constitutive :
    (fixedP506L0FinalCommonActionActual 0).matter 0 =
      FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 := by
  rw [fixedP506L0FinalCommonActionActual_matter]
  exact input_matter_origin_eq_old

/-- The repaired adjoint write preserves its generated conjugate-matter value
at the common contact through the later scalar/P286/EC legs. -/
theorem
    fixedP506L0FinalCommonActionActual_conjugateMatter_origin_eq_constitutive :
    (fixedP506L0FinalCommonActionActual 0).conjugateMatter 0 =
      FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 := by
  rw [fixedP506L0FinalCommonActionActual_conjugateMatter]
  exact input_conjugateMatter_origin_eq_old

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonP286AffineIdentification

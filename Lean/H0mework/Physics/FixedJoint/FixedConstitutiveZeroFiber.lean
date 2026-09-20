import H0mework.Physics.FixedJoint.FixedConstitutiveFirstJet

/-!
# Fixed P506/L0 constitutive successor zero-fiber readback

The common successor consumed here has already been generated forward by the
source/current-owned action operators.  No residual coordinate, sign, support,
branch, or zero-fiber witness enters that constructor.

This module first identifies the exact action contact retained by the
constitutive successor.  It then substitutes the already generated auxiliary
first jet into the P286 connection equation.  The residual is only a
post-construction consistency readout.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveZeroFiber

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCurrentP286CompleteActionResponseOperator
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeScalarVariation
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveFirstJet
open StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor
open StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineIIPlusRestriction
open StageNineMatterPointwiseEquation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineTopologicalFourFormPairing
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance constitutiveZeroFiberP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance constitutiveZeroFiberP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private theorem constitutiveSuccessor_coframe_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe =
      FixedP506JointActual.coframe := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe,
    fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]

private theorem constitutiveSuccessor_coframe_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe 0 =
      FixedP506JointActual.coframe 0 :=
  congrFun constitutiveSuccessor_coframe_eq_fixedActual 0

private theorem
    constitutiveSuccessor_gravityConnection_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gravityConnection 0 =
      FixedP506JointActual.gravityConnection 0 := by
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_gravityConnection_origin,
    fixedP506FormNativeJointActionSolvedSuccessor_gravityConnection_origin,
    fixedP506JointActionSuccessor_gravityConnection]

private theorem constitutiveSuccessor_gravityAuxiliary_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gravityAuxiliary =
      FixedP506JointActual.gravityAuxiliary := by
  funext point
  have successorZero :=
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
      point
  have fixedZero := fixedP506JointResidual_gravityMultiplier_zero point
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor point) =
      0 at successorZero
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField FixedP506JointActual point) =
      0 at fixedZero
  have successorSimplicity :=
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSuccessor point)).1
      successorZero
  have fixedSimplicity :=
    (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (toContinuumPointField FixedP506JointActual point)).1 fixedZero
  change
    FixedP506FormNativeConstitutiveJointActionSuccessor.gravityAuxiliary point =
      FixedP506JointActual.gravityAuxiliary point
  calc
    _ = physicalIIPlusBivector
          (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) :=
      successorSimplicity
    _ = physicalIIPlusBivector (FixedP506JointActual.coframe point) := by
      rw [constitutiveSuccessor_coframe_eq_fixedActual]
    _ = _ := fixedSimplicity.symm

private theorem
    constitutiveSuccessor_gravityAuxiliaryExteriorCovariantDerivative_origin_eq_fixedActual :
    holonomicGravityAuxiliaryExteriorCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      holonomicGravityAuxiliaryExteriorCovariantDerivative
        FixedP506JointActual 0 := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [constitutiveSuccessor_gravityAuxiliary_eq_fixedActual,
    constitutiveSuccessor_gravityConnection_origin_eq_fixedActual]

private theorem constitutiveSuccessor_gaugeConnection_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection 0 =
      FixedP506JointActual.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 direction =
      holonomicP286GaugeConnectionCoordinate
        FixedP506JointActual 0 direction
  rw [congrFun
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero
      direction,
    congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      direction]

private theorem constitutiveSuccessor_gaugeAuxiliary_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary 0 =
      FixedP506JointActual.gaugeAuxiliary 0 := by
  calc
    _ = FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary 0 :=
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary_origin
    _ = FixedP506JointActionSuccessor.gaugeAuxiliary 0 := by
      rw [fixedP506FormNativeJointActionSolvedSuccessor_gaugeAuxiliary]
    _ = _ := congrArg
      (fun field : StageNineContinuumPointField => field.gaugeAuxiliary)
      fixedP506JointActionSuccessor_pointField_origin

private theorem constitutiveSuccessor_scalar_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.scalar =
      FixedP506JointActual.scalar := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
    fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar]

private theorem constitutiveSuccessor_scalar_vacuum :
    FixedP506FormNativeConstitutiveJointActionSuccessor.scalar =
      fun _ =>
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  rw [constitutiveSuccessor_scalar_eq_fixedActual,
    fixedP506JointActual_scalar_vacuum]

private theorem
    constitutiveSuccessor_gaugeConnectionCoordinate_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor
        0 direction direction =
      0 := by
  unfold p286GaugeConnectionCoordinateDerivative
    holonomicP286GaugeConnectionCoordinate
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_diagonal_zero
      direction

private theorem
    constitutiveSuccessor_scalarCovariantDerivative_eq_fixedVacuumAction
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor point direction =
      scalarP286ActionBilinear
        (holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeConstitutiveJointActionSuccessor point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold holonomicScalarCovariantDerivative
  rw [constitutiveSuccessor_scalar_vacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add]
  unfold holonomicP286GaugeConnectionCoordinate
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection
            point direction))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm
            (p286CoordinateEquiv
              (FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection
                point direction))))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
  rw [p286CoordinateEquiv.symm_apply_apply]

private theorem constitutiveSuccessor_scalarCovariantDerivative_origin_zero
    (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 direction =
      0 := by
  rw [
    constitutiveSuccessor_scalarCovariantDerivative_eq_fixedVacuumAction,
    congrFun
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero
      direction]
  simp

private theorem
    constitutiveSuccessor_scalarCovariantDerivative_directionalDerivative
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            FixedP506FormNativeConstitutiveJointActionSuccessor point
              formDirection)
        0 derivativeDirection =
      scalarP286ActionBilinear
        (fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeConnectionCoordinate
              FixedP506FormNativeConstitutiveJointActionSuccessor point
                formDirection)
          0 derivativeDirection)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    holonomicP286GaugeConnectionCoordinate
      FixedP506FormNativeConstitutiveJointActionSuccessor point formDirection
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    have smooth :=
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
        |>.2.2.2.2.1 formDirection
    simpa [connection, holonomicP286GaugeConnectionCoordinate,
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection] using
      (smooth.differentiable (by simp)).differentiableAt
  have actionDerivative :
      fderiv ℝ
          (fun point =>
            action (connection point)
              (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
          0 =
        (action.flip
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).comp
            (fderiv ℝ connection 0) :=
    ((action.flip
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
        ).hasFDerivAt.comp 0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show
      (fun point =>
        holonomicScalarCovariantDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor point
            formDirection) =
        fun point =>
          action (connection point)
            (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
      funext point
      exact
        constitutiveSuccessor_scalarCovariantDerivative_eq_fixedVacuumAction
          point formDirection]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  rfl

private theorem
    constitutiveSuccessor_scalarCovariantDerivative_diagonalDerivative_zero
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          holonomicScalarCovariantDerivative
            FixedP506FormNativeConstitutiveJointActionSuccessor point direction)
        0 direction =
      0 := by
  rw [
    constitutiveSuccessor_scalarCovariantDerivative_directionalDerivative]
  change
    scalarP286ActionBilinear
        (p286GaugeConnectionCoordinateDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor
          0 direction direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) =
      0
  rw [
    constitutiveSuccessor_gaugeConnectionCoordinate_diagonalDerivative_zero]
  simp

private theorem constitutiveSuccessor_coframe_origin_one :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe 0 = 1 := by
  rw [constitutiveSuccessor_coframe_eq_fixedActual]
  exact fixedP506JointActual_coframe_origin_one

private theorem
    constitutiveSuccessor_coframe_fderiv_coordinate_zero
    (direction : LorentzianIndex) :
    (fderiv ℝ
        FixedP506FormNativeConstitutiveJointActionSuccessor.coframe 0)
        (coordinateDirection direction) =
      0 := by
  rw [constitutiveSuccessor_coframe_eq_fixedActual]
  exact fixedP506JointActual_coframe_fderiv_coordinate_zero direction

private theorem constitutiveSuccessor_coframe_differentiableAt :
    DifferentiableAt ℝ
      FixedP506FormNativeConstitutiveJointActionSuccessor.coframe 0 := by
  rw [constitutiveSuccessor_coframe_eq_fixedActual]
  exact fixedP506JointActual_coframe_differentiableAt

private theorem
    constitutiveSuccessor_scalarCovariantDerivative_eq_solvedSuccessor :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor =
      holonomicScalarCovariantDerivative
        FixedP506FormNativeJointActionSolvedSuccessor := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_scalar,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]

private theorem constitutiveSuccessor_scalarCovariantDerivative_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞
      (fun point =>
        holonomicScalarCovariantDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor point
            direction) := by
  rw [constitutiveSuccessor_scalarCovariantDerivative_eq_solvedSuccessor]
  exact
    holonomicScalarCovariantDerivative_contDiff
      FixedP506FormNativeJointActionSolvedSuccessor
      fixedP506FormNativeJointActionSolvedSuccessor_smooth direction

private def constitutiveSuccessorScalarMomentumPointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (joint : BasePoint × LorentzianCoframe) : ℝ :=
  abs (Matrix.det joint.2) *
    scalarGaugeConnectionKineticFirstVariationDensity
      positiveSmoothUnifiedSource 0 joint.1
      (StageNineCoframeVariation.withCoframe
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor joint.1)
        joint.2)
      (scalarVariationDifferentialDirection direction derivativeDirection)

private theorem constitutiveSuccessorScalarMomentumPointCoframe_contDiffAt
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (constitutiveSuccessorScalarMomentumPointCoframe direction
        derivativeDirection)
      (0, 1) := by
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2)) (0, 1) :=
    (StageNineCoframeVariation.coframe_volume_contDiffAt
      (1 : LorentzianCoframe)
      (by norm_num)).comp (0, 1) contDiffAt_snd
  have metricOuter : ContDiffAt ℝ ∞
      (fun coframe : LorentzianCoframe =>
        (lorentzianMetricOfCoframe coframe)⁻¹) 1 :=
    StageNineCoframeLocalDifferentiability.lorentzianMetric_inv_contDiffAt
      (1 : LorentzianCoframe) (by norm_num)
  have metricSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹) (0, 1) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        (lorentzianMetricOfCoframe joint.2)⁻¹) =
        (fun coframe : LorentzianCoframe =>
          (lorentzianMetricOfCoframe coframe)⁻¹) ∘
          (fun joint : BasePoint × LorentzianCoframe => joint.2) by
      rfl]
    exact metricOuter.comp (0, 1)
      (show ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe => joint.2) (0, 1) from
        contDiffAt_snd)
  have covariantSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun joint : BasePoint × LorentzianCoframe =>
        holonomicScalarCovariantDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor joint.1
            formDirection :=
    (constitutiveSuccessor_scalarCovariantDerivative_contDiff formDirection
      ).comp contDiff_fst
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiff ℝ ∞ fun _ : BasePoint × LorentzianCoframe =>
        scalarVariationDifferentialDirection direction derivativeDirection
          formDirection :=
    contDiff_const
  unfold constitutiveSuccessorScalarMomentumPointCoframe
    scalarGaugeConnectionKineticFirstVariationDensity
  simp only [StageNineCoframeVariation.withCoframe,
    scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates_zeroChart]
  apply volumeSmooth.mul
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro first _
  apply ContDiffAt.sum
  intro second _
  apply
    (contDiffAt_pi.mp (contDiffAt_pi.mp metricSmooth first) second).mul
  exact
    ((StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
      _ _ (variationSmooth first) (covariantSmooth second)).add
      (StageNineCoframeScalarMatterRegularity.scalarCoordinatePairingRe_joint_contDiff_local
        _ _ (covariantSmooth first) (variationSmooth second))).contDiffAt

private theorem
    constitutiveSuccessor_scalarDifferentialMomentum_eq_pointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction
          derivativeDirection =
      constitutiveSuccessorScalarMomentumPointCoframe direction
          derivativeDirection ∘
        fun point =>
          (point,
            FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) := by
  funext point
  unfold scalarDifferentialMomentum
    constitutiveSuccessorScalarMomentumPointCoframe generatedVolumeDensity
  simp only [Function.comp_apply, StageNineCoframeVariation.withCoframe,
    toContinuumPointField]

private abbrev FixedP506FormNativeConstitutiveIdentityCoframeComparison :
    StageNineHolonomicConfiguration :=
  identityCoframeComparison
    FixedP506FormNativeConstitutiveJointActionSuccessor

private theorem
    constitutiveComparison_scalarDifferentialMomentum_eq_pointCoframe
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveIdentityCoframeComparison direction
          derivativeDirection =
      constitutiveSuccessorScalarMomentumPointCoframe direction
          derivativeDirection ∘
        fun point => (point, (1 : LorentzianCoframe)) := by
  funext point
  unfold scalarDifferentialMomentum
    constitutiveSuccessorScalarMomentumPointCoframe generatedVolumeDensity
    FixedP506FormNativeConstitutiveIdentityCoframeComparison
    identityCoframeComparison
  simp only [Function.comp_apply, StageNineCoframeVariation.withCoframe,
    toContinuumPointField]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    holonomicScalarCovariantDerivative
  rfl

private theorem fderiv_pointCoframe_eq_frozen_of_zero
    (outer : BasePoint × LorentzianCoframe → ℝ)
    (outerDifferentiable : DifferentiableAt ℝ outer (0, 1))
    (coframe : BasePoint → LorentzianCoframe)
    (coframeOrigin : coframe 0 = 1)
    (coframeDifferentiable : DifferentiableAt ℝ coframe 0)
    (direction : LorentzianIndex)
    (coframeDerivativeZero :
      (fderiv ℝ coframe 0) (coordinateDirection direction) = 0) :
    (fderiv ℝ
        (outer ∘ fun point => (point, coframe point)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
        (outer ∘ fun point => (point, (1 : LorentzianCoframe))) 0)
        (coordinateDirection direction) := by
  have actualInner :
      HasFDerivAt (fun point : BasePoint => (point, coframe point))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (fderiv ℝ coframe 0)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      coframeDifferentiable.hasFDerivAt
  have frozenInner :
      HasFDerivAt
        (fun point : BasePoint => (point, (1 : LorentzianCoframe)))
        ((ContinuousLinearMap.id ℝ BasePoint).prod
          (0 : BasePoint →L[ℝ] LorentzianCoframe)) 0 :=
    HasFDerivAt.prodMk (hasFDerivAt_id (x := (0 : BasePoint)))
      (hasFDerivAt_const (x := (0 : BasePoint))
        (c := (1 : LorentzianCoframe)))
  have outerAtActual : DifferentiableAt ℝ outer (0, coframe 0) := by
    simpa only [coframeOrigin] using outerDifferentiable
  have actualComposition :=
    outerAtActual.hasFDerivAt.comp 0 actualInner
  have frozenComposition :=
    outerDifferentiable.hasFDerivAt.comp 0 frozenInner
  rw [actualComposition.fderiv, frozenComposition.fderiv]
  rw [coframeOrigin]
  change
    (fderiv ℝ outer (0, 1))
        (coordinateDirection direction,
          (fderiv ℝ coframe 0) (coordinateDirection direction)) =
      (fderiv ℝ outer (0, 1))
        (coordinateDirection direction, 0)
  rw [coframeDerivativeZero]

private theorem
    constitutiveSuccessor_scalarMomentumDerivative_eq_comparison
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506FormNativeConstitutiveJointActionSuccessor direction
            derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedP506FormNativeConstitutiveIdentityCoframeComparison direction
            derivativeDirection)
        0 derivativeDirection := by
  unfold fieldDirectionalDerivative
  rw [
    constitutiveSuccessor_scalarDifferentialMomentum_eq_pointCoframe,
    constitutiveComparison_scalarDifferentialMomentum_eq_pointCoframe]
  exact
    fderiv_pointCoframe_eq_frozen_of_zero
      (constitutiveSuccessorScalarMomentumPointCoframe direction
        derivativeDirection)
      ((constitutiveSuccessorScalarMomentumPointCoframe_contDiffAt
        direction derivativeDirection).differentiableAt (by simp))
      FixedP506FormNativeConstitutiveJointActionSuccessor.coframe
      constitutiveSuccessor_coframe_origin_one
      constitutiveSuccessor_coframe_differentiableAt
      derivativeDirection
      (constitutiveSuccessor_coframe_fderiv_coordinate_zero
        derivativeDirection)

private theorem
    constitutiveSuccessor_scalarMomentumDivergence_eq_comparison
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveIdentityCoframeComparison direction
          0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    constitutiveSuccessor_scalarMomentumDerivative_eq_comparison
      direction derivativeDirection

private theorem
    constitutiveComparison_scalarCovariantDerivative_eq_successor
    (point : BasePoint) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveIdentityCoframeComparison point
          direction =
      holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor point direction := by
  rfl

private theorem constitutiveComparison_scalarMomentumDivergence_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveIdentityCoframeComparison direction 0 =
      0 := by
  apply
    StageNineBiradialScalarOriginResponse.scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
      positiveSmoothUnifiedSource
      FixedP506FormNativeConstitutiveIdentityCoframeComparison
      (a := 1) (b := 1)
  · norm_num
  · norm_num
  · rw [identityCoframeComparison_coframe,
      StageNineBiradialCoframeResponse.biradialCoframe_one_one]
  · intro formDirection
    have differentiable :
        DifferentiableAt ℝ
          (fun point =>
            holonomicScalarCovariantDerivative
              FixedP506FormNativeConstitutiveJointActionSuccessor point
                formDirection)
          0 :=
      ((constitutiveSuccessor_scalarCovariantDerivative_contDiff formDirection
        ).differentiable (by simp)).differentiableAt
    simpa only [
      constitutiveComparison_scalarCovariantDerivative_eq_successor] using
      differentiable
  · intro formDirection
    have functionEquality :
        (fun point =>
          holonomicScalarCovariantDerivative
            FixedP506FormNativeConstitutiveIdentityCoframeComparison point
              formDirection) =
          fun point =>
            holonomicScalarCovariantDerivative
              FixedP506FormNativeConstitutiveJointActionSuccessor point
                formDirection := by
      funext point
      exact
        constitutiveComparison_scalarCovariantDerivative_eq_successor
          point formDirection
    rw [functionEquality]
    exact
      constitutiveSuccessor_scalarCovariantDerivative_diagonalDerivative_zero
        formDirection

private theorem constitutiveSuccessor_scalarMomentumDivergence_zero
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      0 := by
  rw [constitutiveSuccessor_scalarMomentumDivergence_eq_comparison]
  exact constitutiveComparison_scalarMomentumDivergence_zero direction

private theorem constitutiveSuccessor_scalarKineticAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0)
        (holonomicScalarVariationAlgebraicDirection
          FixedP506FormNativeConstitutiveJointActionSuccessor direction 0) =
      0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeOrigin :
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSuccessor
          0).scalarCovariantDerivative =
        0 := by
    funext formDirection
    exact
      constitutiveSuccessor_scalarCovariantDerivative_origin_zero
        formDirection
  rw [covariantDerivativeOrigin]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

private theorem constitutiveSuccessor_scalarPotential_origin_zero
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0)
        direction =
      0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField
      FixedP506FormNativeConstitutiveJointActionSuccessor 0).scalar =
        sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    exact congrFun constitutiveSuccessor_scalar_vacuum 0]
  simp

private theorem constitutiveSuccessor_diracDualScalarYukawa_origin_zero
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0)
        direction =
      0 := by
  unfold diracDualScalarYukawaFirstVariationDensity
    diracDualScalarYukawaVariationVector
  rw [show
    (toContinuumPointField
      FixedP506FormNativeConstitutiveJointActionSuccessor
        0).conjugateMatter =
      diracSpinZeroMatterCoordinate by
    change
      FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 =
        diracSpinZeroMatterCoordinate
    rw [
      fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter,
      fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
      fixedP506JointActionSuccessor_conjugateMatter]
    exact fixedP506JointActual_conjugateMatter_origin]
  rw [
    fixedDiracSpinZeroMatterCoordinate_diracDualRightChiralYukawa_zero]
  norm_num

private theorem
    constitutiveSuccessor_diracDualScalarAlgebraic_origin_zero
    (direction : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      0 := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [constitutiveSuccessor_scalarKineticAlgebraic_origin_zero,
    constitutiveSuccessor_scalarPotential_origin_zero,
    constitutiveSuccessor_diracDualScalarYukawa_origin_zero]
  ring

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).scalar =
      0 := by
  funext direction
  change
    diracDualScalarEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      0
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient
  rw [constitutiveSuccessor_diracDualScalarAlgebraic_origin_zero,
    constitutiveSuccessor_scalarMomentumDivergence_zero]
  simp

private theorem constitutiveSuccessor_matter_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter =
      FixedP506JointActual.matter := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_matter,
    fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem constitutiveSuccessor_matter_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 =
      FixedP506JointActual.matter 0 :=
  congrFun constitutiveSuccessor_matter_eq_fixedActual 0

private theorem constitutiveSuccessor_conjugateMatter_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter =
      FixedP506JointActual.conjugateMatter := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter,
    fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]

private theorem constitutiveSuccessor_conjugateMatter_origin_eq_fixedActual :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 =
      FixedP506JointActual.conjugateMatter 0 :=
  congrFun constitutiveSuccessor_conjugateMatter_eq_fixedActual 0

private theorem
    constitutiveSuccessor_matterSpinThreeForm_origin_eq_fixedActual :
    formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      formNativeMatterSpinThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) := by
  have responseEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource
      FixedP506FormNativeConstitutiveJointActionSuccessor
      FixedP506JointActual 0
      constitutiveSuccessor_coframe_origin_eq_fixedActual
      constitutiveSuccessor_matter_origin_eq_fixedActual
      constitutiveSuccessor_conjugateMatter_origin_eq_fixedActual
  have successorRestrict :
      restrictHolonomicConfigurationToIIPlus
          FixedP506FormNativeConstitutiveJointActionSuccessor =
        FixedP506FormNativeConstitutiveJointActionSuccessor := by
    apply
      (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
        FixedP506FormNativeConstitutiveJointActionSuccessor).2
    intro point
    exact congrFun constitutiveSuccessor_gravityAuxiliary_eq_fixedActual point
      |>.trans
        ((formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
          (toContinuumPointField FixedP506JointActual point)).1
          (by
            have old := fixedP506JointResidual_gravityMultiplier_zero point
            change
              formNativeGravityMultiplierEulerResidual
                  (toContinuumPointField FixedP506JointActual point) =
                0 at old
            exact old))
  have fixedRestrict :
      restrictHolonomicConfigurationToIIPlus FixedP506JointActual =
        FixedP506JointActual := by
    apply
      (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
        FixedP506JointActual).2
    intro point
    exact
      (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
        (toContinuumPointField FixedP506JointActual point)).1
        (by
          have old := fixedP506JointResidual_gravityMultiplier_zero point
          change
            formNativeGravityMultiplierEulerResidual
                (toContinuumPointField FixedP506JointActual point) =
              0 at old
          exact old)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at responseEquality
  rw [successorRestrict, fixedRestrict] at responseEquality
  exact neg_injective responseEquality

private theorem constitutiveSuccessor_lorentzEuler_origin_eq_fixedActual :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506JointActual 0 := by
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [
    constitutiveSuccessor_gravityAuxiliaryExteriorCovariantDerivative_origin_eq_fixedActual,
    constitutiveSuccessor_matterSpinThreeForm_origin_eq_fixedActual]

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).lorentzConnection =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      0
  rw [constitutiveSuccessor_lorentzEuler_origin_eq_fixedActual]
  exact fixedP506JointResidual_lorentzConnection_origin_zero

private theorem
    constitutiveSuccessor_scalarCovariantDerivative_origin_eq_fixedActual :
    holonomicScalarCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      holonomicScalarCovariantDerivative FixedP506JointActual 0 := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [constitutiveSuccessor_scalar_eq_fixedActual,
    constitutiveSuccessor_gaugeConnection_origin_eq_fixedActual]

private theorem
    constitutiveSuccessor_matterCovariantDerivative_origin_eq_fixedActual :
    holonomicMatterCovariantDerivative
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      holonomicMatterCovariantDerivative FixedP506JointActual 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [constitutiveSuccessor_matter_eq_fixedActual,
    constitutiveSuccessor_gravityConnection_origin_eq_fixedActual,
    constitutiveSuccessor_gaugeConnection_origin_eq_fixedActual]

private theorem
    constitutiveSuccessor_repairedMatterVector_origin_eq_fixedActual :
    generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      generatedContinuumDiracDualMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedP506JointActual 0) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  rw [constitutiveSuccessor_coframe_eq_fixedActual,
    constitutiveSuccessor_matterCovariantDerivative_origin_eq_fixedActual,
    constitutiveSuccessor_scalar_eq_fixedActual,
    constitutiveSuccessor_matter_eq_fixedActual]

private theorem constitutiveSuccessor_volume_origin_eq_fixedActual :
    generatedVolumeDensity
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      generatedVolumeDensity (toContinuumPointField FixedP506JointActual 0) := by
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [constitutiveSuccessor_coframe_eq_fixedActual]

private theorem constitutiveSuccessor_matterDifferentialMomentum_eq_fixedActual
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction
        derivativeDirection =
      matterDifferentialMomentum positiveSmoothUnifiedSource
        FixedP506JointActual direction derivativeDirection := by
  funext point
  unfold matterDifferentialMomentum matterDifferentialVariationVector
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [constitutiveSuccessor_coframe_eq_fixedActual,
    constitutiveSuccessor_conjugateMatter_eq_fixedActual]

private theorem
    constitutiveSuccessor_matterDifferentialMomentumDivergence_eq_fixedActual
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedP506JointActual direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  rw [
    constitutiveSuccessor_matterDifferentialMomentum_eq_fixedActual
      direction derivativeDirection]

private theorem
    constitutiveSuccessor_diracDualMatterAlgebraic_eq_fixedActual
    (direction : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      diracDualMatterAlgebraicDirectionalCoefficient
        positiveSmoothUnifiedSource FixedP506JointActual direction 0 := by
  unfold diracDualMatterAlgebraicDirectionalCoefficient
    diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    holonomicMatterVariationAlgebraicDirection
    generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [constitutiveSuccessor_coframe_eq_fixedActual,
    constitutiveSuccessor_conjugateMatter_eq_fixedActual,
    constitutiveSuccessor_scalar_eq_fixedActual,
    constitutiveSuccessor_gravityConnection_origin_eq_fixedActual,
    constitutiveSuccessor_gaugeConnection_origin_eq_fixedActual]

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_matter_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).matter =
      0 := by
  funext direction
  change
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      0
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient
  rw [constitutiveSuccessor_diracDualMatterAlgebraic_eq_fixedActual,
    constitutiveSuccessor_matterDifferentialMomentumDivergence_eq_fixedActual]
  exact congrFun fixedP506JointResidual_matter_origin_zero direction

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_conjugateMatter_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).conjugateMatter =
      0 := by
  funext direction
  change
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      0
  have old :=
    congrFun fixedP506JointResidual_conjugateMatter_origin_zero direction
  unfold diracDualConjugateMatterDirectionalCoefficient at old ⊢
  rw [constitutiveSuccessor_volume_origin_eq_fixedActual,
    constitutiveSuccessor_repairedMatterVector_origin_eq_fixedActual]
  exact old

/-- The already generated constitutive successor retains the complete local
action dual at the canonical contact. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_fullActionTarget :
    currentP286FullActionTarget positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor =
      currentP286FullActionTarget positiveSmoothUnifiedSource
        FixedP506JointActual := by
  apply LinearMap.ext
  intro direction
  exact
    p286GaugeConnectionAlgebraicCurrentCoefficient_eq_of_contact
      positiveSmoothUnifiedSource
      FixedP506FormNativeConstitutiveJointActionSuccessor
      FixedP506JointActual 0
      constitutiveSuccessor_coframe_origin_eq_fixedActual
      constitutiveSuccessor_gaugeConnection_origin_eq_fixedActual
      constitutiveSuccessor_gaugeAuxiliary_origin_eq_fixedActual
      (congrFun constitutiveSuccessor_scalar_eq_fixedActual 0)
      constitutiveSuccessor_scalarCovariantDerivative_origin_eq_fixedActual
      constitutiveSuccessor_matter_origin_eq_fixedActual
      constitutiveSuccessor_conjugateMatter_origin_eq_fixedActual
      direction

private theorem
    constitutiveSuccessor_actionCurrent_eq_formNativeCharged
    (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurrentCoefficient
        positiveSmoothUnifiedSource
        FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
      formNativeChargedGaugeFirstCoefficient
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0)
        direction := by
  have curvatureVariationZero :
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureDirection
          FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
        0 := by
    funext pair
    unfold
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureDirection
      StageNineP286GaugeConnectionPointwiseEquation.p286GaugeConnectionAlgebraicCurvatureVariation
    rw [
      fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero]
    simp
  unfold p286GaugeConnectionAlgebraicCurrentCoefficient
    p286GaugeConnectionFirstVariationDensity
    formNativeChargedGaugeFirstCoefficient
  rw [curvatureVariationZero]
  have bfZero :
      p286GaugeBFCurvatureIncrementDensity
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor 0).coframe
          (coframeGaugeSpacetimeHodgeLinear
            (toContinuumPointField
              FixedP506FormNativeConstitutiveJointActionSuccessor 0).coframe)
          (p286AuxiliaryCoordinate
            (toContinuumPointField
              FixedP506FormNativeConstitutiveJointActionSuccessor 0))
          0 =
        0 := by
    simp [p286GaugeBFCurvatureIncrementDensity,
      generatedGaugeTwoFormMetricPairing]
  rw [bfZero, zero_add]
  have scalarVariationEq :
      holonomicScalarGaugeConnectionVariation
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (fun _ => direction) 0 =
        pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor 0)
          direction := by
    symm
    simpa using
      pointwiseScalarP286GaugeConnectionVariation_actual
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (fun _ => direction) 0
  have matterVariationEq :
      holonomicMatterGaugeConnectionVariation
          FixedP506FormNativeConstitutiveJointActionSuccessor
          (fun _ => direction) 0 =
        pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor 0)
          direction := by
    symm
    simpa using
      pointwiseMatterP286GaugeConnectionVariation_actual
        FixedP506FormNativeConstitutiveJointActionSuccessor
        (fun _ => direction) 0
  rw [scalarVariationEq, matterVariationEq]

theorem
    fixedP506FormNativeP286ActionTarget_eq_neg_constitutiveCharged :
    fixedP506FormNativeP286ActionTarget =
      -formNativeChargedGaugeFirstLinearMap positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) := by
  apply LinearMap.ext
  intro direction
  calc
    fixedP506FormNativeP286ActionTarget direction =
        -(currentP286FullActionTarget positiveSmoothUnifiedSource
          FixedP506JointActual) direction := by
      exact DFunLike.congr_fun
        fixedP506FormNativeP286ActionTarget_eq_neg_currentAction direction
    _ = -(currentP286FullActionTarget positiveSmoothUnifiedSource
          FixedP506FormNativeConstitutiveJointActionSuccessor) direction := by
      rw [fixedP506FormNativeConstitutiveJointActionSuccessor_fullActionTarget]
    _ = -formNativeChargedGaugeFirstCoefficient
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor 0)
          direction := by
      change
        -p286GaugeConnectionAlgebraicCurrentCoefficient
            positiveSmoothUnifiedSource
            FixedP506FormNativeConstitutiveJointActionSuccessor direction 0 =
          _
      rw [constitutiveSuccessor_actionCurrent_eq_formNativeCharged]
    _ = (-formNativeChargedGaugeFirstLinearMap
          positiveSmoothUnifiedSource 0 0
          (toContinuumPointField
            FixedP506FormNativeConstitutiveJointActionSuccessor 0))
          direction := by
      rfl

private theorem
    constitutiveSuccessor_exteriorDerivative_wedge_eq_target
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      fixedP506FormNativeP286ActionTarget direction := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  have derivativeEquality :
      p286GaugeAuxiliaryDirectionalDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
        fun derivativeDirection =>
          fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
            (coordinateDirection derivativeDirection) := by
    funext derivativeDirection
    exact
      fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryDirectionalDerivative
        derivativeDirection
  rw [derivativeEquality]
  calc
    _ =
        -(∑ derivativeDirection : LorentzianIndex,
          p286GaugeExteriorPrincipalBilinear derivativeDirection
            (fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection derivativeDirection))
            direction) := by
      exact
        (p286GaugeExteriorPrincipalSum_eq_w13
          (fun derivativeDirection =>
            fixedP506FormNativeJointActionAuxiliaryFirstJetLinear
              (coordinateDirection derivativeDirection))
          direction).symm
    _ = _ := by
      rw [fixedP506FormNativeJointAction_principalSum]
      simp

private theorem constitutiveSuccessor_zeroConnectionExteriorAction
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

private theorem
    constitutiveSuccessor_covariantDerivative_wedge_eq_target
    (direction : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient direction
        (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      fixedP506FormNativeP286ActionTarget direction := by
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
    constitutiveSuccessor_exteriorDerivative_wedge_eq_target,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero,
    constitutiveSuccessor_zeroConnectionExteriorAction]
  simp [p286GaugeOneFormThreeFormWedgeCoefficient]

/-- P286 connection acceptance on the same action-generated common actual.
This is producer soundness: the residual was not used to define the write. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).p286GaugeConnection =
      0 := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      0
  calc
    _ = p286GaugeThreeFormOfDual 0 := by
      apply p286GaugeThreeFormOfDual_unique
      intro direction
      unfold holonomicFormNativeP286GaugeEulerThreeForm
      rw [p286GaugeOneFormThreeFormWedgeCoefficient_add_right,
        constitutiveSuccessor_covariantDerivative_wedge_eq_target,
        formNativeChargedGaugeThreeForm_evaluation]
      have targetEquality :=
        DFunLike.congr_fun
          fixedP506FormNativeP286ActionTarget_eq_neg_constitutiveCharged
          direction
      simpa only [LinearMap.zero_apply, LinearMap.neg_apply,
        formNativeChargedGaugeFirstLinearMap_apply] using
          add_eq_zero_iff_eq_neg.mpr targetEquality
    _ = 0 := by
      unfold p286GaugeThreeFormOfDual
      exact map_zero p286GaugeThreeFormWedgeEquiv.symm

/-- Complete nine-coordinate origin zero fiber on the one common successor
generated by the fixed source/current action chain.  Every residual
coordinate is substituted only after that successor exists. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_origin_zero :
    fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0 =
      0 := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        0
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        0
  · apply
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zero
    rw [constitutiveSuccessor_coframe_origin_one]
    norm_num
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_lorentzConnection_origin_zero
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeConnection_origin_zero
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_scalar_origin_zero
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_matter_origin_zero
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_conjugateMatter_origin_zero
  · exact
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_coframe_origin_zero

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_onPointwiseZeroFiber :
    OnDiracDualFormNativePointwiseJointZeroFiber positiveSmoothUnifiedSource
      FixedP506FormNativeConstitutiveJointActionSuccessor 0 :=
  fixedP506FormNativeConstitutiveJointActionSuccessorResidual_origin_zero

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveZeroFiber

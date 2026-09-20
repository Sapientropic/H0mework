import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerCore
import H0mework.Physics.FixedJoint.FixedP286CanonicalJointActionWrite
import H0mework.Physics.Holonomic.CoframeRegularity
import H0mework.Physics.Coframe.CoframeTwoFormPairing
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Gauge.GaugeWedge
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity
import H0mework.Physics.GaugeAction.P286GaugeDerivativeIntegrationByParts
import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryEquation

/-!
# Canonical P286 joint-action producer soundness

For every smooth current whose selected contact has identity coframe, the
canonical diagonal P286 action principal changes the complete W13 action
covector by exactly the negative nondegenerate one-form pairing.  Therefore
the source/action-generated write is the unique zero of that actual covector.

The theorem is uniform in the background current.  Its hypotheses contain
only primitive-current regularity and the contact coframe value; no residual,
support coordinate, target response, branch, or equation receipt is supplied.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionProducerSoundness

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeHolonomicRegularity
open StageNineCoframeTwoFormPairing
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeDerivativeIntegrationByParts
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ColorCartanConstitutiveResponse
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalFourFormPairing
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

open scoped ContDiff Matrix.Norms.Elementwise

local instance canonicalSoundnessP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance canonicalSoundnessP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance canonicalSoundnessP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private abbrev CanonicalBoundary :=
  sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource

/-! ## Identity-coframe constitutive differential -/

private abbrev positiveSourceCanonicalActionInverse :=
  fixedP506L0P286CanonicalActionInverse

/-! ## Uniform candidate origin and first-jet transport -/

private theorem canonicalConnectionCandidate_smooth
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalConnectionCandidate current write).Smooth :=
  installP286HolonomicConnectionSecondJet_smooth current smooth
    (p286CanonicalDiagonalResponseSecondJet write) 1

private theorem canonicalConnectionCandidate_zero
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeP286CanonicalConnectionCandidate current 0 =
      current := by
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [map_zero, map_zero]
  apply StageNineHolonomicConfiguration.ext <;>
    simp [varyP286GaugeConnectionCoordinate,
      holonomicP286GaugeConnectionCoordinate]

private theorem canonicalJointCandidate_auxiliaryCoordinate
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) point =
      positiveSourceCanonicalActionInverse
        (current.coframe point,
          holonomicP286GaugeCurvatureCoordinate
            (diracDualFormNativeP286CanonicalConnectionCandidate current write)
            point) := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
    positiveSourceCanonicalActionInverse
    diracDualFormNativeP286CanonicalJointCandidate
  change
    formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          CanonicalBoundary (current.coframe point)
          (holonomicGaugeCurvature
            (diracDualFormNativeP286CanonicalConnectionCandidate current write)
            point)) =
      formNativeP286GaugeActualToCoordinateLinear
        (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
          CanonicalBoundary (current.coframe point)
          (formNativeP286GaugeCoordinateToActualLinear
            (formNativeP286GaugeActualToCoordinateLinear
              (holonomicGaugeCurvature
                (diracDualFormNativeP286CanonicalConnectionCandidate current
                  write) point))))
  rw [formNativeP286GaugeActual_coordinate_actual]

private theorem canonicalJointCandidate_connection_origin
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    holonomicP286GaugeConnectionCoordinate
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      holonomicP286GaugeConnectionCoordinate current 0 := by
  change
    holonomicP286GaugeConnectionCoordinate
        (diracDualFormNativeP286CanonicalConnectionCandidate current write) 0 =
      _
  exact installP286HolonomicConnectionSecondJet_connection_origin current
    (p286CanonicalDiagonalResponseSecondJet write) 1

private theorem canonicalJointCandidate_curvature_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    holonomicP286GaugeCurvatureCoordinate
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      holonomicP286GaugeCurvatureCoordinate current 0 := by
  change
    holonomicP286GaugeCurvatureCoordinate
        (diracDualFormNativeP286CanonicalConnectionCandidate current write) 0 =
      _
  exact installP286HolonomicConnectionSecondJet_curvature_origin current
    smooth (p286CanonicalDiagonalResponseSecondJet write) 1

private theorem canonicalJointCandidate_auxiliary_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource current write).gaugeAuxiliary 0 =
      (diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource current 0).gaugeAuxiliary 0 := by
  change
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
        (current.coframe 0)
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalConnectionCandidate current write)
          0) =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
        (current.coframe 0)
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalConnectionCandidate current 0) 0)
  have curvatureCoordinateEquality :
      holonomicP286GaugeCurvatureCoordinate
          (diracDualFormNativeP286CanonicalConnectionCandidate current write) 0 =
        holonomicP286GaugeCurvatureCoordinate
          (diracDualFormNativeP286CanonicalConnectionCandidate current 0) 0 :=
    (installP286HolonomicConnectionSecondJet_curvature_origin current smooth
      (p286CanonicalDiagonalResponseSecondJet write) 1).trans
      (installP286HolonomicConnectionSecondJet_curvature_origin current smooth
        (p286CanonicalDiagonalResponseSecondJet 0) 1).symm
  have curvatureEquality :
      holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalConnectionCandidate current write) 0 =
        holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalConnectionCandidate current 0) 0 := by
    funext pair
    apply p286CoordinateEquiv.injective
    exact congrFun curvatureCoordinateEquality pair
  rw [curvatureEquality]

/-- Every canonical homogeneous-quadratic write preserves the raw P286
connection value at the contact. -/
theorem canonicalJointCandidate_connection_origin_raw
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalJointCandidate
        positiveSmoothUnifiedSource current write).gaugeConnection 0 =
      current.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  exact congrFun (canonicalJointCandidate_connection_origin current write)
    direction

private theorem canonicalJointCandidate_curvature_origin_raw
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    holonomicGaugeCurvature
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      holonomicGaugeCurvature current 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun (canonicalJointCandidate_curvature_origin current smooth write)
    pair

@[simp] private theorem canonicalJointCandidate_scalar
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalJointCandidate
      positiveSmoothUnifiedSource current write).scalar = current.scalar :=
  rfl

@[simp] private theorem canonicalJointCandidate_matter
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalJointCandidate
      positiveSmoothUnifiedSource current write).matter = current.matter :=
  rfl

@[simp] private theorem canonicalJointCandidate_gravityConnection
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalJointCandidate
      positiveSmoothUnifiedSource current write).gravityConnection =
      current.gravityConnection :=
  rfl

private def canonicalJointCandidatePointFieldOriginTemplate
    (current : StageNineHolonomicConfiguration)
    (gaugeCurvature gaugeAuxiliary : Fin 6 → P286LieBlockData)
    (scalarCovariantDerivative :
      LorentzianIndex →
        StageNineDynamicBreakingVacuum.ScalarCoordinateCarrier)
    (matterCovariantDerivative :
      LorentzianIndex →
        DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
    StageNineContinuumPointField where
  coframe := current.coframe 0
  gravityCurvature := holonomicGravityCurvature current 0
  gravityAuxiliary := current.gravityAuxiliary 0
  gravitySimplicityMultiplier := current.gravitySimplicityMultiplier 0
  gaugeCurvature := gaugeCurvature
  gaugeAuxiliary := gaugeAuxiliary
  scalar := current.scalar 0
  scalarCovariantDerivative := scalarCovariantDerivative
  matter := current.matter 0
  matterCovariantDerivative := matterCovariantDerivative
  conjugateMatter := current.conjugateMatter 0

private theorem canonicalJointCandidate_pointField_origin_eq_template
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) :
    toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      canonicalJointCandidatePointFieldOriginTemplate current
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0)
        ((diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write).gaugeAuxiliary 0)
        (holonomicScalarCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0)
        (holonomicMatterCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0) :=
  rfl

theorem canonicalJointCandidate_pointField_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current 0) 0 := by
  have gaugeCurvatureEquality :
      holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0 =
        holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 :=
    (canonicalJointCandidate_curvature_origin_raw current smooth
      write).trans
      (canonicalJointCandidate_curvature_origin_raw current smooth 0).symm
  have gaugeAuxiliaryEquality :
      (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write).gaugeAuxiliary 0 =
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current 0).gaugeAuxiliary 0 :=
    canonicalJointCandidate_auxiliary_origin current smooth write
  have scalarCovariantDerivativeEquality :
      holonomicScalarCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0 =
        holonomicScalarCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 := by
    funext direction
    unfold holonomicScalarCovariantDerivative
    rw [canonicalJointCandidate_scalar current write,
      canonicalJointCandidate_scalar current 0,
      canonicalJointCandidate_connection_origin_raw current write,
      canonicalJointCandidate_connection_origin_raw current 0]
  have matterCovariantDerivativeEquality :
      holonomicMatterCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0 =
        holonomicMatterCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 := by
    funext direction
    unfold holonomicMatterCovariantDerivative
    rw [canonicalJointCandidate_matter current write,
      canonicalJointCandidate_matter current 0,
      canonicalJointCandidate_gravityConnection current write,
      canonicalJointCandidate_gravityConnection current 0,
      canonicalJointCandidate_connection_origin_raw current write,
      canonicalJointCandidate_connection_origin_raw current 0]
  calc
    toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      canonicalJointCandidatePointFieldOriginTemplate current
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0)
        ((diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write).gaugeAuxiliary 0)
        (holonomicScalarCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0)
        (holonomicMatterCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0) :=
      canonicalJointCandidate_pointField_origin_eq_template current write
    _ = canonicalJointCandidatePointFieldOriginTemplate current
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0)
        ((diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current 0).gaugeAuxiliary 0)
        (holonomicScalarCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0)
        (holonomicMatterCovariantDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0) := by
          rw [gaugeCurvatureEquality, gaugeAuxiliaryEquality,
            scalarCovariantDerivativeEquality,
            matterCovariantDerivativeEquality]
    _ = toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current 0) 0 :=
      (canonicalJointCandidate_pointField_origin_eq_template current 0).symm

/-- If the incoming current already carries the authoritative constitutive
auxiliary value at the contact, every canonical quadratic write preserves its
complete continuum point field there.  This is a value/first-jet transport
fact, not an equation premise for the generated write. -/
theorem canonicalJointCandidate_pointField_origin_eq_current
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (liveAuxiliary :
      current.gaugeAuxiliary 0 =
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
          (current.coframe 0) (holonomicGaugeCurvature current 0))
    (write : P286GaugeOneForm) :
    toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      toContinuumPointField current 0 := by
  calc
    toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      toContinuumPointField
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current 0) 0 :=
      canonicalJointCandidate_pointField_origin current smooth write
    _ = toContinuumPointField current 0 := by
      apply StageNineContinuumPointField.ext
      · rfl
      · change
          holonomicGravityCurvature current 0 =
            holonomicGravityCurvature current 0
        rfl
      · rfl
      · rfl
      · exact canonicalJointCandidate_curvature_origin_raw current smooth 0
      · change
          formNativeP286GaugeEliminatedAuxiliaryAtBoundary CanonicalBoundary
              (current.coframe 0)
              (holonomicGaugeCurvature
                (diracDualFormNativeP286CanonicalConnectionCandidate current 0)
                0) =
            current.gaugeAuxiliary 0
        rw [canonicalConnectionCandidate_zero current]
        exact liveAuxiliary.symm
      · rfl
      · change
          holonomicScalarCovariantDerivative
              (diracDualFormNativeP286CanonicalJointCandidate
                positiveSmoothUnifiedSource current 0) 0 =
            holonomicScalarCovariantDerivative current 0
        funext direction
        unfold holonomicScalarCovariantDerivative
        rw [canonicalJointCandidate_scalar current 0,
          canonicalJointCandidate_connection_origin_raw current 0]
      · rfl
      · change
          holonomicMatterCovariantDerivative
              (diracDualFormNativeP286CanonicalJointCandidate
                positiveSmoothUnifiedSource current 0) 0 =
            holonomicMatterCovariantDerivative current 0
        funext direction
        unfold holonomicMatterCovariantDerivative
        rw [canonicalJointCandidate_matter current 0,
          canonicalJointCandidate_gravityConnection current 0,
          canonicalJointCandidate_connection_origin_raw current 0]
      · rfl

private def canonicalJointInput
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) (point : BasePoint) :
    LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm :=
  (current.coframe point,
    holonomicP286GaugeCurvatureCoordinate
      (diracDualFormNativeP286CanonicalConnectionCandidate current write)
      point)

private theorem canonicalJointInput_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    canonicalJointInput current write 0 =
      (1, holonomicP286GaugeCurvatureCoordinate current 0) := by
  apply Prod.ext
  · exact coframeOrigin
  · exact canonicalJointCandidate_curvature_origin current smooth write

private theorem current_coframe_differentiableAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    DifferentiableAt ℝ current.coframe 0 :=
  (holonomicCoframe_contDiff current smooth).differentiable (by simp)
    |>.differentiableAt

private theorem canonicalCandidate_curvature_differentiableAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    DifferentiableAt ℝ
      (holonomicP286GaugeCurvatureCoordinate
        (diracDualFormNativeP286CanonicalConnectionCandidate current write))
      0 := by
  apply differentiableAt_pi.mpr
  intro pair
  exact
    (holonomicGaugeCurvature_coordinate_contDiff
      (diracDualFormNativeP286CanonicalConnectionCandidate current write)
      (canonicalConnectionCandidate_smooth current smooth write) pair
      ).differentiable (by simp) |>.differentiableAt

private theorem canonicalJointInput_differentiableAt
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    DifferentiableAt ℝ (canonicalJointInput current write) 0 :=
  (current_coframe_differentiableAt current smooth).prodMk
    (canonicalCandidate_curvature_differentiableAt current smooth write)

private theorem positiveSourceCanonicalActionInverse_differentiableAt
    (current : StageNineHolonomicConfiguration) :
    DifferentiableAt ℝ positiveSourceCanonicalActionInverse
      (1, holonomicP286GaugeCurvatureCoordinate current 0) :=
  formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_differentiableAt
    CanonicalBoundary 1 (by norm_num)
    (holonomicP286GaugeCurvatureCoordinate current 0)

private theorem canonicalCandidate_curvature_fderiv_apply
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) (direction : LorentzianIndex)
    (pair : Fin 6) :
    ((fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (diracDualFormNativeP286CanonicalConnectionCandidate current write))
        0) (coordinateDirection direction)) pair =
      fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (diracDualFormNativeP286CanonicalConnectionCandidate current write)
            point pair)
        0 direction := by
  unfold fieldDirectionalDerivative
  have derivativeEquality := fderiv_apply
    (canonicalCandidate_curvature_differentiableAt current smooth write) pair
  have applied := congrArg
    (fun derivative : BasePoint →L[ℝ] P286CoordinateCarrier =>
      derivative (coordinateDirection direction)) derivativeEquality
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] using applied.symm

private theorem canonicalCandidate_curvature_fderiv_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    (fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (diracDualFormNativeP286CanonicalConnectionCandidate current write))
        0) (coordinateDirection direction) =
      (fderiv ℝ
          (holonomicP286GaugeCurvatureCoordinate
            (diracDualFormNativeP286CanonicalConnectionCandidate current 0))
          0) (coordinateDirection direction) +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction := by
  funext pair
  calc
    ((fderiv ℝ
        (holonomicP286GaugeCurvatureCoordinate
          (diracDualFormNativeP286CanonicalConnectionCandidate current write))
        0) (coordinateDirection direction)) pair =
      fieldDirectionalDerivative
        (fun point =>
          holonomicP286GaugeCurvatureCoordinate
            (diracDualFormNativeP286CanonicalConnectionCandidate current write)
            point pair)
        0 direction :=
      canonicalCandidate_curvature_fderiv_apply current smooth write direction
        pair
    _ = fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate current point pair)
          0 direction +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      change
        fieldDirectionalDerivative
            (fun point =>
              holonomicP286GaugeCurvatureCoordinate
                (installP286HolonomicConnectionSecondJet current
                  (p286CanonicalDiagonalResponseSecondJet write) 1)
                point pair)
            0 direction = _
      rw [
        installP286HolonomicConnectionSecondJet_curvatureDirectionalDerivative_origin
          current smooth (p286CanonicalDiagonalResponseSecondJet write) 1
          direction pair]
      simp
    _ = fieldDirectionalDerivative
          (fun point =>
            holonomicP286GaugeCurvatureCoordinate
              (diracDualFormNativeP286CanonicalConnectionCandidate current 0)
              point pair)
          0 direction +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      rw [canonicalConnectionCandidate_zero current]
    _ = ((fderiv ℝ
          (holonomicP286GaugeCurvatureCoordinate
            (diracDualFormNativeP286CanonicalConnectionCandidate current 0))
          0) (coordinateDirection direction)) pair +
        p286HolonomicSecondJetCurvatureSymbol
          (p286CanonicalDiagonalResponseSecondJet write) direction pair := by
      rw [canonicalCandidate_curvature_fderiv_apply current smooth]

private theorem canonicalJointInput_fderiv_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    (fderiv ℝ (canonicalJointInput current write) 0)
        (coordinateDirection direction) =
      (fderiv ℝ (canonicalJointInput current 0) 0)
          (coordinateDirection direction) +
        (0,
          p286HolonomicSecondJetCurvatureSymbol
            (p286CanonicalDiagonalResponseSecondJet write) direction) := by
  change
    (fderiv ℝ
        (fun point =>
          (current.coframe point,
            holonomicP286GaugeCurvatureCoordinate
              (diracDualFormNativeP286CanonicalConnectionCandidate current
                write) point)) 0)
        (coordinateDirection direction) =
      (fderiv ℝ
          (fun point =>
            (current.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (diracDualFormNativeP286CanonicalConnectionCandidate current 0)
                point)) 0)
          (coordinateDirection direction) +
        (0,
          p286HolonomicSecondJetCurvatureSymbol
            (p286CanonicalDiagonalResponseSecondJet write) direction)
  have writeProductDerivative :=
    (current_coframe_differentiableAt current smooth).fderiv_prodMk
      (canonicalCandidate_curvature_differentiableAt current smooth write)
  have zeroProductDerivative :=
    (current_coframe_differentiableAt current smooth).fderiv_prodMk
      (canonicalCandidate_curvature_differentiableAt current smooth 0)
  have writeProductDerivativeAt :
      (fderiv ℝ
          (fun point : BasePoint =>
            (current.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (diracDualFormNativeP286CanonicalConnectionCandidate current
                  write) point)) 0)
          (coordinateDirection direction) =
        ((fderiv ℝ current.coframe 0).prod
          (fderiv ℝ
            (holonomicP286GaugeCurvatureCoordinate
              (diracDualFormNativeP286CanonicalConnectionCandidate current
                write)) 0))
          (coordinateDirection direction) :=
    congrArg
      (fun derivative : BasePoint →L[ℝ]
          (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) =>
        derivative (coordinateDirection direction))
      writeProductDerivative
  have zeroProductDerivativeAt :
      (fderiv ℝ
          (fun point : BasePoint =>
            (current.coframe point,
              holonomicP286GaugeCurvatureCoordinate
                (diracDualFormNativeP286CanonicalConnectionCandidate current 0)
                point)) 0)
          (coordinateDirection direction) =
        ((fderiv ℝ current.coframe 0).prod
          (fderiv ℝ
            (holonomicP286GaugeCurvatureCoordinate
              (diracDualFormNativeP286CanonicalConnectionCandidate current 0))
            0))
          (coordinateDirection direction) :=
    congrArg
      (fun derivative : BasePoint →L[ℝ]
          (LorentzianCoframe × FormNativeP286GaugeCoordinateTwoForm) =>
        derivative (coordinateDirection direction))
      zeroProductDerivative
  rw [writeProductDerivativeAt, zeroProductDerivativeAt]
  apply Prod.ext
  · simp
  · exact canonicalCandidate_curvature_fderiv_affine current smooth write
      direction

private theorem canonicalJointCandidate_auxiliary_fderiv
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    fderiv ℝ
        (holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write)) 0 =
      (fderiv ℝ positiveSourceCanonicalActionInverse
          (1, holonomicP286GaugeCurvatureCoordinate current 0)).comp
        (fderiv ℝ (canonicalJointInput current write) 0) := by
  have outerAtOrigin :
      HasFDerivAt positiveSourceCanonicalActionInverse
        (fderiv ℝ positiveSourceCanonicalActionInverse
          (1, holonomicP286GaugeCurvatureCoordinate current 0))
        (canonicalJointInput current write 0) := by
    simpa [canonicalJointInput_origin current smooth coframeOrigin] using
      (positiveSourceCanonicalActionInverse_differentiableAt current
        ).hasFDerivAt
  have composed := outerAtOrigin.comp 0
    (canonicalJointInput_differentiableAt current smooth write).hasFDerivAt
  have auxiliaryFunction :
      holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) =
        positiveSourceCanonicalActionInverse ∘
          canonicalJointInput current write := by
    funext point
    exact canonicalJointCandidate_auxiliaryCoordinate current write point
  rw [auxiliaryFunction]
  exact composed.fderiv

private theorem canonicalJointCandidate_auxiliaryDerivative_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 direction =
      p286GaugeAuxiliaryDirectionalDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 direction +
        p286HolonomicSecondJetConstitutiveAuxiliaryResponse
          (p286CanonicalDiagonalResponseSecondJet write) direction := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [canonicalJointCandidate_auxiliary_fderiv current smooth coframeOrigin
    write]
  simp only [ContinuousLinearMap.comp_apply]
  rw [canonicalJointInput_fderiv_affine current smooth write direction,
    map_add,
    fixedP506L0P286CanonicalActionInverse_fderiv_vertical,
    fixedP506L0P286CanonicalActionInverse_vertical_eq_secondJetResponse]
  rw [canonicalJointCandidate_auxiliary_fderiv current smooth coframeOrigin 0]
  simp only [ContinuousLinearMap.comp_apply]

private theorem canonicalJointCandidate_exteriorDerivative_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    holonomicP286GaugeAuxiliaryExteriorDerivative
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (p286HolonomicSecondJetConstitutiveAuxiliaryResponse
            (p286CanonicalDiagonalResponseSecondJet write)) := by
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
  rw [show
    p286GaugeAuxiliaryDirectionalDerivative
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      p286GaugeAuxiliaryDirectionalDerivative
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 +
        p286HolonomicSecondJetConstitutiveAuxiliaryResponse
          (p286CanonicalDiagonalResponseSecondJet write) by
    funext direction
    exact canonicalJointCandidate_auxiliaryDerivative_affine current smooth
      coframeOrigin write direction]
  exact pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative_add_local _ _

private theorem canonicalJointCandidate_connectionExteriorAction_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0)
        (holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0) =
      pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0)
        (holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0) := by
  have auxiliaryCoordinateEquality :
      holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0 =
        holonomicP286GaugeAuxiliaryCoordinate
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 := by
    funext pair
    exact congrArg p286CoordinateEquiv
      (congrFun (canonicalJointCandidate_auxiliary_origin current smooth write)
        pair)
  rw [canonicalJointCandidate_connection_origin current write,
    canonicalJointCandidate_connection_origin current 0,
    auxiliaryCoordinateEquality]

private theorem canonicalJointCandidate_chargedThreeForm_origin
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (write : P286GaugeOneForm) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current write) 0) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0) := by
  rw [canonicalJointCandidate_pointField_origin current smooth write]

private theorem canonicalJointCandidate_eulerThreeForm_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        (diracDualFormNativeP286CanonicalJointCandidate
          positiveSmoothUnifiedSource current write) 0 =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
          (diracDualFormNativeP286CanonicalJointCandidate
            positiveSmoothUnifiedSource current 0) 0 +
        pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
          (p286HolonomicSecondJetConstitutiveAuxiliaryResponse
            (p286CanonicalDiagonalResponseSecondJet write)) := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts,
    canonicalJointCandidate_exteriorDerivative_affine current smooth
      coframeOrigin write,
    canonicalJointCandidate_connectionExteriorAction_origin current smooth
      write,
    canonicalJointCandidate_chargedThreeForm_origin current smooth write]
  abel

/-! ## Uniform positive-source action zero fiber -/

/-- On every smooth identity-coframe current, the canonical principal has the
same affine action-dual law as the original fixed contact. -/
theorem positiveSourceCanonicalOriginActionDual_eq_affine
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    diracDualFormNativeP286CanonicalOriginActionDual
        positiveSmoothUnifiedSource current write =
      diracDualFormNativeP286CanonicalOriginActionForcing
          positiveSmoothUnifiedSource current -
        p286GaugeOneFormPairingEquiv write := by
  unfold diracDualFormNativeP286CanonicalOriginActionDual
    diracDualFormNativeP286CanonicalOriginActionForcing
  rw [canonicalJointCandidate_eulerThreeForm_affine current smooth
      coframeOrigin write,
    p286GaugeThreeFormWedgeLinearDual_add_local,
    p286HolonomicSecondJetConstitutiveAuxiliaryResponse_w13]
  have canonicalResponse :
      p286HolonomicSecondJetEulerLagrangeResponse
          (p286CanonicalDiagonalResponseSecondJet write) =
        p286GaugeOneFormPairingEquiv write := by
    apply LinearMap.ext
    intro direction
    rw [p286CanonicalDiagonalResponseSecondJet_response,
      p286GaugeOneFormPairingEquiv_apply]
  rw [canonicalResponse]
  rfl

/-- The source/current action forcing selects a zero of its own complete
origin action dual; no residual coordinate is used to construct the write. -/
theorem positiveSourceCanonicalGeneratedWrite_actionDual_zero
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1) :
    diracDualFormNativeP286CanonicalOriginActionDual
        positiveSmoothUnifiedSource current
        (diracDualFormNativeP286CanonicalGeneratedWrite
          positiveSmoothUnifiedSource current) = 0 := by
  rw [positiveSourceCanonicalOriginActionDual_eq_affine current smooth
    coframeOrigin]
  unfold diracDualFormNativeP286CanonicalGeneratedWrite
  rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
  exact sub_self _

/-- Nondegeneracy of the action pairing makes the generated write the unique
zero of the complete origin action dual. -/
theorem positiveSourceCanonicalOriginActionDual_eq_zero_iff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1)
    (write : P286GaugeOneForm) :
    diracDualFormNativeP286CanonicalOriginActionDual
        positiveSmoothUnifiedSource current write = 0 ↔
      write = diracDualFormNativeP286CanonicalGeneratedWrite
        positiveSmoothUnifiedSource current := by
  rw [positiveSourceCanonicalOriginActionDual_eq_affine current smooth
    coframeOrigin]
  constructor
  · intro actionZero
    have pairingEquality :
        p286GaugeOneFormPairingEquiv write =
          diracDualFormNativeP286CanonicalOriginActionForcing
            positiveSmoothUnifiedSource current :=
      (sub_eq_zero.mp actionZero).symm
    apply p286GaugeOneFormPairingEquiv.injective
    unfold diracDualFormNativeP286CanonicalGeneratedWrite
    rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
    exact pairingEquality
  · intro writeEquality
    rw [writeEquality]
    unfold diracDualFormNativeP286CanonicalGeneratedWrite
    rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
    exact sub_self _

/-- The generated actual consequently satisfies the native P286 Euler
three-form at the same contact. -/
theorem positiveSourceCanonicalGeneratedActual_eulerThreeForm_origin_zero
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (coframeOrigin : current.coframe 0 = 1) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        (diracDualFormNativeP286CanonicalGeneratedActual
          positiveSmoothUnifiedSource current) 0 = 0 := by
  apply (p286GaugeThreeFormWedgeLinearDual_eq_zero_iff _).1
  exact positiveSourceCanonicalGeneratedWrite_actionDual_zero current smooth
    coframeOrigin

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionProducerSoundness

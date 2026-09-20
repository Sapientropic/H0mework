import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.Matter.ConjugateMatterActionTimeVelocity
import H0mework.Physics.Matter.MatterVariation
import H0mework.Physics.ScalarJets.ScalarActionSecondJetLocalActualLift

/-!
# S9-C3h182: action-generated temporal first-germ matter response

For a smooth nondegenerate actual whose coframe is the identity, this module
reads the temporal first germ of the actual Dirac--Yukawa vector, applies the
already proved involutive temporal principal, and installs the resulting
acceleration by the canonical `1 / 2 * t^2` matter-coordinate correction.

The acceleration is computed from the action residual.  It is not supplied by
the source, selected from a branch, or reconstructed field-by-field from an
endpoint.  Substitution of the generated correction back into the same
Dirac--Yukawa first-germ equation is recorded only as producer soundness.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineMatterActionTemporalFirstGermResponse

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ActionVelocityLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open StageNineScalarActionSecondJetLocalActualLift
open SU7ExteriorBreakingYukawa
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-! ## Canonical matter-coordinate second jet -/

/-- The canonical quadratic physical-time correction, written in the actual
matter coordinate chart. -/
def matterQuadraticTimeCoordinateCorrection
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) : MatterCoordinateCarrier :=
  scalarQuadraticTimeCoefficient point •
    matterCoordinateEquiv acceleration

@[simp] theorem matterQuadraticTimeCoordinateCorrection_origin
    (acceleration : DiracExteriorMatterCarrier) :
    matterQuadraticTimeCoordinateCorrection acceleration 0 = 0 := by
  simp [matterQuadraticTimeCoordinateCorrection]

theorem matterQuadraticTimeCoordinateCorrection_directionalDerivative
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterQuadraticTimeCoordinateCorrection acceleration) point direction =
      if direction = canonicalLorentzianTimeDirection then
        point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv acceleration
      else
        0 := by
  have derivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt point).smul_const
      (matterCoordinateEquiv acceleration)
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun candidate =>
        scalarQuadraticTimeCoefficient candidate •
          matterCoordinateEquiv acceleration)
      point)
      (coordinateDirection direction) = _
  rw [derivative.fderiv]
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]
  all_goals ring_nf

@[simp] theorem
    matterQuadraticTimeCoordinateCorrection_directionalDerivative_origin
    (acceleration : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterQuadraticTimeCoordinateCorrection acceleration) 0 direction =
      0 := by
  rw [matterQuadraticTimeCoordinateCorrection_directionalDerivative]
  split_ifs <;> simp

theorem matterQuadraticTimeCoordinateCorrection_secondTimeDerivative_origin
    (acceleration : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative
            (matterQuadraticTimeCoordinateCorrection acceleration) point
            canonicalLorentzianTimeDirection)
        0 canonicalLorentzianTimeDirection =
      matterCoordinateEquiv acceleration := by
  rw [show
    (fun point =>
      fieldDirectionalDerivative
        (matterQuadraticTimeCoordinateCorrection acceleration) point
        canonicalLorentzianTimeDirection) =
      fun point =>
        point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv acceleration by
    funext point
    simpa using
      matterQuadraticTimeCoordinateCorrection_directionalDerivative
        acceleration point canonicalLorentzianTimeDirection]
  unfold fieldDirectionalDerivative
  have derivative :=
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      (x := (0 : BasePoint))
      |>.smul_const (matterCoordinateEquiv acceleration)
  rw [show
    (fun point : BasePoint =>
      point canonicalLorentzianTimeDirection •
        matterCoordinateEquiv acceleration) =
      fun point =>
        localBaseCoordinate canonicalLorentzianTimeDirection point •
          matterCoordinateEquiv acceleration by
    rfl,
    derivative.fderiv]
  simp [coordinateDirection]

theorem matterQuadraticTimeCoordinateCorrection_coordinate_smooth
    (acceleration : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (matterQuadraticTimeCoordinateCorrection acceleration) := by
  have coefficientSmooth : ContDiff ℝ ∞ scalarQuadraticTimeCoefficient := by
    unfold scalarQuadraticTimeCoefficient
    exact contDiff_const.mul
      ((localBaseCoordinate canonicalLorentzianTimeDirection).contDiff.mul
        (localBaseCoordinate canonicalLorentzianTimeDirection).contDiff)
  exact coefficientSmooth.smul contDiff_const

/-! ## Involutive action response -/

/-- The temporal first-germ equation after separating its already-known
action residual from the new matter acceleration. -/
def MatterTemporalFirstGermResponseLaw
    (residual acceleration : DiracExteriorMatterCarrier) : Prop :=
  residual +
      identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
        acceleration =
    0

/-- The action itself generates the acceleration.  There is no free response
coordinate: the temporal principal is applied to the actual residual. -/
def actionGeneratedMatterTemporalAcceleration
    (residual : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  -identityCoframeMatterPrincipal canonicalLorentzianTimeDirection residual

/-- Producer-soundness only: substituting the action-generated acceleration
back into the same first-germ equation closes that equation. -/
theorem actionGeneratedMatterTemporalAcceleration_producerSound
    (residual : DiracExteriorMatterCarrier) :
    MatterTemporalFirstGermResponseLaw residual
      (actionGeneratedMatterTemporalAcceleration residual) := by
  unfold MatterTemporalFirstGermResponseLaw
    actionGeneratedMatterTemporalAcceleration
  rw [map_neg, identityCoframeMatterPrincipal_time_involutive]
  simp

/-- Involutivity removes every hidden response branch. -/
theorem matterTemporalFirstGermResponseLaw_unique
    (residual candidate : DiracExteriorMatterCarrier)
    (candidateLaw :
      MatterTemporalFirstGermResponseLaw residual candidate) :
    candidate = actionGeneratedMatterTemporalAcceleration residual := by
  have principalEquality :
      identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          candidate =
        identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          (actionGeneratedMatterTemporalAcceleration residual) := by
    have generatedLaw :=
      actionGeneratedMatterTemporalAcceleration_producerSound residual
    unfold MatterTemporalFirstGermResponseLaw at candidateLaw generatedLaw
    exact add_left_cancel (candidateLaw.trans generatedLaw.symm)
  calc
    candidate =
        identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            candidate) :=
      (identityCoframeMatterPrincipal_time_involutive candidate).symm
    _ =
        identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            (actionGeneratedMatterTemporalAcceleration residual)) := by
      rw [principalEquality]
    _ = actionGeneratedMatterTemporalAcceleration residual :=
      identityCoframeMatterPrincipal_time_involutive _

/-- The canonical response does not manufacture motion on the zero fiber and
cannot hide a nonzero action residual. -/
theorem actionGeneratedMatterTemporalAcceleration_eq_zero_iff
    (residual : DiracExteriorMatterCarrier) :
    actionGeneratedMatterTemporalAcceleration residual = 0 ↔ residual = 0 := by
  constructor
  · intro accelerationZero
    have principalZero := congrArg
      (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection)
      accelerationZero
    rw [actionGeneratedMatterTemporalAcceleration, map_neg,
      identityCoframeMatterPrincipal_time_involutive] at principalZero
    simpa using principalZero
  · rintro rfl
    simp [actionGeneratedMatterTemporalAcceleration]

/-! ## Installation on an already generated actual -/

/-- Install only the canonical matter second jet.  Every other actual field is
retained definitionally. -/
def installMatterTemporalFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  varyMatterCoordinates configuration
    (matterQuadraticTimeCoordinateCorrection acceleration) 1

@[simp] theorem installMatterTemporalFirstGermResponse_coframe
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem installMatterTemporalFirstGermResponse_gravityConnection
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).gravityConnection =
      configuration.gravityConnection :=
  rfl

@[simp] theorem installMatterTemporalFirstGermResponse_gaugeConnection
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).gaugeConnection =
      configuration.gaugeConnection :=
  rfl

@[simp] theorem installMatterTemporalFirstGermResponse_scalar
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).scalar =
      configuration.scalar :=
  rfl

@[simp] theorem installMatterTemporalFirstGermResponse_conjugateMatter
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).conjugateMatter =
      configuration.conjugateMatter :=
  rfl

theorem installMatterTemporalFirstGermResponse_matter_coordinate
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterCoordinateEquiv
        ((installMatterTemporalFirstGermResponse configuration acceleration).matter
          point) =
      matterCoordinateEquiv (configuration.matter point) +
        matterQuadraticTimeCoordinateCorrection acceleration point := by
  simp [installMatterTemporalFirstGermResponse, varyMatterCoordinates]

@[simp] theorem installMatterTemporalFirstGermResponse_matter_origin
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).matter 0 =
      configuration.matter 0 := by
  apply matterCoordinateEquiv.injective
  simp [installMatterTemporalFirstGermResponse_matter_coordinate]

theorem installMatterTemporalFirstGermResponse_matter_firstJet_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((installMatterTemporalFirstGermResponse configuration acceleration).matter
            point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv (configuration.matter point)) 0 :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have correctionDifferentiable : DifferentiableAt ℝ
      (matterQuadraticTimeCoordinateCorrection acceleration) 0 :=
    (matterQuadraticTimeCoordinateCorrection_coordinate_smooth acceleration)
      |>.differentiable (by simp) |>.differentiableAt
  unfold fieldDirectionalDerivative
  rw [show
    (fun point => matterCoordinateEquiv
      ((installMatterTemporalFirstGermResponse configuration acceleration).matter
        point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterQuadraticTimeCoordinateCorrection acceleration by
    funext point
    exact installMatterTemporalFirstGermResponse_matter_coordinate
      configuration acceleration point]
  rw [fderiv_add backgroundDifferentiable correctionDifferentiable]
  change
    (fderiv ℝ (fun point => matterCoordinateEquiv (configuration.matter point)) 0 +
        fderiv ℝ (matterQuadraticTimeCoordinateCorrection acceleration) 0)
        (coordinateDirection direction) = _
  rw [add_apply]
  have correctionZero :=
    matterQuadraticTimeCoordinateCorrection_directionalDerivative_origin
      acceleration direction
  unfold fieldDirectionalDerivative at correctionZero
  rw [correctionZero, add_zero]

theorem installMatterTemporalFirstGermResponse_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  refine
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, ?_, conjugateMatterSmooth⟩
  rw [show
    (fun point => matterCoordinateEquiv
      ((installMatterTemporalFirstGermResponse configuration acceleration).matter
        point)) =
      (fun point => matterCoordinateEquiv (configuration.matter point)) +
        matterQuadraticTimeCoordinateCorrection acceleration by
    funext point
    exact installMatterTemporalFirstGermResponse_matter_coordinate
      configuration acceleration point]
  exact matterSmooth.add
    (matterQuadraticTimeCoordinateCorrection_coordinate_smooth acceleration)

theorem installMatterTemporalFirstGermResponse_nondegenerate
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (acceleration : DiracExteriorMatterCarrier) :
    (installMatterTemporalFirstGermResponse configuration acceleration).Nondegenerate := by
  simpa [StageNineHolonomicConfiguration.Nondegenerate] using nondegenerate

/-- On the residual zero fiber the canonical response is literally the input
actual, not merely first-jet equivalent to it. -/
theorem installMatterTemporalFirstGermResponse_zero
    (configuration : StageNineHolonomicConfiguration) :
    installMatterTemporalFirstGermResponse configuration 0 = configuration := by
  cases configuration
  simp [installMatterTemporalFirstGermResponse, varyMatterCoordinates,
    matterQuadraticTimeCoordinateCorrection]

/-- The canonical quadratic realization is faithful: it is the identity
exactly when its generated acceleration is zero.  Evaluation at the unit
physical-time point prevents a nonzero response from disappearing into an
unobserved third sink. -/
theorem installMatterTemporalFirstGermResponse_eq_iff
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier) :
    installMatterTemporalFirstGermResponse configuration acceleration =
        configuration ↔
      acceleration = 0 := by
  constructor
  · intro actualEq
    have matterEq := congrArg
      (fun candidate : StageNineHolonomicConfiguration =>
        matterCoordinateEquiv
          (candidate.matter
            (coordinateDirection canonicalLorentzianTimeDirection)))
      actualEq
    rw [installMatterTemporalFirstGermResponse_matter_coordinate] at matterEq
    have correctionZero :
        matterQuadraticTimeCoordinateCorrection acceleration
            (coordinateDirection canonicalLorentzianTimeDirection) =
          0 := by
      exact add_left_cancel
        (show
          matterCoordinateEquiv
                (configuration.matter
                  (coordinateDirection canonicalLorentzianTimeDirection)) +
              matterQuadraticTimeCoordinateCorrection acceleration
                (coordinateDirection canonicalLorentzianTimeDirection) =
            matterCoordinateEquiv
                (configuration.matter
                  (coordinateDirection canonicalLorentzianTimeDirection)) +
              0 by
          simpa using matterEq)
    have scaledZero :
        (1 / 2 : ℝ) • matterCoordinateEquiv acceleration = 0 := by
      simpa [matterQuadraticTimeCoordinateCorrection,
        scalarQuadraticTimeCoefficient, localBaseCoordinate,
        coordinateDirection, canonicalLorentzianTimeDirection] using
        correctionZero
    have coordinateZero : matterCoordinateEquiv acceleration = 0 :=
      (smul_eq_zero.mp scaledZero).resolve_left (by norm_num)
    apply matterCoordinateEquiv.injective
    simpa using coordinateZero
  · rintro rfl
    exact installMatterTemporalFirstGermResponse_zero configuration

/-! ## Actual variation normal form -/

def matterQuadraticConnectionAction
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction
      (diracSpinConnectionLift
        (configuration.gravityConnection point) direction)
      acceleration +
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (configuration.gaugeConnection point direction))
      acceleration

theorem matterQuadraticVariationCovariantDerivative_normalForm
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterVariationCovariantDerivative configuration
        (matterQuadraticTimeCoordinateCorrection acceleration) point direction =
      (if direction = canonicalLorentzianTimeDirection then
          point canonicalLorentzianTimeDirection • acceleration
        else
          0) +
        scalarQuadraticTimeCoefficient point •
          matterQuadraticConnectionAction configuration acceleration point
            direction := by
  unfold holonomicMatterVariationCovariantDerivative
    matterVariationCoordinateDerivative matterQuadraticConnectionAction
  rw [matterQuadraticTimeCoordinateCorrection_directionalDerivative]
  have correctionCarrier :
      matterCoordinateEquiv.symm
          (matterQuadraticTimeCoordinateCorrection acceleration point) =
        scalarQuadraticTimeCoefficient point • acceleration := by
    simp [matterQuadraticTimeCoordinateCorrection,
      matterCoordinateEquiv_symm_real_smul]
  rw [correctionCarrier]
  rw [diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  split_ifs <;>
    simp [matterCoordinateEquiv_symm_real_smul]
  all_goals module

theorem matterCoordinateDerivative_installMatterTemporalFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => matterCoordinateEquiv
          ((installMatterTemporalFirstGermResponse configuration acceleration).matter
            candidate))
        point direction =
      fieldDirectionalDerivative
          (fun candidate => matterCoordinateEquiv
            (configuration.matter candidate))
          point direction +
        matterVariationCoordinateDerivative
          (matterQuadraticTimeCoordinateCorrection acceleration)
          point direction := by
  have backgroundDifferentiable : DifferentiableAt ℝ
      (fun candidate => matterCoordinateEquiv
        (configuration.matter candidate)) point :=
    (smooth.2.2.2.2.2.2.2.1.differentiable (by simp)).differentiableAt
  have correctionDifferentiable : DifferentiableAt ℝ
      (matterQuadraticTimeCoordinateCorrection acceleration) point :=
    (matterQuadraticTimeCoordinateCorrection_coordinate_smooth acceleration)
      |>.differentiable (by simp) |>.differentiableAt
  unfold fieldDirectionalDerivative matterVariationCoordinateDerivative
  rw [show
    (fun candidate => matterCoordinateEquiv
      ((installMatterTemporalFirstGermResponse configuration acceleration).matter
        candidate)) =
      (fun candidate => matterCoordinateEquiv
        (configuration.matter candidate)) +
        matterQuadraticTimeCoordinateCorrection acceleration by
    funext candidate
    exact installMatterTemporalFirstGermResponse_matter_coordinate
      configuration acceleration candidate]
  rw [fderiv_add backgroundDifferentiable correctionDifferentiable, add_apply]
  rfl

theorem
    holonomicMatterCovariantDerivative_installMatterTemporalFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    holonomicMatterCovariantDerivative
        (installMatterTemporalFirstGermResponse configuration acceleration)
        point direction =
      holonomicMatterCovariantDerivative configuration point direction +
        holonomicMatterVariationCovariantDerivative configuration
          (matterQuadraticTimeCoordinateCorrection acceleration)
          point direction := by
  unfold holonomicMatterCovariantDerivative
    holonomicMatterVariationCovariantDerivative
  rw [matterCoordinateDerivative_installMatterTemporalFirstGermResponse
    configuration smooth]
  simp only [installMatterTemporalFirstGermResponse,
    varyMatterCoordinates, matterCoordinateEquiv.symm_apply_apply,
    map_add, matterCoordinateEquiv_symm_real_smul]
  rw [diracMatrixMatterAction_real_smul,
    diracExteriorMotherLieAction_matter_real_smul]
  module

theorem toContinuumPointField_installMatterTemporalFirstGermResponse
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    toContinuumPointField
        (installMatterTemporalFirstGermResponse configuration acceleration)
        point =
      withMatterJets (toContinuumPointField configuration point)
        (configuration.matter point +
          matterCoordinateEquiv.symm
            (matterQuadraticTimeCoordinateCorrection acceleration point))
        (holonomicMatterCovariantDerivative configuration point +
          holonomicMatterVariationCovariantDerivative configuration
            (matterQuadraticTimeCoordinateCorrection acceleration) point) := by
  apply StageNineContinuumPointField.ext
  all_goals try rfl
  · simp [toContinuumPointField, withMatterJets,
      installMatterTemporalFirstGermResponse, varyMatterCoordinates, map_add]
  · funext direction
    exact
      holonomicMatterCovariantDerivative_installMatterTemporalFirstGermResponse
        configuration smooth acceleration point direction

theorem generatedContinuumMatterVector_installMatterTemporalFirstGermResponse
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    generatedContinuumMatterVector source 0 point
        (toContinuumPointField
          (installMatterTemporalFirstGermResponse configuration acceleration)
          point) =
      generatedContinuumMatterVector source 0 point
          (toContinuumPointField configuration point) +
        matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          (matterCoordinateEquiv.symm
            (matterQuadraticTimeCoordinateCorrection acceleration point))
          (holonomicMatterVariationCovariantDerivative configuration
            (matterQuadraticTimeCoordinateCorrection acceleration) point) := by
  rw [toContinuumPointField_installMatterTemporalFirstGermResponse
    configuration smooth]
  have affine :=
    generatedContinuumMatterVector_withMatterJets_affine source point
      (toContinuumPointField configuration point)
      (matterCoordinateEquiv.symm
        (matterQuadraticTimeCoordinateCorrection acceleration point))
      (holonomicMatterVariationCovariantDerivative configuration
        (matterQuadraticTimeCoordinateCorrection acceleration) point)
      1
  have matterOne :
      (1 : ℝ) • matterCoordinateEquiv.symm
          (matterQuadraticTimeCoordinateCorrection acceleration point) =
        matterCoordinateEquiv.symm
          (matterQuadraticTimeCoordinateCorrection acceleration point) := by
    module
  have derivativeOne :
      (1 : ℝ) •
          holonomicMatterVariationCovariantDerivative configuration
            (matterQuadraticTimeCoordinateCorrection acceleration) point =
        holonomicMatterVariationCovariantDerivative configuration
          (matterQuadraticTimeCoordinateCorrection acceleration) point := by
    module
  have variationOne :
      (1 : ℝ) • matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          (matterCoordinateEquiv.symm
            (matterQuadraticTimeCoordinateCorrection acceleration point))
          (holonomicMatterVariationCovariantDerivative configuration
            (matterQuadraticTimeCoordinateCorrection acceleration) point) =
        matterFieldVariationVector source point
          (toContinuumPointField configuration point)
          (matterCoordinateEquiv.symm
            (matterQuadraticTimeCoordinateCorrection acceleration point))
          (holonomicMatterVariationCovariantDerivative configuration
            (matterQuadraticTimeCoordinateCorrection acceleration) point) := by
    module
  rw [matterOne, derivativeOne, variationOne] at affine
  simpa [toContinuumPointField] using affine

theorem generatedContinuumMatterVector_installMatterTemporalFirstGermResponse_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (installMatterTemporalFirstGermResponse configuration acceleration)
          0) =
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) := by
  rw [generatedContinuumMatterVector_installMatterTemporalFirstGermResponse
    source configuration smooth]
  have covariantVariationZero :
      holonomicMatterVariationCovariantDerivative configuration
          (matterQuadraticTimeCoordinateCorrection acceleration) 0 =
        0 := by
    exact holonomicMatterVariationCovariantDerivative_eq_zero_of_jet_zero
      configuration (matterQuadraticTimeCoordinateCorrection acceleration) 0
      (matterQuadraticTimeCoordinateCorrection_origin acceleration)
      (matterQuadraticTimeCoordinateCorrection_directionalDerivative_origin
        acceleration)
  rw [matterQuadraticTimeCoordinateCorrection_origin, map_zero,
    covariantVariationZero, matterFieldVariationVector_zero, add_zero]

/-- Identity coframe on the full local germ.  This is a geometric property of
the input actual, not a response certificate. -/
def HasIdentityCoframe
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  configuration.coframe = fun _ => (1 : LorentzianCoframe)

def matterQuadraticDiracRemainder
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        diracMatrixMatterAction (diracGamma direction)
          (matterQuadraticConnectionAction configuration acceleration point
            direction) +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm (configuration.scalar point)) acceleration

theorem matterQuadraticVariationVector_normalForm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (identityCoframe : HasIdentityCoframe configuration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterFieldVariationVector source point
        (toContinuumPointField configuration point)
        (matterCoordinateEquiv.symm
          (matterQuadraticTimeCoordinateCorrection acceleration point))
        (holonomicMatterVariationCovariantDerivative configuration
          (matterQuadraticTimeCoordinateCorrection acceleration) point) =
      point canonicalLorentzianTimeDirection •
          identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            acceleration +
        scalarQuadraticTimeCoefficient point •
          matterQuadraticDiracRemainder configuration acceleration point := by
  classical
  have coframePoint : configuration.coframe point = 1 := by
    exact congrFun identityCoframe point
  have correctionCarrier :
      matterCoordinateEquiv.symm
          (matterQuadraticTimeCoordinateCorrection acceleration point) =
        scalarQuadraticTimeCoefficient point • acceleration := by
    simp [matterQuadraticTimeCoordinateCorrection,
      matterCoordinateEquiv_symm_real_smul]
  have timeSum :
      (∑ direction : LorentzianIndex,
        diracMatrixMatterAction (diracGamma direction)
          (if direction = canonicalLorentzianTimeDirection then
              point canonicalLorentzianTimeDirection • acceleration
            else
              0)) =
        point canonicalLorentzianTimeDirection •
          diracMatrixMatterAction
            (diracGamma canonicalLorentzianTimeDirection) acceleration := by
    rw [Fin.sum_univ_four]
    simp [canonicalLorentzianTimeDirection]
  have gammaIdentity (direction : LorentzianIndex) :
      inverseCoframeDiracGamma
          { coframe := configuration.coframe point, derivative := 0 }
          direction =
        diracGamma direction := by
    rw [coframePoint]
    change
      inverseCoframeDiracGamma identityCoframeMatterGeometry direction =
        diracGamma direction
    exact inverseCoframeDiracGamma_identity direction
  have connectionSum :
      (∑ direction : LorentzianIndex,
        scalarQuadraticTimeCoefficient point •
          diracMatrixMatterAction (diracGamma direction)
            (matterQuadraticConnectionAction configuration acceleration point
              direction)) =
        scalarQuadraticTimeCoefficient point •
          ∑ direction : LorentzianIndex,
            diracMatrixMatterAction (diracGamma direction)
              (matterQuadraticConnectionAction configuration acceleration point
                direction) := by
    exact
      (Finset.smul_sum
        (M := ℝ) (N := DiracExteriorMatterCarrier)
        (r := scalarQuadraticTimeCoefficient point)
        (f := fun direction : LorentzianIndex =>
          diracMatrixMatterAction (diracGamma direction)
            (matterQuadraticConnectionAction configuration acceleration point
              direction))
        (s := Finset.univ)).symm
  unfold matterFieldVariationVector
  rw [matterGaugeKineticSum_zeroChart]
  simp only [toContinuumPointField]
  simp_rw [gammaIdentity]
  simp_rw [matterQuadraticVariationCovariantDerivative_normalForm]
  simp_rw [map_add]
  rw [Finset.sum_add_distrib, timeSum]
  simp_rw [diracMatrixMatterAction_real_smul]
  rw [connectionSum, correctionCarrier,
    chiralExteriorYukawaAction_matter_real_smul]
  unfold matterQuadraticDiracRemainder identityCoframeMatterPrincipal
  simp only [LinearMap.smul_apply]
  rw [smul_add]
  rw [smul_comm Complex.I
    (point canonicalLorentzianTimeDirection)]
  rw [smul_comm Complex.I (scalarQuadraticTimeCoefficient point)]
  module

def constantMatterConfiguration
    (configuration : StageNineHolonomicConfiguration)
    (matter : DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { configuration with matter := fun _ => matter }

theorem constantMatterConfiguration_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (matter : DiracExteriorMatterCarrier) :
    (constantMatterConfiguration configuration matter).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, _matterSmooth, conjugateMatterSmooth⟩
  have constantMatterSmooth : ContDiff ℝ ∞ fun _ : BasePoint =>
      matterCoordinateEquiv matter := contDiff_const
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, by
        simpa [constantMatterConfiguration] using constantMatterSmooth,
      conjugateMatterSmooth⟩

theorem matterQuadraticConnectionAction_eq_constantMatterCovariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint)
    (direction : LorentzianIndex) :
    matterQuadraticConnectionAction configuration acceleration point direction =
      holonomicMatterCovariantDerivative
        (constantMatterConfiguration configuration acceleration)
        point direction := by
  unfold matterQuadraticConnectionAction holonomicMatterCovariantDerivative
    constantMatterConfiguration fieldDirectionalDerivative
  simp

theorem matterQuadraticConnectionAction_coordinate_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (matterQuadraticConnectionAction configuration acceleration point
          direction) := by
  rw [show
    (fun point =>
      matterCoordinateEquiv
        (matterQuadraticConnectionAction configuration acceleration point
          direction)) =
      fun point =>
        matterCoordinateEquiv
          (holonomicMatterCovariantDerivative
            (constantMatterConfiguration configuration acceleration)
            point direction) by
    funext point
    rw [matterQuadraticConnectionAction_eq_constantMatterCovariantDerivative]]
  exact holonomicMatterCovariantDerivative_coordinate_contDiff_local
    (constantMatterConfiguration configuration acceleration)
    (constantMatterConfiguration_smooth configuration smooth acceleration)
    direction

theorem matterQuadraticDiracRemainder_coordinate_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration acceleration point) := by
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (matterQuadraticConnectionAction configuration acceleration point
              direction)) := by
    intro direction
    let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      (diracMatrixMatterCoordinateRealBilinear (diracGamma direction))
        |>.toContinuousLinearMap
    have actual := actionLinear.contDiff.comp
      (matterQuadraticConnectionAction_coordinate_smooth
        configuration smooth acceleration direction)
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (matterQuadraticConnectionAction configuration acceleration point
                direction)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (matterQuadraticConnectionAction configuration acceleration point
              direction)) := by
    exact ContDiff.sum fun direction _ => kineticDirectionSmooth direction
  have kineticSmooth : ContDiff ℝ ∞ fun point =>
      Complex.I •
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma direction)
              (matterQuadraticConnectionAction configuration acceleration point
                direction)) := by
    have iSmooth : ContDiff ℝ ∞ fun _ : BasePoint => (Complex.I : ℂ) :=
      contDiff_const
    exact iSmooth.smul kineticSumSmooth
  have yukawaSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          acceleration) := by
    have accelerationSmooth : ContDiff ℝ ∞ fun _ : BasePoint =>
        matterCoordinateEquiv acceleration := contDiff_const
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply accelerationSmooth
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv acceleration))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  unfold matterQuadraticDiracRemainder
  simp only [map_add, map_smul, map_sum]
  exact kineticSmooth.add yukawaSmooth

theorem matterQuadraticWeightedRemainder_hasFDerivAt_origin_zero
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (acceleration : DiracExteriorMatterCarrier) :
    HasFDerivAt
      (fun point =>
        scalarQuadraticTimeCoefficient point •
          matterCoordinateEquiv
            (matterQuadraticDiracRemainder configuration acceleration point))
      (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0 := by
  have remainderDifferentiableAt : DifferentiableAt ℝ
      (fun point => matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration acceleration point))
      (0 : BasePoint) :=
    (matterQuadraticDiracRemainder_coordinate_smooth
      configuration smooth acceleration).differentiable (by simp)
      |>.differentiableAt
  have remainderDerivative := remainderDifferentiableAt.hasFDerivAt
  have productDerivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt (0 : BasePoint)).smul
      remainderDerivative
  change HasFDerivAt
    (scalarQuadraticTimeCoefficient • fun point =>
      matterCoordinateEquiv
        (matterQuadraticDiracRemainder configuration acceleration point))
    (0 : BasePoint →L[ℝ] MatterCoordinateCarrier) 0
  simpa only [scalarQuadraticTimeCoefficient_origin, zero_smul, zero_add,
    add_zero, localBaseCoordinate, PiLp.zero_apply, map_zero, smul_zero,
    ContinuousLinearMap.zero_smulRight] using
      productDerivative

/-! ## The actual temporal Dirac--Yukawa first germ -/

def holonomicDiracYukawaCoordinateVector
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv
    (generatedContinuumMatterVector source 0 point
      (toContinuumPointField configuration point))

theorem matterCoordinateEquiv_real_smul
    (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    matterCoordinateEquiv (parameter • matter) =
      parameter • matterCoordinateEquiv matter := by
  exact matterCoordinateEquiv.toLinearMap.map_smul_of_tower parameter matter

/-- The action residual is read only after the actual configuration exists. -/
def matterTemporalDiracYukawaFirstGermResidual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (fieldDirectionalDerivative
      (holonomicDiracYukawaCoordinateVector source configuration)
      0 canonicalLorentzianTimeDirection)

/-- Canonical branch-free acceleration generated from the actual residual. -/
def actionGeneratedMatterTemporalFirstGermAcceleration
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    DiracExteriorMatterCarrier :=
  actionGeneratedMatterTemporalAcceleration
    (matterTemporalDiracYukawaFirstGermResidual source configuration)

/-- The same actual, updated only by its action-generated matter second jet. -/
def actionGeneratedMatterTemporalFirstGermActual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installMatterTemporalFirstGermResponse configuration
    (actionGeneratedMatterTemporalFirstGermAcceleration source configuration)

theorem holonomicDiracYukawaCoordinateVector_install_normalForm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (acceleration : DiracExteriorMatterCarrier)
    (point : BasePoint) :
    holonomicDiracYukawaCoordinateVector source
        (installMatterTemporalFirstGermResponse configuration acceleration)
        point =
      holonomicDiracYukawaCoordinateVector source configuration point +
        (point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection acceleration) +
        scalarQuadraticTimeCoefficient point •
          matterCoordinateEquiv
            (matterQuadraticDiracRemainder configuration acceleration point)) := by
  unfold holonomicDiracYukawaCoordinateVector
  rw [generatedContinuumMatterVector_installMatterTemporalFirstGermResponse
    source configuration smooth, map_add]
  rw [matterQuadraticVariationVector_normalForm source configuration
    identityCoframe acceleration point, map_add]
  rw [matterCoordinateEquiv_real_smul,
    matterCoordinateEquiv_real_smul]

theorem holonomicDiracYukawaCoordinateVector_contDiffAt_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration) :
    ContDiffAt ℝ ∞
      (holonomicDiracYukawaCoordinateVector source configuration) 0 := by
  have gammaIdentity (point : BasePoint) (direction : LorentzianIndex) :
      inverseCoframeDiracGamma
          { coframe := configuration.coframe point, derivative := 0 }
          direction =
        diracGamma direction := by
    rw [show configuration.coframe point = 1 by
      exact congrFun identityCoframe point]
    change
      inverseCoframeDiracGamma identityCoframeMatterGeometry direction =
        diracGamma direction
    exact inverseCoframeDiracGamma_identity direction
  have kineticDirectionSmooth : ∀ direction : LorentzianIndex,
      ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (holonomicMatterCovariantDerivative configuration point direction)) := by
    intro direction
    let actionLinear : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      (diracMatrixMatterCoordinateRealBilinear (diracGamma direction))
        |>.toContinuousLinearMap
    have actual := actionLinear.contDiff.comp
      (holonomicMatterCovariantDerivative_coordinate_contDiff_local
        configuration smooth direction)
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma direction)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (holonomicMatterCovariantDerivative configuration point
                direction)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have kineticSumSmooth : ContDiff ℝ ∞ fun point =>
      ∑ direction : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma direction)
            (holonomicMatterCovariantDerivative configuration point direction)) :=
    ContDiff.sum fun direction _ => kineticDirectionSmooth direction
  have iSmooth : ContDiff ℝ ∞ fun _ : BasePoint => (Complex.I : ℂ) :=
    contDiff_const
  have kineticSmooth : ContDiff ℝ ∞ fun point =>
      Complex.I •
        ∑ direction : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction (diracGamma direction)
              (holonomicMatterCovariantDerivative configuration point
                direction)) :=
    iSmooth.smul kineticSumSmooth
  have yukawaSmooth : ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (configuration.matter point)) := by
    have actual :=
      (chiralExteriorYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff.comp
        smooth.2.2.2.2.2.2.1).clm_apply smooth.2.2.2.2.2.2.2.1
    change ContDiff ℝ ∞ fun point =>
      matterCoordinateEquiv
        (chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter point)))) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have simplifiedSmooth : ContDiff ℝ ∞ fun point =>
      Complex.I •
          ∑ direction : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction (diracGamma direction)
                (holonomicMatterCovariantDerivative configuration point
                  direction)) +
        matterCoordinateEquiv
          (chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm (configuration.scalar point))
            (configuration.matter point)) :=
    kineticSmooth.add yukawaSmooth
  have vectorEquality :
      holonomicDiracYukawaCoordinateVector source configuration =
        fun point =>
          Complex.I •
              ∑ direction : LorentzianIndex,
                matterCoordinateEquiv
                  (diracMatrixMatterAction (diracGamma direction)
                    (holonomicMatterCovariantDerivative configuration point
                      direction)) +
            matterCoordinateEquiv
              (chiralExteriorYukawaAction
                (scalarCoordinateEquiv.symm (configuration.scalar point))
                (configuration.matter point)) := by
    funext point
    unfold holonomicDiracYukawaCoordinateVector
      generatedContinuumMatterVector
    simp only [toContinuumPointField,
      matterDerivativeFrameRelative_zeroChart,
      matterFrameRelative_zeroChart_local,
      scalarFrameRelativeCoordinates_zeroChart_local]
    simp_rw [gammaIdentity]
    simp only [map_add, map_smul, map_sum]
  rw [vectorEquality]
  exact simplifiedSmooth.contDiffAt

theorem matterLinearTimePrincipalCoordinate_hasFDerivAt_origin
    (acceleration : DiracExteriorMatterCarrier) :
    HasFDerivAt
      (fun point : BasePoint =>
        point canonicalLorentzianTimeDirection •
          matterCoordinateEquiv
            (identityCoframeMatterPrincipal
              canonicalLorentzianTimeDirection acceleration))
      ((localBaseCoordinate canonicalLorentzianTimeDirection).smulRight
        (matterCoordinateEquiv
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection acceleration)))
      0 := by
  exact
    (localBaseCoordinate canonicalLorentzianTimeDirection).hasFDerivAt
      |>.smul_const
        (matterCoordinateEquiv
          (identityCoframeMatterPrincipal
            canonicalLorentzianTimeDirection acceleration))

theorem holonomicDiracYukawaCoordinateVector_install_temporalFirstGerm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration)
    (acceleration : DiracExteriorMatterCarrier) :
    fieldDirectionalDerivative
        (holonomicDiracYukawaCoordinateVector source
          (installMatterTemporalFirstGermResponse configuration acceleration))
        0 canonicalLorentzianTimeDirection =
      fieldDirectionalDerivative
          (holonomicDiracYukawaCoordinateVector source configuration)
          0 canonicalLorentzianTimeDirection +
        matterCoordinateEquiv
          (identityCoframeMatterPrincipal canonicalLorentzianTimeDirection
            acceleration) := by
  have baseDifferentiable : DifferentiableAt ℝ
      (holonomicDiracYukawaCoordinateVector source configuration) 0 :=
    (holonomicDiracYukawaCoordinateVector_contDiffAt_origin source
      configuration smooth identityCoframe).differentiableAt (by simp)
  have linearDerivative :=
    matterLinearTimePrincipalCoordinate_hasFDerivAt_origin acceleration
  have quadraticDerivative :=
    matterQuadraticWeightedRemainder_hasFDerivAt_origin_zero
      configuration smooth acceleration
  rw [show
    holonomicDiracYukawaCoordinateVector source
        (installMatterTemporalFirstGermResponse configuration acceleration) =
      holonomicDiracYukawaCoordinateVector source configuration +
        ((fun point : BasePoint =>
          point canonicalLorentzianTimeDirection •
            matterCoordinateEquiv
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection acceleration)) +
        fun point =>
          scalarQuadraticTimeCoefficient point •
            matterCoordinateEquiv
              (matterQuadraticDiracRemainder configuration acceleration point)) by
    funext point
    exact holonomicDiracYukawaCoordinateVector_install_normalForm
      source configuration smooth identityCoframe acceleration point]
  unfold fieldDirectionalDerivative
  rw [(baseDifferentiable.hasFDerivAt.add
    (linearDerivative.add quadraticDerivative)).fderiv]
  simp only [add_apply, add_zero]
  change
    (fderiv ℝ (holonomicDiracYukawaCoordinateVector source configuration) 0)
          (coordinateDirection canonicalLorentzianTimeDirection) +
        (localBaseCoordinate canonicalLorentzianTimeDirection)
          (coordinateDirection canonicalLorentzianTimeDirection) •
            matterCoordinateEquiv
              (identityCoframeMatterPrincipal
                canonicalLorentzianTimeDirection acceleration) = _
  simp [localBaseCoordinate, coordinateDirection,
    canonicalLorentzianTimeDirection]

theorem actionGeneratedMatterTemporalFirstGermAcceleration_eq_zero_iff
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    actionGeneratedMatterTemporalFirstGermAcceleration source configuration = 0 ↔
      matterTemporalDiracYukawaFirstGermResidual source configuration = 0 :=
  actionGeneratedMatterTemporalAcceleration_eq_zero_iff _

theorem actionGeneratedMatterTemporalFirstGermActual_zeroFiber
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (residualZero :
      matterTemporalDiracYukawaFirstGermResidual source configuration = 0) :
    actionGeneratedMatterTemporalFirstGermActual source configuration =
      configuration := by
  unfold actionGeneratedMatterTemporalFirstGermActual
  rw [(actionGeneratedMatterTemporalFirstGermAcceleration_eq_zero_iff
    source configuration).2 residualZero]
  exact installMatterTemporalFirstGermResponse_zero configuration

/-- Producer-soundness: the canonical action update kills the actual temporal
Dirac--Yukawa first germ.  This substitution is not counted as an independent
field equation. -/
theorem actionGeneratedMatterTemporalFirstGermActual_producerSound
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (identityCoframe : HasIdentityCoframe configuration) :
    matterTemporalDiracYukawaFirstGermResidual source
        (actionGeneratedMatterTemporalFirstGermActual source configuration) =
      0 := by
  have response :=
    holonomicDiracYukawaCoordinateVector_install_temporalFirstGerm
      source configuration smooth identityCoframe
        (actionGeneratedMatterTemporalFirstGermAcceleration source configuration)
  have actionLaw :=
    actionGeneratedMatterTemporalAcceleration_producerSound
      (matterTemporalDiracYukawaFirstGermResidual source configuration)
  have coordinateActionLaw := congrArg matterCoordinateEquiv actionLaw
  simp only [map_add, map_zero] at coordinateActionLaw
  have residualCoordinate :
      matterCoordinateEquiv
          (matterTemporalDiracYukawaFirstGermResidual source configuration) =
        fieldDirectionalDerivative
          (holonomicDiracYukawaCoordinateVector source configuration)
          0 canonicalLorentzianTimeDirection := by
    simp [matterTemporalDiracYukawaFirstGermResidual]
  rw [residualCoordinate] at coordinateActionLaw
  unfold actionGeneratedMatterTemporalFirstGermActual
    matterTemporalDiracYukawaFirstGermResidual
  rw [response]
  rw [show
    actionGeneratedMatterTemporalFirstGermAcceleration source configuration =
      actionGeneratedMatterTemporalAcceleration
        (matterTemporalDiracYukawaFirstGermResidual source configuration) by
    rfl]
  rw [coordinateActionLaw]
  simp

theorem actionGeneratedMatterTemporalFirstGermActual_smooth
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (actionGeneratedMatterTemporalFirstGermActual source configuration).Smooth :=
  installMatterTemporalFirstGermResponse_smooth configuration smooth _

theorem actionGeneratedMatterTemporalFirstGermActual_nondegenerate
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate) :
    (actionGeneratedMatterTemporalFirstGermActual source configuration).Nondegenerate :=
  installMatterTemporalFirstGermResponse_nondegenerate configuration
    nondegenerate _

@[simp] theorem actionGeneratedMatterTemporalFirstGermActual_matter_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (actionGeneratedMatterTemporalFirstGermActual source configuration).matter 0 =
      configuration.matter 0 :=
  installMatterTemporalFirstGermResponse_matter_origin configuration _

theorem actionGeneratedMatterTemporalFirstGermActual_matter_firstJet_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv
          ((actionGeneratedMatterTemporalFirstGermActual source configuration).matter
            point))
        0 direction =
      fieldDirectionalDerivative
        (fun point => matterCoordinateEquiv (configuration.matter point))
        0 direction :=
  installMatterTemporalFirstGermResponse_matter_firstJet_origin
    configuration smooth _ direction

theorem actionGeneratedMatterTemporalFirstGermActual_diracYukawa_origin
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (actionGeneratedMatterTemporalFirstGermActual source configuration)
          0) =
      generatedContinuumMatterVector source 0 0
        (toContinuumPointField configuration 0) :=
  generatedContinuumMatterVector_installMatterTemporalFirstGermResponse_origin
    source configuration smooth _

theorem actionGeneratedMatterTemporalFirstGermActual_diracYukawa_origin_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (baseZero :
      generatedContinuumMatterVector source 0 0
          (toContinuumPointField configuration 0) =
        0) :
    generatedContinuumMatterVector source 0 0
        (toContinuumPointField
          (actionGeneratedMatterTemporalFirstGermActual source configuration)
          0) =
      0 := by
  rw [actionGeneratedMatterTemporalFirstGermActual_diracYukawa_origin
    source configuration smooth, baseZero]

end

end
  SaturationMonoid.PhysicsCore.StageNineMatterActionTemporalFirstGermResponse

import H0mework.Physics.Geometry.GravityAlgebraicKeepEndpoint
import H0mework.Physics.Source.PositiveNativeAlgebraicEliminationLiftDefect
import H0mework.Physics.GravitySource.ConnectionLiftNoGo
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# S9-C3h70b: actual origin germ for the gravity algebraic keep response

C3h70a uniquely forces the next auxiliary/curvature pair at fixed coframe.
This module turns its internally derived curvature endpoint into a primitive
connection-field germ: the normalized-affine grammar preserves the input
origin connection value, and its actual `dω + ω∧ω` curvature realizes the
forced target at the canonical-chart origin.  The auxiliary field is updated
pointwise by the same forced formula.  The update has no target argument,
free coefficient, branch, source slot, shell witness, or stationarity receipt.
Generic Lorentz-skewness requires the input origin value to be Lorentz-skew;
the positive source-native specialization discharges that condition.

For the C3h69 source-native algebraic image, both auxiliary residuals are
already zero.  The new update therefore transports all three algebraic
coordinates at the origin, changes the gravity-simplicity raw coordinate from
`5/4` to `5/8`, generates actual curvature coordinate `-3/8`, and makes the
algebraic layer of the full joint lift defect exactly zero.  It also proves
the full bivector bridge from the simplicity residual to the actual gravity
mouth residual; no coordinate-only identification is used.

This is a fixed-coframe, canonical-chart/origin existing-field response germ.
It is not a full residual-section lift: the six Euler--Lagrange channels,
away-from-origin constraint propagation, smoothness of the forced auxiliary,
Spin/frame naturality, patch descent, global boundary conditions, finite
action, matter torsion/backreaction, and joint stationarity remain open.
Preserving the multiplier is reader jurisdiction, not a claim that the
triangular auxiliary residual is the complete off-simplicity variation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseGerm

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepEndpoint
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineJointStateLiftDefect
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNinePositiveSourceGravityMouthConnectionLiftNoGo
open StageNinePositiveSourceGravityMouthObstruction
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNinePositiveSourceGravityMouthTransportCurvature
open StageNinePositiveSourceNativeAlgebraicEliminationLiftDefect
open StageNinePositiveSourceNativeAlgebraicEliminationUpdate
open StageNinePositiveSourceNativeGravityCurvatureBridge

noncomputable section

set_option autoImplicit false

/-- Pointwise auxiliary response forced by the same source-generated keep. -/
def gravityAlgebraicKeepResponseAuxiliaryField
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    BasePoint → PhysicalBivector :=
  fun point => forcedGravityAuxiliaryKeepEndpoint source.legacy.sigma
    (configuration.coframe point) (configuration.gravityAuxiliary point)

/-- Origin curvature target derived internally from the input's actual
coframe, curvature, auxiliary and source sigma. -/
def gravityAlgebraicKeepResponseCurvatureTarget
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : PhysicalBivector :=
  forcedGravityCurvatureKeepEndpoint source.legacy.sigma
    (configuration.coframe 0)
    (holonomicGravityCurvature configuration 0)
    (configuration.gravityAuxiliary 0)

/-- Existing-field response: update only the primitive Lorentz connection and
gravity auxiliary.  The normalized-affine target is internal, not an input. -/
def gravityAlgebraicKeepResponseUpdate
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityConnection := normalizedAffineLorentzConnectionField
      (configuration.gravityConnection 0)
      (gravityAlgebraicKeepResponseCurvatureTarget source configuration)
    gravityAuxiliary :=
      gravityAlgebraicKeepResponseAuxiliaryField source configuration }

abbrev gravityAlgebraicKeepResponseStateUpdate
    (source : CurrentSmoothUnifiedSource) : CurrentJointShellStateUpdate :=
  gravityAlgebraicKeepResponseUpdate source

@[simp] theorem gravityAlgebraicKeepResponseUpdate_coframe
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (gravityAlgebraicKeepResponseUpdate source configuration).coframe =
      configuration.coframe :=
  rfl

/-- The response does not erase multiplier, P286, scalar, matter, or dual
responsibility. -/
theorem gravityAlgebraicKeepResponseUpdate_preserves_otherFields
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (gravityAlgebraicKeepResponseUpdate source
        configuration).gravitySimplicityMultiplier =
          configuration.gravitySimplicityMultiplier ∧
      (gravityAlgebraicKeepResponseUpdate source
        configuration).gaugeConnection = configuration.gaugeConnection ∧
      (gravityAlgebraicKeepResponseUpdate source
        configuration).gaugeAuxiliary = configuration.gaugeAuxiliary ∧
      (gravityAlgebraicKeepResponseUpdate source
        configuration).scalar = configuration.scalar ∧
      (gravityAlgebraicKeepResponseUpdate source
        configuration).matter = configuration.matter ∧
      (gravityAlgebraicKeepResponseUpdate source
        configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The local response installs the normalized-affine first jet while
preserving the input connection's origin value. -/
@[simp] theorem gravityAlgebraicKeepResponseUpdate_gravityConnection_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (gravityAlgebraicKeepResponseUpdate source
      configuration).gravityConnection 0 =
        configuration.gravityConnection 0 :=
  normalizedAffineLorentzConnectionField_zero _ _

theorem gravityAlgebraicKeepResponseUpdate_lorentzSkew
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (originSkew : LorentzSkew (configuration.gravityConnection 0))
    (point : BasePoint) :
    LorentzSkew
      ((gravityAlgebraicKeepResponseUpdate source
        configuration).gravityConnection point) := by
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _ originSkew point

theorem gravityAlgebraicKeepResponseUpdate_nondegenerate_iff
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (gravityAlgebraicKeepResponseUpdate source configuration).Nondegenerate ↔
      configuration.Nondegenerate :=
  Iff.rfl

/-- The primitive connection's actual origin curvature realizes the internally
forced target. -/
theorem gravityAlgebraicKeepResponseUpdate_curvature_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (gravityAlgebraicKeepResponseUpdate source configuration) 0 =
      gravityAlgebraicKeepResponseCurvatureTarget source configuration := by
  change holonomicGravityCurvature
      (normalizedAffineConfiguration (configuration.gravityConnection 0)
        (gravityAlgebraicKeepResponseCurvatureTarget source configuration)) 0 =
    gravityAlgebraicKeepResponseCurvatureTarget source configuration
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-- The actual simplicity residual at the origin obeys the source keep. -/
theorem gravityAlgebraicKeepResponseUpdate_simplicityResidual_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual source
      (gravityAlgebraicKeepResponseUpdate source configuration)
      0).gravitySimplicity =
        (1 - source.legacy.sigma) •
          (currentPointwiseAlgebraicResidual source configuration
            0).gravitySimplicity := by
  change
    forcedGravityAuxiliaryKeepEndpoint source.legacy.sigma
          (configuration.coframe 0) (configuration.gravityAuxiliary 0) -
        physicalIIPlusBivector (configuration.coframe 0) =
      (1 - source.legacy.sigma) •
        (configuration.gravityAuxiliary 0 -
          physicalIIPlusBivector (configuration.coframe 0))
  exact forcedGravityAuxiliaryKeepEndpoint_residual _ _ _

/-- The actual triangular gravity-auxiliary residual at the origin obeys the
same source keep. -/
theorem gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual source
      (gravityAlgebraicKeepResponseUpdate source configuration)
      0).gravityAuxiliary =
        (1 - source.legacy.sigma) •
          (currentPointwiseAlgebraicResidual source configuration
            0).gravityAuxiliary := by
  change
    holonomicGravityCurvature
        (gravityAlgebraicKeepResponseUpdate source configuration) 0 -
        gravityInternalDualEquiv
          (forcedGravityAuxiliaryKeepEndpoint source.legacy.sigma
            (configuration.coframe 0)
            (configuration.gravityAuxiliary 0)) =
      (1 - source.legacy.sigma) •
        (holonomicGravityCurvature configuration 0 -
          gravityInternalDualEquiv (configuration.gravityAuxiliary 0))
  rw [gravityAlgebraicKeepResponseUpdate_curvature_origin]
  exact forcedGravityCurvatureKeepEndpoint_residual _ _ _ _

/-- P286 fields and coframe are unchanged, so its algebraic residual is read
back unchanged.  It transports only on an input zero fiber. -/
theorem gravityAlgebraicKeepResponseUpdate_p286Residual_origin
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual source
      (gravityAlgebraicKeepResponseUpdate source configuration)
      0).p286GaugeAuxiliary =
        (currentPointwiseAlgebraicResidual source configuration
          0).p286GaugeAuxiliary := by
  rfl

/-- On the gravity-auxiliary equation, the internal dual of the simplicity
residual is exactly the actual curvature-mouth residual. -/
theorem gravitySimplicityDual_eq_actualMouthResidual_of_auxiliaryEquation
    (source : CurrentSmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (auxiliaryEquation : holonomicGravityCurvature configuration point =
      gravityInternalDualEquiv (configuration.gravityAuxiliary point)) :
    gravityInternalDualEquiv
        ((currentPointwiseAlgebraicResidual source configuration
          point).gravitySimplicity) =
      stageNineGravityMouthResidualAt configuration point := by
  change
    gravityInternalDualEquiv
        (configuration.gravityAuxiliary point -
          physicalIIPlusBivector (configuration.coframe point)) =
      holonomicGravityCurvature configuration point -
        gravityInternalDualEquiv
          (physicalIIPlusBivector (configuration.coframe point))
  rw [map_sub, auxiliaryEquation]

/-! ## Positive source-native fixed-image specialization -/

def positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate :
    CurrentJointShellStateUpdate :=
  gravityAlgebraicKeepResponseUpdate positiveSmoothUnifiedSource

theorem positiveSourceNativeGravityAlgebraicKeepResponse_simplicityResidual_origin
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
      0).gravitySimplicity =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).gravitySimplicity :=
  gravityAlgebraicKeepResponseUpdate_simplicityResidual_origin _ _

theorem positiveSourceNativeGravityAlgebraicKeepResponse_auxiliaryResidual_origin
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
      0).gravityAuxiliary =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).gravityAuxiliary :=
  gravityAlgebraicKeepResponseUpdate_auxiliaryResidual_origin _ _

theorem positiveSourceNativeGravityAlgebraicKeepResponse_p286Residual_origin
    (configuration : StageNineHolonomicConfiguration) :
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
      0).p286GaugeAuxiliary =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).p286GaugeAuxiliary := by
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).p286GaugeAuxiliary =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).p286GaugeAuxiliary
  have inputZero :=
    (positiveSourceNativeAlgebraicEliminationUpdate_solvedAlgebraicResiduals
      configuration 0).2
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).p286GaugeAuxiliary = 0 at inputZero
  rw [inputZero, smul_zero]

/-- Full-bivector bridge at the C3h69 input image; this does not assert Spin
equivariance of the internal dual. -/
theorem positiveSourceNativeAlgebraicImage_simplicityDual_eq_actualMouthResidual
    (configuration : StageNineHolonomicConfiguration) :
    gravityInternalDualEquiv
        ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
          0).gravitySimplicity) =
      stageNineGravityMouthResidualAt
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration) 0 := by
  apply gravitySimplicityDual_eq_actualMouthResidual_of_auxiliaryEquation
  exact positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
    configuration 0

theorem positiveSourceNativeGravityAlgebraicKeepResponse_simplicityDual_eq_actualMouthResidual
    (configuration : StageNineHolonomicConfiguration) :
    gravityInternalDualEquiv
        ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
          (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
          0).gravitySimplicity) =
      stageNineGravityMouthResidualAt
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0 := by
  apply gravitySimplicityDual_eq_actualMouthResidual_of_auxiliaryEquation
  have transported :=
    positiveSourceNativeGravityAlgebraicKeepResponse_auxiliaryResidual_origin
      configuration
  have inputZero :=
    (positiveSourceNativeAlgebraicEliminationUpdate_solvedAlgebraicResiduals
      configuration 0).1
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).gravityAuxiliary = 0 at inputZero
  rw [inputZero, smul_zero] at transported
  change
    holonomicGravityCurvature
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0 -
      gravityInternalDualEquiv
        ((positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate
            configuration)).gravityAuxiliary 0) = 0 at transported
  exact sub_eq_zero.mp transported

/-- The actual mouth residual transports because both endpoints remain on the
gravity-auxiliary zero fiber.  This is not yet a Spin-covariance theorem. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_actualMouthResidual_origin
    (configuration : StageNineHolonomicConfiguration) :
    stageNineGravityMouthResidualAt
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0 =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        stageNineGravityMouthResidualAt
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
          0 := by
  rw [←
    positiveSourceNativeGravityAlgebraicKeepResponse_simplicityDual_eq_actualMouthResidual,
    ← positiveSourceNativeAlgebraicImage_simplicityDual_eq_actualMouthResidual,
    positiveSourceNativeGravityAlgebraicKeepResponse_simplicityResidual_origin,
    map_smul]

/-- Concrete kept responsibility on the existing raw carrier. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_residual_three_zero
    (configuration : StageNineHolonomicConfiguration) :
    ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
      0).gravitySimplicity) 3 0 = (5 / 8 : ℝ) := by
  have transported := congrFun (congrFun
    (positiveSourceNativeGravityAlgebraicKeepResponse_simplicityResidual_origin
      configuration) 3) 0
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half] at transported
  have inputValue :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravitySimplicity_three_zero
      configuration
  change
    ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).gravitySimplicity) 3 0 = (5 / 4 : ℝ) at inputValue
  change
    ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
      0).gravitySimplicity) 3 0 =
        (1 - (1 / 2 : ℝ)) *
          ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).gravitySimplicity) 3 0 at transported
  rw [inputValue] at transported
  norm_num at transported ⊢
  exact transported

/-- Positive regression: the residual-forced response is not the unchanged
C3h69 fixed image. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_changes_fixedImage
    (configuration : StageNineHolonomicConfiguration) :
    positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate configuration) ≠
      positiveSourceNativeAlgebraicEliminationStateUpdate configuration := by
  intro unchanged
  have residualUnchanged := congrArg
    (fun candidate : StageNineHolonomicConfiguration =>
      ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        candidate 0).gravitySimplicity) 3 0) unchanged
  have inputValue :=
    positiveSourceNativeAlgebraicEliminationUpdate_gravitySimplicity_three_zero
      configuration
  change
    ((currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).gravitySimplicity) 3 0 = (5 / 4 : ℝ) at inputValue
  rw [positiveSourceNativeGravityAlgebraicKeepResponse_residual_three_zero,
    inputValue] at residualUnchanged
  norm_num at residualUnchanged

/-- The generated connection remains Lorentz-skew because the internally
preserved source-native origin value is Lorentz-skew. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_lorentzSkew
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    LorentzSkew
      ((positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
        (positiveSourceNativeAlgebraicEliminationStateUpdate
          configuration)).gravityConnection point) := by
  apply gravityAlgebraicKeepResponseUpdate_lorentzSkew
  change LorentzSkew (generatedLorentzConnectionAt positiveSmoothUnifiedSource 0)
  exact positive_generatedLorentzConnection_lorentzSkew 0

/-- The response preserves the source-native coframe and hence its proved
nondegeneracy; this is an admissibility readout, not stationarity. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_nondegenerate
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (positiveSourceNativeAlgebraicEliminationStateUpdate
        configuration)).Nondegenerate := by
  change
    (gravityAlgebraicKeepResponseUpdate positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationStateUpdate
        configuration)).Nondegenerate
  exact
    (gravityAlgebraicKeepResponseUpdate_nondegenerate_iff _ _).mpr
      (positiveSourceNativeAlgebraicEliminationUpdate_nondegenerate
        configuration)

/-- The response really changes the connection jet: its actual curvature at
the obstruction coordinate is `-3/8`, rather than C3h68's `1/4`. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_curvature_zero_zero
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0 0 0 = (-3 / 8 : ℝ) := by
  let initial :=
    positiveSourceNativeAlgebraicEliminationStateUpdate configuration
  let response :=
    positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate initial
  have auxiliaryTransport :=
    positiveSourceNativeGravityAlgebraicKeepResponse_auxiliaryResidual_origin
      configuration
  have initialAuxiliaryZero :=
    (positiveSourceNativeAlgebraicEliminationUpdate_solvedAlgebraicResiduals
      configuration 0).1
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      response 0).gravityAuxiliary =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            initial 0).gravityAuxiliary at auxiliaryTransport
  change
    (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
      initial 0).gravityAuxiliary = 0 at initialAuxiliaryZero
  rw [initialAuxiliaryZero, smul_zero] at auxiliaryTransport
  change
    holonomicGravityCurvature response 0 -
      gravityInternalDualEquiv (response.gravityAuxiliary 0) = 0
      at auxiliaryTransport
  have curvatureAuxiliary :
      holonomicGravityCurvature response 0 =
        gravityInternalDualEquiv (response.gravityAuxiliary 0) :=
    sub_eq_zero.mp auxiliaryTransport
  have simplicityCoordinate :=
    positiveSourceNativeGravityAlgebraicKeepResponse_residual_three_zero
      configuration
  change
    response.gravityAuxiliary 0 3 0 -
      physicalIIPlusBivector
        (positiveSmoothUnifiedSource.legacy.coframeAt 0) 3 0 =
          (5 / 8 : ℝ) at simplicityCoordinate
  have constitutiveCoordinate :
      gravityInternalDualEquiv
          (physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0)) 0 0 =
        (-1 : ℝ) := by
    have mouth := positiveSourceGravityMouthObstruction_zero_zero
    have sourceCurvature := positiveSourceLegacyCurvature_zero_zero
    change
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 -
        gravityInternalDualEquiv
          (physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0)) 0 0 =
        (5 / 4 : ℝ) at mouth
    rw [sourceCurvature] at mouth
    linarith
  have auxiliaryCoordinate : response.gravityAuxiliary 0 3 0 =
      (-3 / 8 : ℝ) := by
    have iiPlusCoordinate :
        physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0) 3 0 =
          (-1 : ℝ) := by
      exact constitutiveCoordinate
    rw [iiPlusCoordinate] at simplicityCoordinate
    linarith
  have curvatureCoordinate := congrFun (congrFun curvatureAuxiliary 0) 0
  change
    holonomicGravityCurvature response 0 0 0 =
      response.gravityAuxiliary 0 3 0 at curvatureCoordinate
  rw [auxiliaryCoordinate] at curvatureCoordinate
  exact curvatureCoordinate

/-- At the proved obstruction coordinate, the actual dynamic response agrees
with the existing C3g7a required-curvature authority.  This does not assert a
full-bivector equality. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_curvature_zero_zero_eq_required
    (configuration : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0 0 0 = positiveSourceGravityMouthRequiredCurvature 0 0 := by
  rw [positiveSourceNativeGravityAlgebraicKeepResponse_curvature_zero_zero,
    positiveSourceGravityMouthRequiredCurvature_zero_zero]

/-- The source-native response realizes the keep on all three algebraic
coordinates of the actual full joint defect at the origin. -/
theorem positiveSourceNativeGravityAlgebraicKeepResponse_liftDefect_algebraic_origin
    (configuration : StageNineHolonomicConfiguration) :
    (currentJointShellStateLiftDefect positiveSmoothUnifiedSource
      positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
      (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
      0).algebraic = 0 := by
  apply CurrentPointwiseAlgebraicResidualCarrier.ext
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0).gravitySimplicity -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).gravitySimplicity = 0
    rw [
      positiveSourceNativeGravityAlgebraicKeepResponse_simplicityResidual_origin]
    exact sub_self _
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0).gravityAuxiliary -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).gravityAuxiliary = 0
    rw [
      positiveSourceNativeGravityAlgebraicKeepResponse_auxiliaryResidual_origin]
    exact sub_self _
  · change
      (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
        (positiveSourceNativeGravityAlgebraicKeepResponseStateUpdate
          (positiveSourceNativeAlgebraicEliminationStateUpdate configuration))
        0).p286GaugeAuxiliary -
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          (currentPointwiseAlgebraicResidual positiveSmoothUnifiedSource
            (positiveSourceNativeAlgebraicEliminationStateUpdate configuration)
            0).p286GaugeAuxiliary = 0
    rw [positiveSourceNativeGravityAlgebraicKeepResponse_p286Residual_origin]
    exact sub_self _

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseGerm

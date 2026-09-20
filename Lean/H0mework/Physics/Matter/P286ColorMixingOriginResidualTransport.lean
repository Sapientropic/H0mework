import H0mework.Physics.GaugeAction.ResidualLimitP286BFBalanceDecision
import H0mework.Physics.Lorentz.ResidualLimitLorentzClassObstruction

/-!
# S9-C3h41: P286 color-mixing origin residual transport

This module constructs the one-dimensional origin class through
the actual source P286 connection.  The class coordinate `t` is a transported
state coordinate, not a primitive-source knob: the target curvature stays the
actual positive-source target, and the antisymmetric affine first jet is
uniquely generated as `target - [A,A]` with the forced `1/2` normalization.

No curvature, balance, zero-fiber, branch, shell, or stationarity receipt is
accepted by the constructor.  The resulting theorem is deliberately
class-scoped: it closes the actual P286 Euler--Lagrange response channel and
its no-naked-sink responsibility, but does not claim joint stationarity.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorMixingOriginResidualTransport

open ProofFreeRicherAnholonomicSource
open EmpiricalReferenceScaleCouplingBoundary
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineConnectionSectorSourceBalance
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286Bianchi
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionPointwiseEquation
open StageNineP286GaugeConnectionVariation
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286BFBalanceDecision
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineSourceGeneratedPartialPrimitiveCarrier
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open SU7ExteriorYukawaMassSpectrum
open AffineRelaxation
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Fixed target and one-dimensional origin class -/

/-- The class coordinate changes only the color-mixing origin component. -/
def colorMixingOriginPotential (t : ℝ) :
    LorentzianIndex → P286LieBlockData
  | 0 => (1 / 2 : ℝ) • colorCartanP286ConnectionDirection
  | 1 => t • colorMixingP286ConnectionDirection
  | _ => 0

/-- The target is the actual positive-source target, independent of `t`. -/
abbrev colorMixingOriginTargetCurvature : Fin 6 → P286LieBlockData :=
  sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy

/-- The exterior derivative is forced by the target and the live bracket. -/
def colorMixingOriginExteriorDerivative
    (t : ℝ) (pair : Fin 6) : P286LieBlockData :=
  colorMixingOriginTargetCurvature pair -
    p286LieBracket
      (colorMixingOriginPotential t (pairFirst pair))
      (colorMixingOriginPotential t (pairSecond pair))

/-- Antisymmetric extension of the six forced exterior-derivative values. -/
def colorMixingOriginExteriorDerivativeComponent
    (t : ℝ) (first second : LorentzianIndex) : P286LieBlockData :=
  if first = 0 ∧ second = 1 then colorMixingOriginExteriorDerivative t 0
  else if first = 1 ∧ second = 0 then
    -colorMixingOriginExteriorDerivative t 0
  else if first = 0 ∧ second = 2 then
    colorMixingOriginExteriorDerivative t 1
  else if first = 2 ∧ second = 0 then
    -colorMixingOriginExteriorDerivative t 1
  else if first = 0 ∧ second = 3 then
    colorMixingOriginExteriorDerivative t 2
  else if first = 3 ∧ second = 0 then
    -colorMixingOriginExteriorDerivative t 2
  else if first = 2 ∧ second = 3 then
    colorMixingOriginExteriorDerivative t 3
  else if first = 3 ∧ second = 2 then
    -colorMixingOriginExteriorDerivative t 3
  else if first = 3 ∧ second = 1 then
    colorMixingOriginExteriorDerivative t 4
  else if first = 1 ∧ second = 3 then
    -colorMixingOriginExteriorDerivative t 4
  else if first = 1 ∧ second = 2 then
    colorMixingOriginExteriorDerivative t 5
  else if first = 2 ∧ second = 1 then
    -colorMixingOriginExteriorDerivative t 5
  else 0

theorem colorMixingOriginExteriorDerivativeComponent_antisymm
    (t : ℝ) (first second : LorentzianIndex) :
    colorMixingOriginExteriorDerivativeComponent t first second =
      -colorMixingOriginExteriorDerivativeComponent t second first := by
  fin_cases first <;> fin_cases second <;>
    simp [colorMixingOriginExteriorDerivativeComponent]

@[simp] theorem colorMixingOriginExteriorDerivativeComponent_pair
    (t : ℝ) (pair : Fin 6) :
    colorMixingOriginExteriorDerivativeComponent t
        (pairFirst pair) (pairSecond pair) =
      colorMixingOriginExteriorDerivative t pair := by
  fin_cases pair <;>
    simp [colorMixingOriginExteriorDerivativeComponent, pairFirst, pairSecond]

/-! ## Forced normalized affine first jet -/

def colorMixingOriginAffineIncrementLinear
    (t : ℝ) (formDirection : LorentzianIndex) :
    BasePoint →L[ℝ] P286CoordinateCarrier :=
  (1 / 2 : ℝ) •
    ∑ derivativeDirection : LorentzianIndex,
      (p286BaseCoordinate derivativeDirection).smulRight
        (p286CoordinateEquiv
          (colorMixingOriginExteriorDerivativeComponent t
            derivativeDirection formDirection))

def colorMixingOriginAffineConnectionCoordinate
    (t : ℝ) (point : BasePoint)
    (formDirection : LorentzianIndex) : P286CoordinateCarrier :=
  p286CoordinateEquiv (colorMixingOriginPotential t formDirection) +
    colorMixingOriginAffineIncrementLinear t formDirection point

def colorMixingOriginAffineConnectionField
    (t : ℝ) : P286ConnectionField :=
  fun point formDirection =>
    p286CoordinateEquiv.symm
      (colorMixingOriginAffineConnectionCoordinate t point formDirection)

@[simp] theorem colorMixingOriginAffineIncrementLinear_zero
    (t : ℝ) (formDirection : LorentzianIndex) :
    colorMixingOriginAffineIncrementLinear t formDirection 0 = 0 :=
  map_zero _

@[simp] theorem colorMixingOriginAffineConnectionField_origin
    (t : ℝ) (formDirection : LorentzianIndex) :
    colorMixingOriginAffineConnectionField t 0 formDirection =
      colorMixingOriginPotential t formDirection := by
  simp [colorMixingOriginAffineConnectionField,
    colorMixingOriginAffineConnectionCoordinate]

theorem colorMixingOriginAffineConnectionField_smooth
    (t : ℝ) (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286CoordinateEquiv
        (colorMixingOriginAffineConnectionField t point formDirection) := by
  simpa [colorMixingOriginAffineConnectionField,
    colorMixingOriginAffineConnectionCoordinate] using
      (contDiff_const.add
        (colorMixingOriginAffineIncrementLinear t formDirection).contDiff)

theorem colorMixingOriginAffineConnectionCoordinate_directionalDerivative_origin
    (t : ℝ)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          colorMixingOriginAffineConnectionCoordinate t point formDirection)
        0 derivativeDirection =
      (1 / 2 : ℝ) •
        p286CoordinateEquiv
          (colorMixingOriginExteriorDerivativeComponent t
            derivativeDirection formDirection) := by
  unfold fieldDirectionalDerivative colorMixingOriginAffineConnectionCoordinate
  let increment := colorMixingOriginAffineIncrementLinear t formDirection
  rw [fderiv_const_add]
  rw [increment.hasFDerivAt.fderiv]
  change
    colorMixingOriginAffineIncrementLinear t formDirection
        (coordinateDirection derivativeDirection) = _
  simp only [colorMixingOriginAffineIncrementLinear]
  fin_cases derivativeDirection <;> fin_cases formDirection <;>
    simp [coordinateDirection, Fin.sum_univ_four]

theorem colorMixingOriginAffineConnectionCoordinate_antisymmetrizedDerivative_pair
    (t : ℝ) (pair : Fin 6) :
    fieldDirectionalDerivative
        (fun point =>
          colorMixingOriginAffineConnectionCoordinate t point
            (pairSecond pair))
        0 (pairFirst pair) -
      fieldDirectionalDerivative
        (fun point =>
          colorMixingOriginAffineConnectionCoordinate t point
            (pairFirst pair))
        0 (pairSecond pair) =
      p286CoordinateEquiv (colorMixingOriginExteriorDerivative t pair) := by
  rw [colorMixingOriginAffineConnectionCoordinate_directionalDerivative_origin,
    colorMixingOriginAffineConnectionCoordinate_directionalDerivative_origin,
    colorMixingOriginExteriorDerivativeComponent_antisymm t
      (pairSecond pair) (pairFirst pair),
    colorMixingOriginExteriorDerivativeComponent_pair]
  simp only [map_neg]
  module

/-! ## Actual field installer, curvature, smoothness, and Bianchi -/

def installColorMixingOriginAffineConnection
    (t : ℝ) (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with gaugeConnection :=
      colorMixingOriginAffineConnectionField t }

theorem installColorMixingOriginAffineConnection_smooth
    (t : ℝ) (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (installColorMixingOriginAffineConnection t configuration).Smooth := by
  rcases smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, _oldGaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩
  exact ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
    gravityMultiplierSmooth, colorMixingOriginAffineConnectionField_smooth t,
    gaugeAuxiliarySmooth, scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

theorem installColorMixingOriginAffineConnection_connectionDerivative_antisymm
    (t : ℝ) (configuration : StageNineHolonomicConfiguration)
    (pair : Fin 6) :
    p286ConnectionDerivative
        (installColorMixingOriginAffineConnection t configuration) 0
        (pairFirst pair) (pairSecond pair) -
      p286ConnectionDerivative
        (installColorMixingOriginAffineConnection t configuration) 0
        (pairSecond pair) (pairFirst pair) =
      colorMixingOriginExteriorDerivative t pair := by
  apply p286CoordinateEquiv.injective
  simp only [map_sub, p286ConnectionDerivative,
    p286CoordinateEquiv.apply_symm_apply]
  simp only [installColorMixingOriginAffineConnection,
    colorMixingOriginAffineConnectionField,
    p286CoordinateEquiv.apply_symm_apply]
  exact
    colorMixingOriginAffineConnectionCoordinate_antisymmetrizedDerivative_pair
      t pair

theorem holonomicGaugeCurvature_installColorMixingOrigin_origin
    (t : ℝ) (configuration : StageNineHolonomicConfiguration) :
    holonomicGaugeCurvature
        (installColorMixingOriginAffineConnection t configuration) 0 =
      colorMixingOriginTargetCurvature := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [installColorMixingOriginAffineConnection_connectionDerivative_antisymm]
  change
    colorMixingOriginExteriorDerivative t pair +
        p286LieBracket
          (colorMixingOriginAffineConnectionField t 0 (pairFirst pair))
          (colorMixingOriginAffineConnectionField t 0 (pairSecond pair)) =
      colorMixingOriginTargetCurvature pair
  rw [colorMixingOriginAffineConnectionField_origin,
    colorMixingOriginAffineConnectionField_origin]
  simp [colorMixingOriginExteriorDerivative]

theorem installColorMixingOriginAffineConnection_offShellBianchi
    (t : ℝ) (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative
          (installColorMixingOriginAffineConnection t configuration)
          point first second third +
        covariantCurvatureDerivative
          (installColorMixingOriginAffineConnection t configuration)
          point second third first +
        covariantCurvatureDerivative
          (installColorMixingOriginAffineConnection t configuration)
          point third first second = 0 := by
  exact holonomicP286GaugeCurvature_bianchi
    (installColorMixingOriginAffineConnection t configuration)
    (installColorMixingOriginAffineConnection_smooth t configuration smooth)
    point first second third

/-! ## The actual source lies in the class at `t = 1/2` -/

theorem colorMixingOriginPotential_source
    (direction : LorentzianIndex) :
    colorMixingOriginPotential (1 / 2 : ℝ) direction =
      sourceP286Potential positiveSmoothUnifiedSource.legacy direction := by
  fin_cases direction <;>
    simp [colorMixingOriginPotential, sourceP286Potential,
      colorCartanP286ConnectionDirection,
      colorMixingP286ConnectionDirection,
      positiveSmoothUnifiedSource_legacy_sigma_eq_half,
      realScaleP286_eq_smul]

theorem colorMixingOriginExteriorDerivative_source
    (pair : Fin 6) :
    colorMixingOriginExteriorDerivative (1 / 2 : ℝ) pair =
      sourceP286ExteriorDerivative positiveSmoothUnifiedSource.legacy pair := by
  unfold colorMixingOriginExteriorDerivative sourceP286ExteriorDerivative
  rw [colorMixingOriginPotential_source,
    colorMixingOriginPotential_source]

theorem colorMixingOriginExteriorDerivativeComponent_source
    (first second : LorentzianIndex) :
    colorMixingOriginExteriorDerivativeComponent (1 / 2 : ℝ)
        first second =
      sourceP286ExteriorDerivativeComponent
        positiveSmoothUnifiedSource.legacy first second := by
  unfold colorMixingOriginExteriorDerivativeComponent
    sourceP286ExteriorDerivativeComponent
  simp_rw [colorMixingOriginExteriorDerivative_source]

theorem colorMixingOriginAffineIncrementLinear_source
    (formDirection : LorentzianIndex) :
    colorMixingOriginAffineIncrementLinear (1 / 2 : ℝ) formDirection =
      sourceP286AffineIncrementLinear positiveSmoothUnifiedSource.legacy
        formDirection := by
  apply ContinuousLinearMap.ext
  intro point
  unfold colorMixingOriginAffineIncrementLinear
    sourceP286AffineIncrementLinear
  simp_rw [colorMixingOriginExteriorDerivativeComponent_source]

theorem colorMixingOriginAffineConnectionField_source :
    colorMixingOriginAffineConnectionField (1 / 2 : ℝ) =
      sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy := by
  funext point direction
  unfold colorMixingOriginAffineConnectionField
    sourceP286AffineConnectionField
    colorMixingOriginAffineConnectionCoordinate
    sourceP286AffineConnectionCoordinate
  rw [colorMixingOriginPotential_source,
    colorMixingOriginAffineIncrementLinear_source]

/-! ## Fixed-field class reader -/

def colorMixingOriginConfiguration
    (t : ℝ) : StageNineHolonomicConfiguration :=
  installColorMixingOriginAffineConnection t residualLimitLorentzCarrierReader

@[simp] theorem colorMixingOriginConfiguration_gaugeConnection
    (t : ℝ) :
    (colorMixingOriginConfiguration t).gaugeConnection =
      colorMixingOriginAffineConnectionField t :=
  rfl

theorem colorMixingOriginConfiguration_preserves_fixedFields
    (t : ℝ) :
    (colorMixingOriginConfiguration t).coframe =
        positiveResidualLimitSixFieldCarrier.coframe ∧
      (colorMixingOriginConfiguration t).gaugeAuxiliary =
        positiveResidualLimitSixFieldCarrier.gaugeAuxiliary ∧
      (colorMixingOriginConfiguration t).scalar =
        positiveResidualLimitSixFieldCarrier.scalar ∧
      (colorMixingOriginConfiguration t).matter = 0 ∧
      (colorMixingOriginConfiguration t).conjugateMatter = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem colorMixingOriginConfiguration_source :
    colorMixingOriginConfiguration (1 / 2 : ℝ) =
      residualLimitLorentzCarrierReader := by
  unfold colorMixingOriginConfiguration
    installColorMixingOriginAffineConnection
  rw [colorMixingOriginAffineConnectionField_source]
  rfl

/-! ## Actual charged currents on the class -/

theorem colorMixingOriginConfiguration_scalar_eq_constantVacuum
    (t : ℝ) :
    (colorMixingOriginConfiguration t).scalar =
      fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  exact positiveResidualLimitSixFieldCarrier_scalar_eq_constantVacuum

theorem colorCartanP286Direction_scalar_action_zero
    (parameter : ℝ) :
    scalarMotherLieAction
        (p286LieBlockEmbed
          (parameter • colorCartanP286ConnectionDirection))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  apply scalarCoordinateEquiv.symm.injective
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  simp only [scalarCoordinateEquiv.symm_apply_apply, map_zero]
  rw [positive_sourceGeneratedVacuumBase, p286LieBlockEmbed_real_smul]
  change
    exteriorMotherLieAction 4
        (parameter • colorCartanMotherDirection)
        finiteGenerationJointBreakingScalar = 0
  rw [exteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    finiteGenerationJointBreakingScalar_colorCartan_action_zero, smul_zero]

theorem colorMixingP286Direction_scalar_action_zero
    (parameter : ℝ) :
    scalarMotherLieAction
        (p286LieBlockEmbed
          (parameter • colorMixingP286ConnectionDirection))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = 0 := by
  apply scalarCoordinateEquiv.symm.injective
  unfold scalarMotherLieAction sourceGeneratedVacuumCoordinates
  simp only [scalarCoordinateEquiv.symm_apply_apply, map_zero]
  rw [positive_sourceGeneratedVacuumBase, p286LieBlockEmbed_real_smul]
  change
    exteriorMotherLieAction 4
        (parameter • colorMixingMotherDirection)
        finiteGenerationJointBreakingScalar = 0
  rw [exteriorMotherLieAction_real_smul, LinearMap.smul_apply,
    finiteGenerationJointBreakingScalar_colorMixing_action_zero, smul_zero]

theorem colorMixingOriginScalarCovariantDerivative_origin_eq_zero
    (t : ℝ) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative
        (colorMixingOriginConfiguration t) 0 direction = 0 := by
  unfold holonomicScalarCovariantDerivative
  rw [colorMixingOriginConfiguration_scalar_eq_constantVacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add, colorMixingOriginConfiguration_gaugeConnection,
    colorMixingOriginAffineConnectionField_origin]
  fin_cases direction
  · exact colorCartanP286Direction_scalar_action_zero (1 / 2 : ℝ)
  · exact colorMixingP286Direction_scalar_action_zero t
  · simp [colorMixingOriginPotential]
  · simp [colorMixingOriginPotential]

theorem colorMixingOriginP286ScalarCurrent_eq_zero
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  unfold p286ScalarCurrentCoefficient
    scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeZero :
      (toContinuumPointField
        (colorMixingOriginConfiguration t) 0).scalarCovariantDerivative = 0 := by
    funext derivativeDirection
    exact colorMixingOriginScalarCovariantDerivative_origin_eq_zero
      t derivativeDirection
  rw [covariantDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem colorMixingOriginP286MatterCurrent_eq_zero
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  unfold p286MatterCurrentCoefficient
    matterGaugeConnectionFirstVariationDensity
  have conjugateZero :
      (toContinuumPointField
        (colorMixingOriginConfiguration t) 0).conjugateMatter = 0 := rfl
  rw [conjugateZero]
  simp [matterDualFrameRelative]

/-! ## Full-direction BF response -/

def colorMixingOriginLinearResponse
    (direction : P286GaugeOneForm) : ℝ :=
  -(1 / 2 : ℝ) *
    p286CoordinateLiePairing
      (p286CoordinateEquiv canonicalP286Generator)
      (p286CoordinateLieBracket
        (direction 0)
        (p286CoordinateEquiv colorMixingP286ConnectionDirection))

theorem specialUnitaryLiePairing_self_bracket_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix (suLieBracket matrix residual) = 0 := by
  unfold specialUnitaryLiePairing suLieBracket
  simp only [Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle'
    (matrix : Matrix n n ℂ) (residual : Matrix n n ℂ)
    (matrix : Matrix n n ℂ)]
  simp

theorem specialUnitaryLiePairing_zero_bracket_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing matrix (suLieBracket 0 residual) = 0 := by
  have bracketZero : suLieBracket (0 : SpecialUnitaryLieMatrix n) residual = 0 := by
    apply Subtype.ext
    simp [suLieBracket]
  rw [bracketZero]
  simp [specialUnitaryLiePairing]

theorem canonicalP286Pairing_colorCartanBracket_zero
    (residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (p286CoordinateEquiv canonicalP286Generator)
        (p286CoordinateLieBracket
          (p286CoordinateEquiv colorCartanP286ConnectionDirection)
          residual) = 0 := by
  unfold p286CoordinateLiePairing p286CoordinateLieBracket
  simp only [LinearEquiv.symm_apply_apply]
  unfold p286LiePairing p286LieBracket canonicalP286Generator
    colorCartanP286ConnectionDirection
  rw [specialUnitaryLiePairing_self_bracket_zero]
  rw [specialUnitaryLiePairing_zero_bracket_zero]
  simp [hyperchargeLiePairing]

theorem colorMixingOriginAlgebraicCurvatureDirection_zero
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeConnectionAlgebraicCurvatureDirection
        (colorMixingOriginConfiguration t) direction 0 0 =
      t • p286CoordinateLieBracket
          (direction 0)
          (p286CoordinateEquiv colorMixingP286ConnectionDirection) +
        (1 / 2 : ℝ) • p286CoordinateLieBracket
          (p286CoordinateEquiv colorCartanP286ConnectionDirection)
          (direction 1) := by
  unfold p286GaugeConnectionAlgebraicCurvatureDirection
    p286GaugeConnectionAlgebraicCurvatureVariation
    holonomicP286GaugeConnectionCoordinate
  simp only [colorMixingOriginConfiguration_gaugeConnection,
    colorMixingOriginAffineConnectionField_origin]
  simp [colorMixingOriginPotential, pairFirst, pairSecond,
    p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right,
    p286CoordinateEquiv.map_smul]

theorem colorMixingOriginP286BFAlgebraic_eq_momentum
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeBFAlgebraicCoefficient
        (colorMixingOriginConfiguration t) direction 0 =
      positiveResidualLimitP286DifferentialMomentum
        (p286GaugeConnectionAlgebraicCurvatureDirection
          (colorMixingOriginConfiguration t) direction 0) 0 := by
  unfold p286GaugeBFAlgebraicCoefficient
    positiveResidualLimitP286DifferentialMomentum
  change
    abs (Matrix.det (canonicalPhysicalSource.coframeAt 0)) *
        p286GaugeBFCurvatureIncrementDensity
          (canonicalPhysicalSource.coframeAt 0)
          (coframeGaugeSpacetimeHodgeLinear
            (canonicalPhysicalSource.coframeAt 0))
          (positiveResidualLimitP286AuxiliaryCoordinate 0)
          (p286GaugeConnectionAlgebraicCurvatureDirection
            (colorMixingOriginConfiguration t) direction 0) =
      abs (Matrix.det (canonicalPhysicalSource.coframeAt 0)) *
        p286GaugeAuxiliaryHodgePairingPolynomial
          (canonicalPhysicalSource.coframeAt 0)
          (positiveResidualLimitP286AuxiliaryCoordinate 0)
          (p286GaugeConnectionAlgebraicCurvatureDirection
            (colorMixingOriginConfiguration t) direction 0)
  rw [p286GaugeAuxiliaryHodgePairingPolynomial_eq]
  · rfl
  · rw [canonicalPhysicalSource_coframeAt_det]
    norm_num

theorem colorMixingOriginP286Divergence_eq_zero
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeConnectionBFDifferentialMomentumDivergence
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  change positiveResidualLimitP286Divergence direction = 0
  exact positiveResidualLimitP286Divergence_apply_eq_zero direction

theorem colorMixingOriginP286BFBalance_linear
    (t : ℝ) (direction : P286GaugeOneForm) :
    p286GaugeBFBalanceCoefficient
        (colorMixingOriginConfiguration t) direction 0 =
      t * colorMixingOriginLinearResponse direction := by
  unfold p286GaugeBFBalanceCoefficient
  rw [colorMixingOriginP286BFAlgebraic_eq_momentum,
    positiveResidualLimitP286DifferentialMomentum_normalForm,
    colorMixingOriginAlgebraicCurvatureDirection_zero,
    colorMixingOriginP286Divergence_eq_zero,
    p286CoordinateLiePairing_add_right,
    p286CoordinateLiePairing_smul_right,
    p286CoordinateLiePairing_smul_right,
    canonicalP286Pairing_colorCartanBracket_zero]
  unfold colorMixingOriginLinearResponse
  ring

/-! ## Full Euler--Lagrange residual, zero fiber, and transported endpoint -/

def colorMixingOriginP286Residual (t : ℝ) : P286GaugeOneForm → ℝ :=
  fun direction =>
    p286GaugeConnectionEulerLagrangeCoefficient
      positiveSmoothUnifiedSource
      (colorMixingOriginConfiguration t) direction 0

theorem colorMixingOriginP286Residual_apply_linear
    (t : ℝ) (direction : P286GaugeOneForm) :
    colorMixingOriginP286Residual t direction =
      t * colorMixingOriginLinearResponse direction := by
  unfold colorMixingOriginP286Residual
  rw [p286GaugeConnectionEulerLagrangeCoefficient_eq_sectorBalance,
    colorMixingOriginP286BFBalance_linear,
    colorMixingOriginP286ScalarCurrent_eq_zero,
    colorMixingOriginP286MatterCurrent_eq_zero]
  ring

theorem colorMixingOriginP286Residual_linear (t : ℝ) :
    colorMixingOriginP286Residual t =
      t • colorMixingOriginLinearResponse := by
  funext direction
  exact colorMixingOriginP286Residual_apply_linear t direction

theorem colorMixingOriginLinearResponse_probe_eq_neg_four :
    colorMixingOriginLinearResponse p286CommutatorProbe = -4 := by
  unfold colorMixingOriginLinearResponse p286CommutatorProbe
  change
    -(1 / 2 : ℝ) *
        p286CoordinateLiePairing
          (p286CoordinateEquiv canonicalP286Generator)
          (p286CoordinateLieBracket
            (p286CoordinateEquiv p286CommutatorProbeData)
            (p286CoordinateEquiv colorMixingP286ConnectionDirection)) = -4
  rw [p286CoordinateLieBracket_equiv_apply]
  change
    -(1 / 2 : ℝ) *
        p286CoordinateLiePairing
          (p286CoordinateEquiv canonicalP286Generator)
          (p286CoordinateEquiv p286DoubleCommutatorProbeData) = -4
  rw [p286ProbePairing_eq_eight]
  norm_num

theorem colorMixingOriginP286Residual_probe_normalForm (t : ℝ) :
    colorMixingOriginP286Residual t p286CommutatorProbe = -4 * t := by
  rw [colorMixingOriginP286Residual_apply_linear,
    colorMixingOriginLinearResponse_probe_eq_neg_four]
  ring

theorem colorMixingOriginP286Residual_eq_zero_iff (t : ℝ) :
    colorMixingOriginP286Residual t = 0 ↔ t = 0 := by
  constructor
  · intro residualZero
    have probeZero := congrFun residualZero p286CommutatorProbe
    rw [colorMixingOriginP286Residual_probe_normalForm] at probeZero
    norm_num at probeZero ⊢
    exact probeZero
  · rintro rfl
    rw [colorMixingOriginP286Residual_linear]
    simp

theorem colorMixingOriginP286Residual_source_probe_eq_neg_two :
    colorMixingOriginP286Residual (1 / 2 : ℝ) p286CommutatorProbe = -2 := by
  rw [colorMixingOriginP286Residual_probe_normalForm]
  norm_num

/-- The actual keep endpoint coordinate is derived from the source keep map
and the source-class coordinate.  It belongs to the P286 transport module,
not to any later gravity audit reader. -/
def colorMixingOriginActualKeepEndpointParameter : ℝ :=
  (1 - positiveSmoothUnifiedSource.legacy.sigma) * (1 / 2 : ℝ)

theorem colorMixingOriginActualKeepEndpointParameter_eq_quarter :
    colorMixingOriginActualKeepEndpointParameter = (1 / 4 : ℝ) := by
  unfold colorMixingOriginActualKeepEndpointParameter
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num

theorem colorMixingOriginP286Residual_endpoint_probe_eq_neg_one :
    colorMixingOriginP286Residual (1 / 4 : ℝ) p286CommutatorProbe = -1 := by
  rw [colorMixingOriginP286Residual_probe_normalForm]
  norm_num

theorem colorMixingOriginP286Residual_transport
    (t : ℝ) :
    colorMixingOriginP286Residual
        ((1 - positiveSmoothUnifiedSource.legacy.sigma) * t) =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        colorMixingOriginP286Residual t := by
  rw [colorMixingOriginP286Residual_linear,
    colorMixingOriginP286Residual_linear]
  ext direction
  simp
  ring

theorem colorMixingOriginP286Residual_actual_endpoint_transport :
    colorMixingOriginP286Residual (1 / 4 : ℝ) =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        colorMixingOriginP286Residual (1 / 2 : ℝ) := by
  convert colorMixingOriginP286Residual_transport (1 / 2 : ℝ) using 1
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num

theorem colorMixingOriginP286Residual_transport_iff
    (initial terminal : ℝ) :
    colorMixingOriginP286Residual terminal =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          colorMixingOriginP286Residual initial ↔
      terminal =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) * initial := by
  constructor
  · intro transportLaw
    have probeLaw := congrFun transportLaw p286CommutatorProbe
    have probeLaw' :
      -4 * terminal =
          (1 - positiveSmoothUnifiedSource.legacy.sigma) * (-4 * initial) := by
      simpa only [Pi.smul_apply, smul_eq_mul,
        colorMixingOriginP286Residual_probe_normalForm] using probeLaw
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half] at probeLaw'
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
    norm_num at probeLaw' ⊢
    linarith
  · rintro rfl
    exact colorMixingOriginP286Residual_transport initial

theorem colorMixingOriginP286Residual_actual_endpoint_unique
    (terminal : ℝ) :
    colorMixingOriginP286Residual terminal =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          colorMixingOriginP286Residual (1 / 2 : ℝ) ↔
      terminal = (1 / 4 : ℝ) := by
  rw [colorMixingOriginP286Residual_transport_iff,
    positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  norm_num

theorem colorMixingOriginP286Residual_actual_endpoint_eq_keep_source :
    colorMixingOriginP286Residual (1 / 4 : ℝ) =
      scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma
        (colorMixingOriginP286Residual (1 / 2 : ℝ)) := by
  change
    colorMixingOriginP286Residual (1 / 4 : ℝ) =
      (1 - positiveSmoothUnifiedSource.legacy.sigma) •
        colorMixingOriginP286Residual (1 / 2 : ℝ)
  exact colorMixingOriginP286Residual_actual_endpoint_transport

theorem colorMixingOriginP286Residual_actual_endpoint_ne_zero :
    colorMixingOriginP286Residual (1 / 4 : ℝ) ≠ 0 := by
  intro endpointZero
  have parameterZero :=
    (colorMixingOriginP286Residual_eq_zero_iff (1 / 4 : ℝ)).mp
      endpointZero
  norm_num at parameterZero

theorem colorMixingOriginP286Residual_actual_endpoint_has_no_naked_sink :
    (¬ ResidualTransportFixed
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
        (colorMixingOriginP286Residual (1 / 4 : ℝ))) ∧
      linearResidualTrace
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
        (colorMixingOriginP286Residual (1 / 4 : ℝ)) ≠ 0 := by
  have sigmaNeZero : positiveSmoothUnifiedSource.legacy.sigma ≠ 0 := by
    rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
    norm_num
  have keepActive :
      ResidualTransportActive
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma :
          (P286GaugeOneForm → ℝ) →ₗ[ℝ] (P286GaugeOneForm → ℝ)) :=
    scalarKeepLinearMap_active_of_ne_zero
      positiveSmoothUnifiedSource.legacy.sigma sigmaNeZero
  constructor
  · intro fixed
    exact colorMixingOriginP286Residual_actual_endpoint_ne_zero
      ((residualTransport_fixed_iff_zero_residual
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
        keepActive (colorMixingOriginP286Residual (1 / 4 : ℝ))).mp fixed)
  · intro traceZero
    have fixed :=
      (residualTransport_fixed_iff_zero_trace
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
        keepActive (colorMixingOriginP286Residual (1 / 4 : ℝ))).mpr traceZero
    exact colorMixingOriginP286Residual_actual_endpoint_ne_zero
      ((residualTransport_fixed_iff_zero_residual
        (scalarKeepLinearMap positiveSmoothUnifiedSource.legacy.sigma)
        keepActive (colorMixingOriginP286Residual (1 / 4 : ℝ))).mp fixed)

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorMixingOriginResidualTransport

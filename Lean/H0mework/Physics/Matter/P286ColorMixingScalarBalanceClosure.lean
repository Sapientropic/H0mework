import H0mework.Physics.Matter.P286ColorMixingOriginResidualTransport

/-!
# S9-C3h56: scalar closure on the P286 color-mixing transport class

C3h41 generated a one-dimensional P286 origin class whose affine first jet
is forced by the actual source curvature and whose unique keep endpoint is
`t = 1/4`.  This module evaluates the scalar equation on that entire class.

The scalar covariant derivative vanishes at the origin for every `t`.  More
importantly, its same-direction first derivative also vanishes: the affine
jet reads the antisymmetric residual carrier, so the only diagonal component
seen by the scalar divergence is `F_{μμ} = 0`.  A general canonical-coframe
momentum lemma then converts that fact into vanishing of the actual scalar
differential divergence.  The kinetic algebraic, potential, and Yukawa terms
vanish independently, hence the complete scalar Euler--Lagrange coordinate is
zero for every transported state in the class.

No scalar zero, differential-response match, endpoint witness, source knob,
branch choice, shell, or stationarity receipt is accepted at the theorem
mouth.  The conclusion is a standing-relevant scalar projection only; it does
not claim a zero joint residual.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineP286ColorMixingScalarBalanceClosure

open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ColorMixingOriginResidualTransport
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceGravityMouthResidualOrbitConnectionLift
open StageNineResidualLimitP286ScalarSourceNormalForm
open StageNineResidualLimitScalarBalanceClosure
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance p286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def colorMixingScalarCovariantDerivative
    (t : ℝ) (point : BasePoint) (direction : LorentzianIndex) :
    ScalarCoordinateCarrier :=
  holonomicScalarCovariantDerivative
    (colorMixingOriginConfiguration t) point direction

theorem colorMixingScalarCovariantDerivative_eq_fixedVacuumAction
    (t : ℝ) (point : BasePoint) (direction : LorentzianIndex) :
    colorMixingScalarCovariantDerivative t point direction =
      scalarP286ActionBilinear
        (colorMixingOriginAffineConnectionCoordinate t point direction)
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  unfold colorMixingScalarCovariantDerivative
    holonomicScalarCovariantDerivative
  rw [colorMixingOriginConfiguration_scalar_eq_constantVacuum]
  simp only [fieldDirectionalDerivative, fderiv_const_apply, zero_apply,
    zero_add, colorMixingOriginConfiguration_gaugeConnection,
    colorMixingOriginAffineConnectionField]
  rfl

theorem colorMixingScalarCovariantDerivative_directionalDerivative
    (t : ℝ) (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          colorMixingScalarCovariantDerivative t point formDirection)
        0 derivativeDirection =
      scalarP286ActionBilinear
        ((1 / 2 : ℝ) •
          p286CoordinateEquiv
            (colorMixingOriginExteriorDerivativeComponent t
              derivativeDirection formDirection))
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    colorMixingOriginAffineConnectionCoordinate t point formDirection
  have connectionDifferentiable : DifferentiableAt ℝ connection 0 := by
    simpa [connection, colorMixingOriginAffineConnectionField] using
      ((colorMixingOriginAffineConnectionField_smooth t formDirection).differentiable
        (by simp)).differentiableAt
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
        (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).hasFDerivAt.comp
      0 connectionDifferentiable.hasFDerivAt).fderiv
  rw [show (fun point =>
      colorMixingScalarCovariantDerivative t point formDirection) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact colorMixingScalarCovariantDerivative_eq_fixedVacuumAction
      t point formDirection]
  unfold fieldDirectionalDerivative
  rw [actionDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change scalarP286ActionBilinear
      (fieldDirectionalDerivative connection 0 derivativeDirection)
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) = _
  exact congrArg
    (fun coordinate => scalarP286ActionBilinear coordinate
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource))
    (colorMixingOriginAffineConnectionCoordinate_directionalDerivative_origin
      t derivativeDirection formDirection)

theorem colorMixingScalarCovariantDerivative_diagonalDerivative_eq_zero
    (t : ℝ) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => colorMixingScalarCovariantDerivative t point direction)
        0 direction = 0 := by
  rw [colorMixingScalarCovariantDerivative_directionalDerivative]
  have selfZero :
      colorMixingOriginExteriorDerivativeComponent t direction direction = 0 := by
    fin_cases direction <;>
      simp [colorMixingOriginExteriorDerivativeComponent]
  rw [selfZero]
  simp

theorem colorMixingScalarCovariantDerivative_differentiable
    (t : ℝ) (direction : LorentzianIndex) :
    Differentiable ℝ
      (fun point => colorMixingScalarCovariantDerivative t point direction) := by
  let action := scalarP286ActionBilinear.toContinuousBilinearMap
  let connection := fun point =>
    colorMixingOriginAffineConnectionCoordinate t point direction
  have connectionDifferentiable : Differentiable ℝ connection := by
    simpa [connection, colorMixingOriginAffineConnectionField] using
      (colorMixingOriginAffineConnectionField_smooth t direction).differentiable
        (by simp)
  rw [show (fun point =>
      colorMixingScalarCovariantDerivative t point direction) =
      fun point =>
        action (connection point)
          (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) by
    funext point
    exact colorMixingScalarCovariantDerivative_eq_fixedVacuumAction
      t point direction]
  exact (action.flip
    (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)).differentiable.comp
      connectionDifferentiable

def canonicalCoframeScalarDifferentialMomentum
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) : ℝ :=
  abs (Matrix.det (positiveResidualLimitSixFieldCarrier.coframe point)) *
    ((1 / 2 : ℝ) *
      ∑ first : LorentzianIndex,
        ∑ second : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              first second) *
            (scalarCoordinatePairingRe
                (scalarVariationDifferentialDirection direction
                  derivativeDirection first)
                (covariantDerivative point second) +
              scalarCoordinatePairingRe
                (covariantDerivative point first)
                (scalarVariationDifferentialDirection direction
                  derivativeDirection second)))

def canonicalCoframeScalarDivergence
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier) : ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    fieldDirectionalDerivative
      (canonicalCoframeScalarDifferentialMomentum covariantDerivative direction
        derivativeDirection) 0 derivativeDirection

theorem colorMixing_scalarDifferentialMomentum_eq_canonical
    (t : ℝ) (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction derivativeDirection point =
      canonicalCoframeScalarDifferentialMomentum
        (colorMixingScalarCovariantDerivative t) direction
        derivativeDirection point := by
  have coframePoint :
      (toContinuumPointField (colorMixingOriginConfiguration t) point).coframe =
        positiveResidualLimitSixFieldCarrier.coframe point := by
    rfl
  have covariantDerivativePoint :
      (toContinuumPointField
        (colorMixingOriginConfiguration t) point).scalarCovariantDerivative =
        colorMixingScalarCovariantDerivative t point := by
    rfl
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    canonicalCoframeScalarDifferentialMomentum generatedVolumeDensity
  rw [coframePoint, covariantDerivativePoint]
  simp [scalarFrameRelativeCovariantDerivative]

theorem colorMixing_scalarDivergence_eq_canonical
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 =
      canonicalCoframeScalarDivergence
        (colorMixingScalarCovariantDerivative t) direction := by
  unfold scalarDifferentialMomentumDivergence
    canonicalCoframeScalarDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  apply congrArg
    (fun momentum : BasePoint → ℝ =>
      fieldDirectionalDerivative momentum 0 derivativeDirection)
  funext point
  exact colorMixing_scalarDifferentialMomentum_eq_canonical
    t direction derivativeDirection point

theorem canonicalCoframeScalarDifferentialMomentum_eq_pairingSums
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) (point : BasePoint) :
    canonicalCoframeScalarDifferentialMomentum covariantDerivative direction
        derivativeDirection point =
      (1 / 2 : ℝ) *
        ((∑ formDirection : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              derivativeDirection formDirection) *
            scalarCoordinatePairingRe direction
              (covariantDerivative point formDirection)) +
        (∑ formDirection : LorentzianIndex,
          ((lorentzianMetricOfCoframe
            (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
              formDirection derivativeDirection) *
            scalarCoordinatePairingRe
              (covariantDerivative point formDirection) direction)) := by
  unfold canonicalCoframeScalarDifferentialMomentum
  rw [positiveResidualLimitSixFieldCarrier_volume_eq_one, one_mul]
  fin_cases derivativeDirection <;>
    simp [scalarVariationDifferentialDirection, scalarCoordinatePairingRe,
      Fin.sum_univ_four] <;>
    ring

def canonicalCoframeScalarMomentumLeftTerm
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  ((lorentzianMetricOfCoframe
    (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
      derivativeDirection formDirection) *
    scalarCoordinatePairingRe direction
      (covariantDerivative point formDirection)

def canonicalCoframeScalarMomentumRightTerm
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  ((lorentzianMetricOfCoframe
    (positiveResidualLimitSixFieldCarrier.coframe point))⁻¹
      formDirection derivativeDirection) *
    scalarCoordinatePairingRe
      (covariantDerivative point formDirection) direction

theorem canonicalCoframeScalarMomentumLeftPairing_differentiable
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      scalarCoordinatePairingRe direction
        (covariantDerivative point formDirection)) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  exact pairing.differentiable.comp
    (covariantDerivativeDifferentiable formDirection)

theorem canonicalCoframeScalarMomentumRightPairing_differentiable
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (formDirection : LorentzianIndex) :
    Differentiable ℝ (fun point =>
      scalarCoordinatePairingRe
        (covariantDerivative point formDirection) direction) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  exact pairing.differentiable.comp
    (covariantDerivativeDifferentiable formDirection)

theorem canonicalCoframeScalarMomentumLeftPairing_directionalDerivative
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe direction
          (covariantDerivative point formDirection))
        0 derivativeDirection =
      scalarCoordinatePairingRe direction
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  have derivative := pairing.hasFDerivAt.comp 0
    (covariantDerivativeDifferentiable formDirection).differentiableAt.hasFDerivAt
  change fieldDirectionalDerivative
      (fun point => pairing (covariantDerivative point formDirection))
      0 derivativeDirection =
    pairing
      (fieldDirectionalDerivative
        (fun point => covariantDerivative point formDirection)
        0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing
      (covariantDerivative point formDirection)) =
      pairing ∘ (fun point => covariantDerivative point formDirection) by rfl,
    derivative.fderiv]
  rfl

theorem canonicalCoframeScalarMomentumRightPairing_directionalDerivative
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => scalarCoordinatePairingRe
          (covariantDerivative point formDirection) direction)
        0 derivativeDirection =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection) direction := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  have derivative := pairing.hasFDerivAt.comp 0
    (covariantDerivativeDifferentiable formDirection).differentiableAt.hasFDerivAt
  change fieldDirectionalDerivative
      (fun point => pairing (covariantDerivative point formDirection))
      0 derivativeDirection =
    pairing
      (fieldDirectionalDerivative
        (fun point => covariantDerivative point formDirection)
        0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show (fun point => pairing
      (covariantDerivative point formDirection)) =
      pairing ∘ (fun point => covariantDerivative point formDirection) by rfl,
    derivative.fderiv]
  rfl

theorem canonicalCoframeScalarMomentumLeftTerm_differentiable
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    Differentiable ℝ
      (canonicalCoframeScalarMomentumLeftTerm covariantDerivative direction
        derivativeDirection formDirection) := by
  unfold canonicalCoframeScalarMomentumLeftTerm
  exact (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
    derivativeDirection formDirection).mul
      (canonicalCoframeScalarMomentumLeftPairing_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        formDirection)

theorem canonicalCoframeScalarMomentumRightTerm_differentiable
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    Differentiable ℝ
      (canonicalCoframeScalarMomentumRightTerm covariantDerivative direction
        derivativeDirection formDirection) := by
  unfold canonicalCoframeScalarMomentumRightTerm
  exact (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
    formDirection derivativeDirection).mul
      (canonicalCoframeScalarMomentumRightPairing_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        formDirection)

theorem canonicalCoframeScalarMomentumLeftTerm_diagonalDerivative_eq_zero
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (covariantDerivativeOriginZero : ∀ formDirection,
      covariantDerivative 0 formDirection = 0)
    (covariantDerivativeDiagonalZero : ∀ formDirection,
      fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 formDirection = 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (canonicalCoframeScalarMomentumLeftTerm covariantDerivative direction
          derivativeDirection formDirection)
        0 derivativeDirection = 0 := by
  unfold canonicalCoframeScalarMomentumLeftTerm
  rw [fieldDirectionalDerivative_mul_of_right_zero
    _ _
    (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
      derivativeDirection formDirection).differentiableAt
    (canonicalCoframeScalarMomentumLeftPairing_differentiable
      covariantDerivative covariantDerivativeDifferentiable direction
      formDirection).differentiableAt]
  · rw [canonicalCoframeScalarMomentumLeftPairing_directionalDerivative
      covariantDerivative covariantDerivativeDifferentiable,
      positiveResidualLimitSixFieldCarrier_metricInv_origin_component]
    fin_cases derivativeDirection <;> fin_cases formDirection <;>
      simp [minkowskiInternalMetric,
        covariantDerivativeDiagonalZero, scalarCoordinatePairingRe]
  · rw [covariantDerivativeOriginZero]
    simp [scalarCoordinatePairingRe]

theorem canonicalCoframeScalarMomentumRightTerm_diagonalDerivative_eq_zero
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (covariantDerivativeOriginZero : ∀ formDirection,
      covariantDerivative 0 formDirection = 0)
    (covariantDerivativeDiagonalZero : ∀ formDirection,
      fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 formDirection = 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (canonicalCoframeScalarMomentumRightTerm covariantDerivative direction
          derivativeDirection formDirection)
        0 derivativeDirection = 0 := by
  unfold canonicalCoframeScalarMomentumRightTerm
  rw [fieldDirectionalDerivative_mul_of_right_zero
    _ _
    (positiveResidualLimitSixFieldCarrier_metricInv_component_differentiable
      formDirection derivativeDirection).differentiableAt
    (canonicalCoframeScalarMomentumRightPairing_differentiable
      covariantDerivative covariantDerivativeDifferentiable direction
      formDirection).differentiableAt]
  · rw [canonicalCoframeScalarMomentumRightPairing_directionalDerivative
      covariantDerivative covariantDerivativeDifferentiable,
      positiveResidualLimitSixFieldCarrier_metricInv_origin_component]
    fin_cases derivativeDirection <;> fin_cases formDirection <;>
      simp [minkowskiInternalMetric,
        covariantDerivativeDiagonalZero, scalarCoordinatePairingRe]
  · rw [covariantDerivativeOriginZero]
    simp [scalarCoordinatePairingRe]

theorem canonicalCoframeScalarDifferentialMomentum_diagonalDerivative_eq_zero
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (covariantDerivativeOriginZero : ∀ formDirection,
      covariantDerivative 0 formDirection = 0)
    (covariantDerivativeDiagonalZero : ∀ formDirection,
      fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 formDirection = 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (canonicalCoframeScalarDifferentialMomentum covariantDerivative direction
          derivativeDirection)
        0 derivativeDirection = 0 := by
  let leftSum := fun point =>
    ∑ formDirection : LorentzianIndex,
      canonicalCoframeScalarMomentumLeftTerm covariantDerivative direction
        derivativeDirection formDirection point
  let rightSum := fun point =>
    ∑ formDirection : LorentzianIndex,
      canonicalCoframeScalarMomentumRightTerm covariantDerivative direction
        derivativeDirection formDirection point
  have momentumFunction :
      canonicalCoframeScalarDifferentialMomentum covariantDerivative direction
          derivativeDirection =
        fun point => (1 / 2 : ℝ) * (leftSum point + rightSum point) := by
    funext point
    rw [canonicalCoframeScalarDifferentialMomentum_eq_pairingSums]
    rfl
  have leftDifferentiableGlobal : Differentiable ℝ leftSum := by
    change Differentiable ℝ
      (∑ formDirection : LorentzianIndex,
        canonicalCoframeScalarMomentumLeftTerm covariantDerivative direction
          derivativeDirection formDirection)
    exact Differentiable.sum fun formDirection _ =>
      canonicalCoframeScalarMomentumLeftTerm_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        derivativeDirection formDirection
  have rightDifferentiableGlobal : Differentiable ℝ rightSum := by
    change Differentiable ℝ
      (∑ formDirection : LorentzianIndex,
        canonicalCoframeScalarMomentumRightTerm covariantDerivative direction
          derivativeDirection formDirection)
    exact Differentiable.sum fun formDirection _ =>
      canonicalCoframeScalarMomentumRightTerm_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        derivativeDirection formDirection
  have leftDifferentiable : DifferentiableAt ℝ leftSum 0 :=
    leftDifferentiableGlobal.differentiableAt
  have rightDifferentiable : DifferentiableAt ℝ rightSum 0 :=
    rightDifferentiableGlobal.differentiableAt
  rw [momentumFunction]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul
      (a := fun point => leftSum point + rightSum point)
      (leftDifferentiable.add rightDifferentiable)
      (1 / 2 : ℝ),
    fderiv_fun_add leftDifferentiable rightDifferentiable]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change (1 / 2 : ℝ) *
      (fieldDirectionalDerivative leftSum 0 derivativeDirection +
        fieldDirectionalDerivative rightSum 0 derivativeDirection) = 0
  have leftZero :
      fieldDirectionalDerivative leftSum 0 derivativeDirection = 0 := by
    unfold leftSum fieldDirectionalDerivative
    rw [fderiv_fun_sum (fun formDirection _ =>
      (canonicalCoframeScalarMomentumLeftTerm_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        derivativeDirection formDirection).differentiableAt)]
    change (∑ formDirection : LorentzianIndex,
      fieldDirectionalDerivative
        (canonicalCoframeScalarMomentumLeftTerm covariantDerivative direction
          derivativeDirection formDirection) 0 derivativeDirection) = 0
    exact Finset.sum_eq_zero fun formDirection _ =>
      canonicalCoframeScalarMomentumLeftTerm_diagonalDerivative_eq_zero
        covariantDerivative covariantDerivativeDifferentiable
        covariantDerivativeOriginZero covariantDerivativeDiagonalZero direction
        derivativeDirection formDirection
  have rightZero :
      fieldDirectionalDerivative rightSum 0 derivativeDirection = 0 := by
    unfold rightSum fieldDirectionalDerivative
    rw [fderiv_fun_sum (fun formDirection _ =>
      (canonicalCoframeScalarMomentumRightTerm_differentiable
        covariantDerivative covariantDerivativeDifferentiable direction
        derivativeDirection formDirection).differentiableAt)]
    change (∑ formDirection : LorentzianIndex,
      fieldDirectionalDerivative
        (canonicalCoframeScalarMomentumRightTerm covariantDerivative direction
          derivativeDirection formDirection) 0 derivativeDirection) = 0
    exact Finset.sum_eq_zero fun formDirection _ =>
      canonicalCoframeScalarMomentumRightTerm_diagonalDerivative_eq_zero
        covariantDerivative covariantDerivativeDifferentiable
        covariantDerivativeOriginZero covariantDerivativeDiagonalZero direction
        derivativeDirection formDirection
  rw [leftZero, rightZero]
  norm_num

theorem canonicalCoframeScalarDivergence_eq_zero
    (covariantDerivative : BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (covariantDerivativeDifferentiable : ∀ formDirection,
      Differentiable ℝ (fun point => covariantDerivative point formDirection))
    (covariantDerivativeOriginZero : ∀ formDirection,
      covariantDerivative 0 formDirection = 0)
    (covariantDerivativeDiagonalZero : ∀ formDirection,
      fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 formDirection = 0)
    (direction : ScalarCoordinateCarrier) :
    canonicalCoframeScalarDivergence covariantDerivative direction = 0 := by
  unfold canonicalCoframeScalarDivergence
  exact Finset.sum_eq_zero fun derivativeDirection _ =>
    canonicalCoframeScalarDifferentialMomentum_diagonalDerivative_eq_zero
      covariantDerivative covariantDerivativeDifferentiable
      covariantDerivativeOriginZero covariantDerivativeDiagonalZero direction
      derivativeDirection

theorem colorMixing_scalarDivergence_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  rw [colorMixing_scalarDivergence_eq_canonical]
  exact canonicalCoframeScalarDivergence_eq_zero
    (colorMixingScalarCovariantDerivative t)
    (colorMixingScalarCovariantDerivative_differentiable t)
    (colorMixingOriginScalarCovariantDerivative_origin_eq_zero t)
    (colorMixingScalarCovariantDerivative_diagonalDerivative_eq_zero t)
    direction

theorem colorMixing_scalarKineticAlgebraic_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity
        positiveSmoothUnifiedSource 0 0
        (toContinuumPointField (colorMixingOriginConfiguration t) 0)
        (holonomicScalarVariationAlgebraicDirection
          (colorMixingOriginConfiguration t) direction 0) = 0 := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  have covariantDerivativeZero :
      (toContinuumPointField
        (colorMixingOriginConfiguration t) 0).scalarCovariantDerivative = 0 := by
    funext formDirection
    exact colorMixingOriginScalarCovariantDerivative_origin_eq_zero
      t formDirection
  rw [covariantDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

theorem colorMixing_scalarPotential_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
        (toContinuumPointField (colorMixingOriginConfiguration t) 0)
        direction = 0 := by
  unfold scalarPotentialFirstVariation
  rw [show
    (toContinuumPointField (colorMixingOriginConfiguration t) 0).scalar =
      sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource by
    change (colorMixingOriginConfiguration t).scalar 0 = _
    rw [colorMixingOriginConfiguration_scalar_eq_constantVacuum]]
  simp

theorem colorMixing_scalarYukawa_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField (colorMixingOriginConfiguration t) 0)
        direction = 0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  change
    ((colorMixingOriginConfiguration t).conjugateMatter 0
      (chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm direction)
        ((colorMixingOriginConfiguration t).matter 0))).re = 0
  rfl

theorem colorMixing_scalarAlgebraic_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [colorMixing_scalarKineticAlgebraic_zero,
    colorMixing_scalarPotential_zero,
    colorMixing_scalarYukawa_zero]
  ring

theorem colorMixing_scalarResidual_zero
    (t : ℝ) (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0 = 0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [colorMixing_scalarAlgebraic_zero,
    colorMixing_scalarDivergence_zero]
  ring

theorem colorMixing_scalarResidual_allDirections_zero
    (t : ℝ) :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        (colorMixingOriginConfiguration t) direction 0) = 0 := by
  funext direction
  exact colorMixing_scalarResidual_zero t direction

end

end SaturationMonoid.PhysicsCore.StageNineP286ColorMixingScalarBalanceClosure

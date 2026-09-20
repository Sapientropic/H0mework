import H0mework.Physics.Coframe.BiradialCoframeResponse
import H0mework.Physics.Geometry.ScalarPointwiseEquation

/-!
# Stage-9 scalar response on a constant biradial coframe

This module reduces the actual scalar Euler--Lagrange equation at the
canonical origin on a positive constant biradial coframe.  The reduction
uses only local properties of the existing scalar covariant derivative:
its value at the origin, its same-direction first derivatives, and local
differentiability.

The result is an action-level readout.  It accepts no endpoint, target
residual, second-jet representative, inverse, source slot, branch choice,
field equation, or stationarity certificate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineBiradialScalarOriginResponse

open ProofFreeRicherAnholonomicSource
open StageNineBiradialCoframeResponse
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open SU7ExteriorBreakingYukawa

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Constant biradial inverse metric -/

/-- The inverse metric computed from the positive biradial coframe. -/
def biradialInverseMetric (a b : ℝ) : LorentzianMetric :=
  Matrix.diagonal
    ![-(a ^ 2)⁻¹, (a ^ 2)⁻¹, (b ^ 2)⁻¹, (b ^ 2)⁻¹]

theorem lorentzianMetricOfCoframe_biradial_inv
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (lorentzianMetricOfCoframe (biradialCoframe a b))⁻¹ =
      biradialInverseMetric a b := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [biradialInverseMetric, biradialCoframe,
      lorentzianMetricOfCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp [ha.ne', hb.ne']

/-! ## Actual differential momentum normal form -/

/-- Volume times inverse-metric weight in each diagonal spacetime direction. -/
def biradialScalarMomentumWeight (a b : ℝ) :
    LorentzianIndex → ℝ :=
  ![-b ^ 2, b ^ 2, a ^ 2, a ^ 2]

/-- The action-derived scalar momentum normal form on a constant biradial
coframe.  The frame-relative source action has disappeared only through the
already proved pairing invariance; the scalar covariant derivative remains
the one read from the supplied configuration. -/
def biradialScalarDifferentialMomentumNormalForm
    (a b : ℝ)
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (point : BasePoint) : ℝ :=
  (1 / 2 : ℝ) *
    biradialScalarMomentumWeight a b derivativeDirection *
      (scalarCoordinatePairingRe direction
          (covariantDerivative point derivativeDirection) +
        scalarCoordinatePairingRe
          (covariantDerivative point derivativeDirection) direction)

theorem scalarDifferentialMomentum_eq_biradialNormalForm
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (coframe_eq :
      configuration.coframe = fun _ => biradialCoframe a b)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarDifferentialMomentum source configuration direction
        derivativeDirection =
      biradialScalarDifferentialMomentumNormalForm a b
        (holonomicScalarCovariantDerivative configuration)
        direction derivativeDirection := by
  funext point
  have coframePoint :
      (toContinuumPointField configuration point).coframe =
        biradialCoframe a b := by
    change configuration.coframe point = biradialCoframe a b
    rw [coframe_eq]
  have determinantPositive : 0 < a ^ 2 * b ^ 2 := by
    positivity
  unfold scalarDifferentialMomentum
    scalarGaugeConnectionKineticFirstVariationDensity
    biradialScalarDifferentialMomentumNormalForm
    generatedVolumeDensity
  rw [coframePoint, biradialCoframe_det,
    abs_of_pos determinantPositive,
    lorentzianMetricOfCoframe_biradial_inv ha hb]
  fin_cases derivativeDirection <;>
    simp [biradialScalarMomentumWeight, biradialInverseMetric,
      scalarVariationDifferentialDirection,
      scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe,
      toContinuumPointField, Fin.sum_univ_four] <;>
    field_simp [ha.ne', hb.ne']

private theorem scalarPairingLeft_directionalDerivative
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point => covariantDerivative point formDirection) 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          scalarCoordinatePairingRe direction
            (covariantDerivative point formDirection))
        0 derivativeDirection =
      scalarCoordinatePairingRe direction
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  have derivative :=
    pairing.hasFDerivAt.comp 0
      (differentiable formDirection).hasFDerivAt
  change
    fieldDirectionalDerivative
        (fun point => pairing (covariantDerivative point formDirection))
        0 derivativeDirection =
      pairing
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show
      (fun point => pairing (covariantDerivative point formDirection)) =
        pairing ∘
          (fun point => covariantDerivative point formDirection) by
      rfl,
    derivative.fderiv]
  rfl

private theorem scalarPairingRight_directionalDerivative
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point => covariantDerivative point formDirection) 0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          scalarCoordinatePairingRe
            (covariantDerivative point formDirection) direction)
        0 derivativeDirection =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection)
        direction := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  have derivative :=
    pairing.hasFDerivAt.comp 0
      (differentiable formDirection).hasFDerivAt
  change
    fieldDirectionalDerivative
        (fun point => pairing (covariantDerivative point formDirection))
        0 derivativeDirection =
      pairing
        (fieldDirectionalDerivative
          (fun point => covariantDerivative point formDirection)
          0 derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show
      (fun point => pairing (covariantDerivative point formDirection)) =
        pairing ∘
          (fun point => covariantDerivative point formDirection) by
      rfl,
    derivative.fderiv]
  rfl

theorem scalarPairingLeft_directionalDerivative_at
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (point : BasePoint)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun candidate => covariantDerivative candidate formDirection)
          point)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          scalarCoordinatePairingRe direction
            (covariantDerivative candidate formDirection))
        point derivativeDirection =
      scalarCoordinatePairingRe direction
        (fieldDirectionalDerivative
          (fun candidate => covariantDerivative candidate formDirection)
          point derivativeDirection) := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
  have derivative :=
    pairing.hasFDerivAt.comp point
      (differentiable formDirection).hasFDerivAt
  change
    fieldDirectionalDerivative
        (fun candidate => pairing (covariantDerivative candidate formDirection))
        point derivativeDirection =
      pairing
        (fieldDirectionalDerivative
          (fun candidate => covariantDerivative candidate formDirection)
          point derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show
      (fun candidate => pairing (covariantDerivative candidate formDirection)) =
        pairing ∘
          (fun candidate => covariantDerivative candidate formDirection) by
      rfl,
    derivative.fderiv]
  rfl

theorem scalarPairingRight_directionalDerivative_at
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (point : BasePoint)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun candidate => covariantDerivative candidate formDirection)
          point)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection formDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          scalarCoordinatePairingRe
            (covariantDerivative candidate formDirection) direction)
        point derivativeDirection =
      scalarCoordinatePairingRe
        (fieldDirectionalDerivative
          (fun candidate => covariantDerivative candidate formDirection)
          point derivativeDirection)
        direction := by
  let pairing :=
    scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
  have derivative :=
    pairing.hasFDerivAt.comp point
      (differentiable formDirection).hasFDerivAt
  change
    fieldDirectionalDerivative
        (fun candidate => pairing (covariantDerivative candidate formDirection))
        point derivativeDirection =
      pairing
        (fieldDirectionalDerivative
          (fun candidate => covariantDerivative candidate formDirection)
          point derivativeDirection)
  unfold fieldDirectionalDerivative
  rw [show
      (fun candidate => pairing (covariantDerivative candidate formDirection)) =
        pairing ∘
          (fun candidate => covariantDerivative candidate formDirection) by
      rfl,
    derivative.fderiv]
  rfl

/-- Exact same-direction derivative of the constant-biradial scalar momentum
normal form at an arbitrary spacetime point. -/
theorem biradialScalarDifferentialMomentumNormalForm_diagonalDerivative
    (a b : ℝ)
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (point : BasePoint)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun candidate => covariantDerivative candidate formDirection)
          point)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (biradialScalarDifferentialMomentumNormalForm a b
          covariantDerivative direction derivativeDirection)
        point derivativeDirection =
      ((1 / 2 : ℝ) *
          biradialScalarMomentumWeight a b derivativeDirection) *
        (scalarCoordinatePairingRe direction
            (fieldDirectionalDerivative
              (fun candidate =>
                covariantDerivative candidate derivativeDirection)
              point derivativeDirection) +
          scalarCoordinatePairingRe
            (fieldDirectionalDerivative
              (fun candidate =>
                covariantDerivative candidate derivativeDirection)
              point derivativeDirection)
            direction) := by
  let left : BasePoint → ℝ := fun candidate =>
    scalarCoordinatePairingRe direction
      (covariantDerivative candidate derivativeDirection)
  let right : BasePoint → ℝ := fun candidate =>
    scalarCoordinatePairingRe
      (covariantDerivative candidate derivativeDirection) direction
  have leftDifferentiable : DifferentiableAt ℝ left point := by
    let pairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
    exact pairing.differentiableAt.comp point
      (differentiable derivativeDirection)
  have rightDifferentiable : DifferentiableAt ℝ right point := by
    let pairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
    exact pairing.differentiableAt.comp point
      (differentiable derivativeDirection)
  let combined : BasePoint → ℝ := left + right
  have combinedDifferentiable : DifferentiableAt ℝ combined point :=
    leftDifferentiable.add rightDifferentiable
  have combinedDerivative :
      fderiv ℝ combined point =
        fderiv ℝ left point + fderiv ℝ right point := by
    unfold combined
    change
      fderiv ℝ (fun candidate => left candidate + right candidate) point =
        fderiv ℝ left point + fderiv ℝ right point
    exact fderiv_fun_add leftDifferentiable rightDifferentiable
  rw [show
    biradialScalarDifferentialMomentumNormalForm a b covariantDerivative
        direction derivativeDirection =
      fun candidate =>
        ((1 / 2 : ℝ) *
          biradialScalarMomentumWeight a b derivativeDirection) *
            combined candidate by
    funext candidate
    rfl]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul combinedDifferentiable
      ((1 / 2 : ℝ) *
        biradialScalarMomentumWeight a b derivativeDirection),
    combinedDerivative]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change
    ((1 / 2 : ℝ) *
        biradialScalarMomentumWeight a b derivativeDirection) *
      (fieldDirectionalDerivative left point derivativeDirection +
        fieldDirectionalDerivative right point derivativeDirection) = _
  rw [show
      fieldDirectionalDerivative left point derivativeDirection =
        scalarCoordinatePairingRe direction
          (fieldDirectionalDerivative
            (fun candidate =>
              covariantDerivative candidate derivativeDirection)
            point derivativeDirection) by
      exact scalarPairingLeft_directionalDerivative_at covariantDerivative
        point differentiable direction derivativeDirection
        derivativeDirection,
    show
      fieldDirectionalDerivative right point derivativeDirection =
        scalarCoordinatePairingRe
          (fieldDirectionalDerivative
            (fun candidate =>
              covariantDerivative candidate derivativeDirection)
            point derivativeDirection)
          direction by
      exact scalarPairingRight_directionalDerivative_at covariantDerivative
        point differentiable direction derivativeDirection
        derivativeDirection]
  rfl

theorem
    biradialScalarDifferentialMomentumNormalForm_diagonalDerivative_eq_zero
    (a b : ℝ)
    (covariantDerivative :
      BasePoint → LorentzianIndex → ScalarCoordinateCarrier)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point => covariantDerivative point formDirection) 0)
    (diagonalDerivativeZero :
      ∀ formDirection,
        fieldDirectionalDerivative
            (fun point => covariantDerivative point formDirection)
            0 formDirection =
          0)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (biradialScalarDifferentialMomentumNormalForm a b
          covariantDerivative direction derivativeDirection)
        0 derivativeDirection = 0 := by
  let left : BasePoint → ℝ := fun point =>
    scalarCoordinatePairingRe direction
      (covariantDerivative point derivativeDirection)
  let right : BasePoint → ℝ := fun point =>
    scalarCoordinatePairingRe
      (covariantDerivative point derivativeDirection) direction
  have leftDifferentiable : DifferentiableAt ℝ left 0 := by
    let pairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap direction
    exact pairing.differentiableAt.comp 0
      (differentiable derivativeDirection)
  have rightDifferentiable : DifferentiableAt ℝ right 0 := by
    let pairing :=
      scalarCoordinatePairingReBilinear.toContinuousBilinearMap.flip direction
    exact pairing.differentiableAt.comp 0
      (differentiable derivativeDirection)
  let combined : BasePoint → ℝ := left + right
  have combinedDifferentiable : DifferentiableAt ℝ combined 0 :=
    leftDifferentiable.add rightDifferentiable
  have combinedDerivative :
      fderiv ℝ combined 0 =
        fderiv ℝ left 0 + fderiv ℝ right 0 := by
    unfold combined
    change
      fderiv ℝ (fun point => left point + right point) 0 =
        fderiv ℝ left 0 + fderiv ℝ right 0
    exact fderiv_fun_add leftDifferentiable rightDifferentiable
  rw [show
    biradialScalarDifferentialMomentumNormalForm a b covariantDerivative
        direction derivativeDirection =
      fun point =>
        ((1 / 2 : ℝ) *
          biradialScalarMomentumWeight a b derivativeDirection) *
            combined point by
    funext point
    rfl]
  unfold fieldDirectionalDerivative
  rw [fderiv_const_mul
      combinedDifferentiable
      ((1 / 2 : ℝ) *
        biradialScalarMomentumWeight a b derivativeDirection),
    combinedDerivative]
  simp only [smul_apply, add_apply, smul_eq_mul]
  change
    ((1 / 2 : ℝ) *
        biradialScalarMomentumWeight a b derivativeDirection) *
      (fieldDirectionalDerivative left 0 derivativeDirection +
        fieldDirectionalDerivative right 0 derivativeDirection) =
      0
  rw [show
      fieldDirectionalDerivative left 0 derivativeDirection =
        scalarCoordinatePairingRe direction
          (fieldDirectionalDerivative
            (fun point =>
              covariantDerivative point derivativeDirection)
            0 derivativeDirection) by
      exact scalarPairingLeft_directionalDerivative covariantDerivative
        differentiable direction derivativeDirection derivativeDirection,
    show
      fieldDirectionalDerivative right 0 derivativeDirection =
        scalarCoordinatePairingRe
          (fieldDirectionalDerivative
            (fun point =>
              covariantDerivative point derivativeDirection)
            0 derivativeDirection)
          direction by
      exact scalarPairingRight_directionalDerivative covariantDerivative
        differentiable direction derivativeDirection derivativeDirection,
    diagonalDerivativeZero]
  simp [scalarCoordinatePairingRe]

/-- On a positive constant biradial coframe, the actual scalar differential
momentum divergence vanishes when each same-direction first derivative of
the scalar covariant derivative vanishes at the origin. -/
theorem scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (coframe_eq :
      configuration.coframe = fun _ => biradialCoframe a b)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point =>
            holonomicScalarCovariantDerivative configuration point
              formDirection)
          0)
    (diagonalDerivativeZero :
      ∀ formDirection,
        fieldDirectionalDerivative
            (fun point =>
              holonomicScalarCovariantDerivative configuration point
                formDirection)
            0 formDirection =
          0)
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence source configuration direction 0 =
      0 := by
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_eq_zero
  intro derivativeDirection _
  rw [scalarDifferentialMomentum_eq_biradialNormalForm source configuration
    ha hb coframe_eq direction derivativeDirection]
  exact
    biradialScalarDifferentialMomentumNormalForm_diagonalDerivative_eq_zero
      a b (holonomicScalarCovariantDerivative configuration)
      differentiable diagonalDerivativeZero direction derivativeDirection

/-! ## Algebraic and complete scalar origin reduction -/

private theorem scalarKineticAlgebraic_origin_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (covariantDerivativeOriginZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (direction : ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source 0 0
        (toContinuumPointField configuration 0)
        (holonomicScalarVariationAlgebraicDirection
          configuration direction 0) =
      0 := by
  have covariantDerivativeZero :
      (toContinuumPointField configuration 0).scalarCovariantDerivative = 0 := by
    funext formDirection
    exact covariantDerivativeOriginZero formDirection
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  rw [covariantDerivativeZero]
  simp [scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]

private theorem scalarPotential_origin_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates source)
    (direction : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation source
        (toContinuumPointField configuration 0) direction = 0 := by
  unfold scalarPotentialFirstVariation
  change
    2 * scalarCoordinatePairingRe
        (configuration.scalar 0 -
          sourceGeneratedVacuumCoordinates source)
        direction =
      0
  rw [scalarOrigin]
  simp [scalarCoordinatePairingRe]

private theorem scalarYukawa_origin_eq_zero
    (configuration : StageNineHolonomicConfiguration)
    (matterOrigin : configuration.matter 0 = 0)
    (direction : ScalarCoordinateCarrier) :
    scalarYukawaFirstVariationDensity
        (toContinuumPointField configuration 0) direction = 0 := by
  unfold scalarYukawaFirstVariationDensity scalarYukawaVariationVector
  change
    (configuration.conjugateMatter 0
      (chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm direction)
        (configuration.matter 0))).re =
      0
  rw [matterOrigin]
  simp [chiralExteriorYukawaAction]

theorem scalarAlgebraicDirectionalCoefficient_origin_eq_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (covariantDerivativeOriginZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates source)
    (matterOrigin : configuration.matter 0 = 0)
    (direction : ScalarCoordinateCarrier) :
    scalarAlgebraicDirectionalCoefficient source configuration direction 0 =
      0 := by
  unfold scalarAlgebraicDirectionalCoefficient
  rw [scalarKineticAlgebraic_origin_eq_zero source configuration
      covariantDerivativeOriginZero direction,
    scalarPotential_origin_eq_zero source configuration scalarOrigin direction,
    scalarYukawa_origin_eq_zero configuration matterOrigin direction]
  ring

/-- Complete actual scalar origin equation on a positive constant biradial
coframe.  Every premise is a primitive field identity or a local first-jet
property; no equation or residual value is supplied. -/
theorem scalarEulerLagrangeDirectionalCoefficient_origin_eq_zero_of_biradial
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (coframe_eq :
      configuration.coframe = fun _ => biradialCoframe a b)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point =>
            holonomicScalarCovariantDerivative configuration point
              formDirection)
          0)
    (covariantDerivativeOriginZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (diagonalDerivativeZero :
      ∀ formDirection,
        fieldDirectionalDerivative
            (fun point =>
              holonomicScalarCovariantDerivative configuration point
                formDirection)
            0 formDirection =
          0)
    (scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates source)
    (matterOrigin : configuration.matter 0 = 0)
    (direction : ScalarCoordinateCarrier) :
    scalarEulerLagrangeDirectionalCoefficient source configuration direction
        0 =
      0 := by
  unfold scalarEulerLagrangeDirectionalCoefficient
  rw [scalarAlgebraicDirectionalCoefficient_origin_eq_zero source
      configuration covariantDerivativeOriginZero scalarOrigin matterOrigin
      direction,
    scalarDifferentialMomentumDivergence_origin_eq_zero_of_biradial source
      configuration ha hb coframe_eq differentiable
      diagonalDerivativeZero direction]
  ring

theorem scalarEulerLagrange_origin_eq_zero_of_biradial
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (coframe_eq :
      configuration.coframe = fun _ => biradialCoframe a b)
    (differentiable :
      ∀ formDirection,
        DifferentiableAt ℝ
          (fun point =>
            holonomicScalarCovariantDerivative configuration point
              formDirection)
          0)
    (covariantDerivativeOriginZero :
      ∀ formDirection,
        holonomicScalarCovariantDerivative configuration 0 formDirection = 0)
    (diagonalDerivativeZero :
      ∀ formDirection,
        fieldDirectionalDerivative
            (fun point =>
              holonomicScalarCovariantDerivative configuration point
                formDirection)
            0 formDirection =
          0)
    (scalarOrigin :
      configuration.scalar 0 =
        sourceGeneratedVacuumCoordinates source)
    (matterOrigin : configuration.matter 0 = 0) :
    (fun direction =>
      scalarEulerLagrangeDirectionalCoefficient source configuration direction
        0) =
      0 := by
  funext direction
  exact
    scalarEulerLagrangeDirectionalCoefficient_origin_eq_zero_of_biradial
      source configuration ha hb coframe_eq differentiable
      covariantDerivativeOriginZero diagonalDerivativeZero scalarOrigin
      matterOrigin direction

end

end SaturationMonoid.PhysicsCore.StageNineBiradialScalarOriginResponse

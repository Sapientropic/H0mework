import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation
import H0mework.Physics.GaugeAction.P286BracketCalculus

/-!
# S9-C3f6a: actual infinitesimal P286 gauge transformation

This module opens the active local-gauge mouth needed by the later Ward
identity.  A compactly supported smooth Lie-algebra parameter generates the
primitive connection direction

`delta A_mu = [epsilon, A_mu] - partial_mu epsilon`.

The resulting linear curvature variation is proved, from the actual
connection calculus, to be `[epsilon, F_mu_nu]`.  Curvature covariance is not
accepted as a field or certificate.  No equation, current, torque, Ward,
stationarity, or conservation premise is used here.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286InfinitesimalGaugeTransformation

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286BracketCalculus
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

abbrev P286InfinitesimalGaugeParameter :=
  CompactlySupportedSmoothVariation P286CoordinateCarrier

@[simp] theorem coordinateBracket_zero_left
    (residual : P286CoordinateCarrier) :
    coordinateBracket 0 residual = 0 := by
  unfold coordinateBracket
  simp [SU7MotherGaugeTheory.p286LieBracket,
    SU7MotherGaugeTheory.suLieBracket]

@[simp] theorem coordinateBracket_zero_right
    (residual : P286CoordinateCarrier) :
    coordinateBracket residual 0 = 0 := by
  unfold coordinateBracket
  simp [SU7MotherGaugeTheory.p286LieBracket,
    SU7MotherGaugeTheory.suLieBracket]

theorem p286CoordinateLieBracket_eq_coordinateBracket
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket first second = coordinateBracket first second :=
  rfl

def p286GaugeParameterDerivative
    (gaugeParameter : BasePoint → P286CoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative gaugeParameter point direction

def p286GaugeParameterSecondDerivative
    (gaugeParameter : BasePoint → P286CoordinateCarrier)
    (point : BasePoint) (outer inner : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
    (fun candidate =>
      p286GaugeParameterDerivative gaugeParameter candidate inner)
    point outer

theorem p286GaugeParameterDerivative_contDiff
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeParameterDerivative gaugeParameter point direction := by
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ gaugeParameter) :=
    gaugeParameter.smooth.fderiv_right (m := ∞) (by simp)
  simpa [p286GaugeParameterDerivative, fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        coordinateDirection direction)

theorem p286GaugeParameterSecondDerivative_comm
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) (first second : LorentzianIndex) :
    p286GaugeParameterSecondDerivative gaugeParameter point first second =
      p286GaugeParameterSecondDerivative gaugeParameter point second first := by
  unfold p286GaugeParameterSecondDerivative p286GaugeParameterDerivative
  exact mixedFieldDirectionalDerivative_comm gaugeParameter
    gaugeParameter.smooth point second first

theorem holonomicP286GaugeConnectionCoordinate_contDiff_active
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      holonomicP286GaugeConnectionCoordinate configuration point direction := by
  exact smooth.2.2.2.2.1 direction

theorem p286GaugeConnectionCoordinateDerivative_contDiff_active
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      p286GaugeConnectionCoordinateDerivative configuration point
        derivativeDirection formDirection := by
  have derivativeSmooth : ContDiff ℝ ∞
      (fderiv ℝ fun point =>
        holonomicP286GaugeConnectionCoordinate configuration point
          formDirection) :=
    (holonomicP286GaugeConnectionCoordinate_contDiff_active configuration
      smooth formDirection).fderiv_right (m := ∞) (by simp)
  simpa [p286GaugeConnectionCoordinateDerivative,
    fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        coordinateDirection derivativeDirection)

theorem fieldDirectionalDerivative_sub_of_contDiff_active
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => first candidate - second candidate) point direction =
      fieldDirectionalDerivative first point direction -
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

/-- The actual active connection direction generated by one local Lie
parameter. -/
def p286InfinitesimalGaugeConnectionDirection
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : BasePoint → P286CoordinateCarrier)
    (point : BasePoint) : P286GaugeOneForm :=
  fun direction =>
    coordinateBracket (gaugeParameter point)
        (holonomicP286GaugeConnectionCoordinate configuration point direction) -
      p286GaugeParameterDerivative gaugeParameter point direction

/-- Adjoint covariant derivative of the active Lie parameter in the actual
P286 coordinate chart. -/
def p286AdjointCovariantParameterDerivative
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : BasePoint → P286CoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    P286CoordinateCarrier :=
  p286GaugeParameterDerivative gaugeParameter point direction +
    coordinateBracket
      (holonomicP286GaugeConnectionCoordinate configuration point direction)
      (gaugeParameter point)

theorem p286InfinitesimalGaugeConnectionDirection_eq_neg_covariantDerivative
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : BasePoint → P286CoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) :
    p286InfinitesimalGaugeConnectionDirection configuration gaugeParameter
        point direction =
      -p286AdjointCovariantParameterDerivative configuration gaugeParameter
        point direction := by
  unfold p286InfinitesimalGaugeConnectionDirection
    p286AdjointCovariantParameterDerivative
  rw [coordinateBracket_skew (gaugeParameter point)
    (holonomicP286GaugeConnectionCoordinate configuration point direction)]
  abel

theorem p286InfinitesimalGaugeConnectionDirection_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    ContDiff ℝ ∞
      (p286InfinitesimalGaugeConnectionDirection configuration
        gaugeParameter) := by
  apply contDiff_pi'
  intro direction
  exact (coordinateBracket_contDiff gaugeParameter
      (fun point => holonomicP286GaugeConnectionCoordinate configuration point
        direction)
      gaugeParameter.smooth
      (holonomicP286GaugeConnectionCoordinate_contDiff_active configuration
        smooth direction)).sub
    (p286GaugeParameterDerivative_contDiff gaugeParameter direction)

theorem p286InfinitesimalGaugeConnectionDirection_compactSupport
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasCompactSupport
      (p286InfinitesimalGaugeConnectionDirection configuration
        gaugeParameter) := by
  have parameterEventually := gaugeParameter.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at parameterEventually
  have derivativeEventually : ∀ direction : LorentzianIndex,
      ∀ᶠ point in Filter.coclosedCompact BasePoint,
        p286GaugeParameterDerivative gaugeParameter point direction = 0 := by
    intro direction
    have actual := compactVariation_directionalDerivative_compact
      gaugeParameter direction
    rw [hasCompactSupport_iff_eventuallyEq] at actual
    change ∀ᶠ point in Filter.coclosedCompact BasePoint,
      fderiv ℝ gaugeParameter point (coordinateDirection direction) = 0
    exact actual
  have everyDerivativeEventually :=
    Filter.eventually_all.2 derivativeEventually
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards [parameterEventually, everyDerivativeEventually] with
    point parameterZero derivativeZero
  have parameterZero' : gaugeParameter point = 0 := by
    simpa using parameterZero
  funext direction
  simp [p286InfinitesimalGaugeConnectionDirection, parameterZero',
    derivativeZero direction]

/-- The generated active direction packaged in the existing primitive
connection-variation carrier. -/
def p286InfinitesimalGaugeConnectionVariation
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    CompactlySupportedSmoothVariation P286GaugeOneForm where
  toFun := p286InfinitesimalGaugeConnectionDirection configuration
    gaugeParameter
  smooth := p286InfinitesimalGaugeConnectionDirection_contDiff
    configuration smooth gaugeParameter
  compactSupport := p286InfinitesimalGaugeConnectionDirection_compactSupport
    configuration gaugeParameter

@[simp] theorem p286InfinitesimalGaugeConnectionVariation_apply
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) (direction : LorentzianIndex) :
    p286InfinitesimalGaugeConnectionVariation configuration smooth
        gaugeParameter point direction =
      p286InfinitesimalGaugeConnectionDirection configuration gaugeParameter
        point direction :=
  rfl

theorem p286InfinitesimalGaugeConnectionDerivative_expansion
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeVariationCoordinateDerivative
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter)
        point derivativeDirection formDirection =
      coordinateBracket
          (p286GaugeParameterDerivative gaugeParameter point
            derivativeDirection)
          (holonomicP286GaugeConnectionCoordinate configuration point
            formDirection) +
        coordinateBracket (gaugeParameter point)
          (p286GaugeConnectionCoordinateDerivative configuration point
            derivativeDirection formDirection) -
        p286GaugeParameterSecondDerivative gaugeParameter point
          derivativeDirection formDirection := by
  have parameterSmooth := gaugeParameter.smooth
  have connectionSmooth :=
    holonomicP286GaugeConnectionCoordinate_contDiff_active configuration smooth
      formDirection
  have bracketSmooth := coordinateBracket_contDiff gaugeParameter
    (fun candidate =>
      holonomicP286GaugeConnectionCoordinate configuration candidate
        formDirection)
    parameterSmooth connectionSmooth
  have derivativeSmooth :=
    p286GaugeParameterDerivative_contDiff gaugeParameter formDirection
  unfold p286GaugeVariationCoordinateDerivative
    p286InfinitesimalGaugeConnectionVariation
    p286InfinitesimalGaugeConnectionDirection
  rw [fieldDirectionalDerivative_sub_of_contDiff_active
    (fun candidate => coordinateBracket (gaugeParameter candidate)
      (holonomicP286GaugeConnectionCoordinate configuration candidate
        formDirection))
    (fun candidate =>
      p286GaugeParameterDerivative gaugeParameter candidate formDirection)
    bracketSmooth derivativeSmooth]
  rw [fieldDirectionalDerivative_coordinateBracket gaugeParameter
    (fun candidate =>
      holonomicP286GaugeConnectionCoordinate configuration candidate
        formDirection)
    parameterSmooth connectionSmooth]
  rfl

/-- The commutator acts as a derivation on itself; this is a Jacobi theorem,
not an assumed representation law. -/
theorem coordinateBracket_derivation_left
    (parameter first second : P286CoordinateCarrier) :
    coordinateBracket parameter (coordinateBracket first second) =
      coordinateBracket (coordinateBracket parameter first) second +
        coordinateBracket first (coordinateBracket parameter second) := by
  have jacobi := coordinateBracket_jacobi parameter first second
  calc
    coordinateBracket parameter (coordinateBracket first second) =
        -(coordinateBracket first (coordinateBracket second parameter) +
          coordinateBracket second (coordinateBracket parameter first)) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc] using jacobi
    _ = coordinateBracket (coordinateBracket parameter first) second +
        coordinateBracket first (coordinateBracket parameter second) := by
      rw [coordinateBracket_skew second parameter,
        coordinateBracket_neg_right,
        coordinateBracket_skew second (coordinateBracket parameter first)]
      abel

/-- The curvature response of the actual primitive active connection
direction is the adjoint response of the actual curvature. -/
theorem p286InfinitesimalGaugeCurvatureVariation_eq_adjoint
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) (pair : Fin 6) :
    p286GaugeConnectionLinearCurvatureVariation configuration
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter)
        point pair =
      coordinateBracket (gaugeParameter point)
        (holonomicP286GaugeCurvatureCoordinate configuration point pair) := by
  rw [show p286GaugeConnectionLinearCurvatureVariation configuration
        (p286InfinitesimalGaugeConnectionVariation configuration smooth
          gaugeParameter) point pair =
      p286GaugeVariationCoordinateDerivative
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          point (pairFirst pair) (pairSecond pair) -
        p286GaugeVariationCoordinateDerivative
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          point (pairSecond pair) (pairFirst pair) +
        coordinateBracket
          (p286InfinitesimalGaugeConnectionDirection configuration
            gaugeParameter point (pairFirst pair))
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairSecond pair)) +
        coordinateBracket
          (holonomicP286GaugeConnectionCoordinate configuration point
            (pairFirst pair))
          (p286InfinitesimalGaugeConnectionDirection configuration
            gaugeParameter point (pairSecond pair)) by
    rfl]
  rw [p286InfinitesimalGaugeConnectionDerivative_expansion,
    p286InfinitesimalGaugeConnectionDerivative_expansion]
  rw [holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket]
  rw [p286CoordinateLieBracket_eq_coordinateBracket]
  unfold p286InfinitesimalGaugeConnectionDirection
  simp only [coordinateBracket_sub_left, coordinateBracket_sub_right,
    coordinateBracket_add_right]
  rw [p286GaugeParameterSecondDerivative_comm gaugeParameter point
    (pairFirst pair) (pairSecond pair)]
  rw [coordinateBracket_skew
    (p286GaugeParameterDerivative gaugeParameter point (pairSecond pair))
    (holonomicP286GaugeConnectionCoordinate configuration point
      (pairFirst pair))]
  rw [coordinateBracket_derivation_left (gaugeParameter point)
    (holonomicP286GaugeConnectionCoordinate configuration point
      (pairFirst pair))
    (holonomicP286GaugeConnectionCoordinate configuration point
      (pairSecond pair))]
  abel

/-- First-order readout from the existing exact polynomial expansion of the
same primitive varied connection. -/
theorem holonomicP286GaugeCurvature_expansion_with_adjoint_linearTerm
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        (varyP286GaugeConnectionCoordinate configuration
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          parameter)
        point =
      holonomicP286GaugeCurvatureCoordinate configuration point +
        parameter • (fun pair =>
          coordinateBracket (gaugeParameter point)
            (holonomicP286GaugeCurvatureCoordinate configuration point pair)) +
        parameter ^ 2 •
          p286GaugeConnectionQuadraticCurvatureVariation
            (p286InfinitesimalGaugeConnectionVariation configuration smooth
              gaugeParameter)
            point := by
  rw [holonomicP286GaugeCurvatureCoordinate_expansion configuration smooth]
  have linearTerm :
      p286GaugeConnectionLinearCurvatureVariation configuration
          (p286InfinitesimalGaugeConnectionVariation configuration smooth
            gaugeParameter)
          point =
        fun pair => coordinateBracket (gaugeParameter point)
          (holonomicP286GaugeCurvatureCoordinate configuration point pair) := by
    funext pair
    exact p286InfinitesimalGaugeCurvatureVariation_eq_adjoint configuration
      smooth gaugeParameter point pair
  rw [linearTerm]

end

end SaturationMonoid.PhysicsCore.StageNineP286InfinitesimalGaugeTransformation

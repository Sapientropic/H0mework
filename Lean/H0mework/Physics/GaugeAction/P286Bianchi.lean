import H0mework.Physics.GaugeAction.P286BracketCalculus

/-!
# S9-C3f1: actual P286 differential Bianchi identity

The ordered curvature and its covariant exterior derivative below are
generated from the same primitive smooth P286 connection stored by
`StageNineHolonomicConfiguration`.  The proof explicitly uses mixed-second
Fréchet derivative symmetry, the directional Leibniz rule for the actual
matrix commutator, and its Jacobi identity.

This is an off-shell kinematic theorem.  It consumes no curvature, Bianchi,
stationarity, field-equation, current, or conservation receipt.  The ordered
curvature is also bridged back to the existing canonical `Fin 6` curvature
readout, so the new three-index calculus cannot be hand-filled independently.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286Bianchi

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineP286BracketCalculus
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- Actual primitive P286 connection in the already chosen faithful finite
coordinate chart. -/
def connectionCoordinate
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) :
    P286CoordinateCarrier :=
  p286CoordinateEquiv (configuration.gaugeConnection point direction)

/-- Actual coordinate-direction derivative of one primitive connection
component. -/
def connectionCoordinateDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
    (fun candidate => connectionCoordinate configuration candidate formDirection)
    point derivativeDirection

/-- Ordered `F_{μν} = ∂μ Aν - ∂ν Aμ + [Aμ,Aν]`.  Unlike the
canonical `Fin 6` readout, this is defined for every ordered pair needed by
the cyclic Bianchi sum. -/
def orderedCurvature
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  connectionCoordinateDerivative configuration point first second -
    connectionCoordinateDerivative configuration point second first +
    coordinateBracket
      (connectionCoordinate configuration point first)
      (connectionCoordinate configuration point second)

def orderedCurvatureDirectionalDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
    (fun candidate => orderedCurvature configuration candidate first second)
    point derivativeDirection

/-- Actual adjoint covariant derivative of the ordered curvature. -/
def covariantCurvatureDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  orderedCurvatureDirectionalDerivative configuration point
      derivativeDirection first second +
    coordinateBracket
      (connectionCoordinate configuration point derivativeDirection)
      (orderedCurvature configuration point first second)

theorem connectionCoordinate_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      connectionCoordinate configuration point direction := by
  exact smooth.2.2.2.2.1 direction

theorem connectionCoordinateDerivative_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      connectionCoordinateDerivative configuration point
        derivativeDirection formDirection := by
  have derivativeSmooth : ContDiff ℝ ∞
      (fderiv ℝ fun point =>
        connectionCoordinate configuration point formDirection) :=
    (connectionCoordinate_contDiff configuration smooth formDirection).fderiv_right
      (m := ∞) (by simp)
  simpa [connectionCoordinateDerivative, fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        coordinateDirection derivativeDirection)

theorem connectionCoordinateDerivative_mixed_comm
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (formDirection first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          connectionCoordinateDerivative configuration candidate
            first formDirection)
        point second =
      fieldDirectionalDerivative
        (fun candidate =>
          connectionCoordinateDerivative configuration candidate
            second formDirection)
        point first := by
  unfold connectionCoordinateDerivative
  exact mixedFieldDirectionalDerivative_comm
    (fun candidate => connectionCoordinate configuration candidate formDirection)
    (connectionCoordinate_contDiff configuration smooth formDirection)
    point first second

theorem orderedCurvature_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (first second : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      orderedCurvature configuration point first second := by
  have firstDerivative := connectionCoordinateDerivative_contDiff
    configuration smooth first second
  have secondDerivative := connectionCoordinateDerivative_contDiff
    configuration smooth second first
  have bracketSmooth := coordinateBracket_contDiff
    (fun point => connectionCoordinate configuration point first)
    (fun point => connectionCoordinate configuration point second)
    (connectionCoordinate_contDiff configuration smooth first)
    (connectionCoordinate_contDiff configuration smooth second)
  exact (firstDerivative.sub secondDerivative).add bracketSmooth

theorem fieldDirectionalDerivative_add_of_contDiff
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => first candidate + second candidate)
        point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

theorem fieldDirectionalDerivative_sub_of_contDiff
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => first candidate - second candidate)
        point direction =
      fieldDirectionalDerivative first point direction -
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

def orderedCurvatureDerivativeExpansion
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) :
    P286CoordinateCarrier :=
  fieldDirectionalDerivative
      (fun candidate =>
        connectionCoordinateDerivative configuration candidate first second)
      point derivativeDirection -
    fieldDirectionalDerivative
      (fun candidate =>
        connectionCoordinateDerivative configuration candidate second first)
      point derivativeDirection +
    coordinateBracket
      (connectionCoordinateDerivative configuration point
        derivativeDirection first)
      (connectionCoordinate configuration point second) +
    coordinateBracket
      (connectionCoordinate configuration point first)
      (connectionCoordinateDerivative configuration point
        derivativeDirection second)

theorem orderedCurvatureDirectionalDerivative_eq_expansion
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) :
    orderedCurvatureDirectionalDerivative configuration point
        derivativeDirection first second =
      orderedCurvatureDerivativeExpansion configuration point
        derivativeDirection first second := by
  have firstDerivativeSmooth := connectionCoordinateDerivative_contDiff
    configuration smooth first second
  have secondDerivativeSmooth := connectionCoordinateDerivative_contDiff
    configuration smooth second first
  have firstConnectionSmooth := connectionCoordinate_contDiff
    configuration smooth first
  have secondConnectionSmooth := connectionCoordinate_contDiff
    configuration smooth second
  have bracketSmooth := coordinateBracket_contDiff
    (fun candidate => connectionCoordinate configuration candidate first)
    (fun candidate => connectionCoordinate configuration candidate second)
    firstConnectionSmooth secondConnectionSmooth
  unfold orderedCurvatureDirectionalDerivative orderedCurvature
  rw [fieldDirectionalDerivative_add_of_contDiff
    (fun candidate =>
      connectionCoordinateDerivative configuration candidate first second -
        connectionCoordinateDerivative configuration candidate second first)
    (fun candidate => coordinateBracket
      (connectionCoordinate configuration candidate first)
      (connectionCoordinate configuration candidate second))
    (firstDerivativeSmooth.sub secondDerivativeSmooth) bracketSmooth]
  rw [fieldDirectionalDerivative_sub_of_contDiff
    (fun candidate =>
      connectionCoordinateDerivative configuration candidate first second)
    (fun candidate =>
      connectionCoordinateDerivative configuration candidate second first)
    firstDerivativeSmooth secondDerivativeSmooth]
  rw [fieldDirectionalDerivative_coordinateBracket
    (fun candidate => connectionCoordinate configuration candidate first)
    (fun candidate => connectionCoordinate configuration candidate second)
    firstConnectionSmooth secondConnectionSmooth]
  unfold orderedCurvatureDerivativeExpansion connectionCoordinateDerivative
  abel

/-- The ordered curvature is not a new slot: on every canonical oriented
pair it is exactly the existing curvature generated by
`StageNineHolonomicField`. -/
theorem orderedCurvature_canonicalPair_eq_holonomic
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (pair : Fin 6) :
    orderedCurvature configuration point
        (pairFirst pair) (pairSecond pair) =
      p286CoordinateEquiv (holonomicGaugeCurvature configuration point pair) := by
  unfold orderedCurvature connectionCoordinateDerivative
    connectionCoordinate holonomicGaugeCurvature p286ConnectionDerivative
    fieldDirectionalDerivative coordinateBracket
  simp only [map_add, map_sub, p286CoordinateEquiv.apply_symm_apply]
  simp

/-- Off-shell differential Bianchi identity for the actual primitive smooth
P286 connection. -/
theorem holonomicP286GaugeCurvature_bianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantCurvatureDerivative configuration point first second third +
        covariantCurvatureDerivative configuration point second third first +
        covariantCurvatureDerivative configuration point third first second = 0 := by
  rw [show covariantCurvatureDerivative configuration point first second third =
      orderedCurvatureDerivativeExpansion configuration point first second third +
        coordinateBracket (connectionCoordinate configuration point first)
          (orderedCurvature configuration point second third) by
    rw [covariantCurvatureDerivative,
      orderedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  rw [show covariantCurvatureDerivative configuration point second third first =
      orderedCurvatureDerivativeExpansion configuration point second third first +
        coordinateBracket (connectionCoordinate configuration point second)
          (orderedCurvature configuration point third first) by
    rw [covariantCurvatureDerivative,
      orderedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  rw [show covariantCurvatureDerivative configuration point third first second =
      orderedCurvatureDerivativeExpansion configuration point third first second +
        coordinateBracket (connectionCoordinate configuration point third)
          (orderedCurvature configuration point first second) by
    rw [covariantCurvatureDerivative,
      orderedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  unfold orderedCurvatureDerivativeExpansion orderedCurvature
  simp only [coordinateBracket_add_right, coordinateBracket_sub_right]
  rw [connectionCoordinateDerivative_mixed_comm
    configuration smooth point third second first]
  rw [connectionCoordinateDerivative_mixed_comm
    configuration smooth point second third first]
  rw [connectionCoordinateDerivative_mixed_comm
    configuration smooth point first third second]
  rw [coordinateBracket_skew
    (connectionCoordinateDerivative configuration point first second)
    (connectionCoordinate configuration point third)]
  rw [coordinateBracket_skew
    (connectionCoordinateDerivative configuration point second third)
    (connectionCoordinate configuration point first)]
  rw [coordinateBracket_skew
    (connectionCoordinateDerivative configuration point third first)
    (connectionCoordinate configuration point second)]
  calc
    _ = coordinateBracket (connectionCoordinate configuration point first)
          (coordinateBracket
            (connectionCoordinate configuration point second)
            (connectionCoordinate configuration point third)) +
        coordinateBracket (connectionCoordinate configuration point second)
          (coordinateBracket
            (connectionCoordinate configuration point third)
            (connectionCoordinate configuration point first)) +
        coordinateBracket (connectionCoordinate configuration point third)
          (coordinateBracket
            (connectionCoordinate configuration point first)
            (connectionCoordinate configuration point second)) := by
      abel
    _ = 0 := coordinateBracket_jacobi
      (connectionCoordinate configuration point first)
      (connectionCoordinate configuration point second)
      (connectionCoordinate configuration point third)

end

end SaturationMonoid.PhysicsCore.StageNineP286Bianchi

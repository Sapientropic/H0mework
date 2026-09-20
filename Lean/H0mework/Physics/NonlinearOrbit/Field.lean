import H0mework.Physics.NonlinearOrbit.Adjoint

/-! Full-mother Q is read from the orbit's actual A, F and D F. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics SU7MotherLieAlgebra SU7MotherGaugeTheory
open Set Filter
open scoped Topology

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance
local instance : NormedAddCommGroup P286CoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : P286CoordinateIndex => ℝ)
local instance : NormedSpace ℝ P286CoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : P286CoordinateIndex => ℝ)

variable {initial : PhaseSpace} {initialTime : ℝ}

def LocalOrbit.curvatureCoordinates (flow : LocalOrbit initial initialTime) (point : BasePoint) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (holonomicGaugeCurvature flow.configuration point pair)

def LocalOrbit.curvatureCurve (flow : LocalOrbit initial initialTime) (time : ℝ) : P286GaugeTwoForm :=
  flow.velocity time • electricCoordinates - (flow.amplitude time)^2 • magneticCoordinates

theorem LocalOrbit.curvatureCurve_derivative (flow : LocalOrbit initial initialTime) (time : ℝ)
    (inside : time ∈ flow.window) :
    HasDerivAt flow.curvatureCurve (flow.acceleration time • electricCoordinates -
      (2*flow.amplitude time*flow.velocity time) • magneticCoordinates) time := by
  have electric := (flow.velocity_derivative time inside).smul_const electricCoordinates
  have magnetic := ((flow.amplitude_derivative time inside).pow 2).smul_const magneticCoordinates
  unfold LocalOrbit.curvatureCurve
  convert electric.sub magnetic using 1 <;> first | rfl | simp

theorem LocalOrbit.curvatureSpatial_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (axis : Fin 3) :
    fieldDirectionalDerivative flow.curvatureCoordinates point axis.succ = 0 := by
  have localValues : flow.curvatureCoordinates =ᶠ[𝓝 point] fun p => flow.curvatureCurve (p 0) := by
    filter_upwards [flow.time_neighborhood point inside] with p hp
    funext pair
    unfold LocalOrbit.curvatureCoordinates
    rw [flow.curvature p hp]
    fin_cases pair <;> simp [LocalOrbit.curvatureCurve, radialCurvature, electricCoordinates,
      magneticCoordinates, map_smul]
  have composed := (flow.curvatureCurve_derivative (point 0) inside).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun p : BasePoint => flow.curvatureCurve (p 0)) _ point at composed
  unfold fieldDirectionalDerivative
  rw [localValues.fderiv_eq, composed.fderiv]
  change (coordinateDirection axis.succ) 0 • (flow.acceleration (point 0) • electricCoordinates -
    (2*flow.amplitude (point 0)*flow.velocity (point 0)) • magneticCoordinates) = 0
  simp [coordinateDirection, Fin.succ_ne_zero]

def LocalOrbit.motherConnection (flow : LocalOrbit initial initialTime) (point : BasePoint) (axis : Fin 3) : Helicity.MotherMatrix :=
  p286LieBlockEmbed (flow.configuration.gaugeConnection point axis.succ)
def LocalOrbit.motherMagnetic (flow : LocalOrbit initial initialTime) (point : BasePoint) (axis : Fin 3) : Helicity.MotherMatrix :=
  p286LieBlockEmbed (holonomicGaugeCurvature flow.configuration point (magneticPair axis))
def LocalOrbit.motherDerivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (direction axis : Fin 3) : Helicity.MotherMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm (pointwiseP286GaugeTwoFormCovariantDerivative
    (holonomicP286GaugeConnectionCoordinate flow.configuration point) (flow.curvatureCoordinates point)
    (fieldDirectionalDerivative flow.curvatureCoordinates point) direction.succ (magneticPair axis)))

theorem LocalOrbit.motherDerivative_bracket (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (direction axis : Fin 3) :
    flow.motherDerivative point direction axis = Helicity.bracket (flow.motherConnection point direction) (flow.motherMagnetic point axis) := by
  unfold LocalOrbit.motherDerivative pointwiseP286GaugeTwoFormCovariantDerivative
  rw [flow.curvatureSpatial_zero point inside, zero_add]
  simp only [p286GaugeTwoFormAdjoint, p286CoordinateLieBracket, LocalOrbit.curvatureCoordinates,
    holonomicP286GaugeConnectionCoordinate, LinearEquiv.symm_apply_apply]
  rw [p286LieBlockEmbed_bracket]
  rfl

def LocalOrbit.motherCurl (flow : LocalOrbit initial initialTime) (point : BasePoint) : Fin 3 → Helicity.MotherMatrix :=
  ![flow.motherDerivative point 1 2-flow.motherDerivative point 2 1,
    flow.motherDerivative point 2 0-flow.motherDerivative point 0 2,
    flow.motherDerivative point 0 1-flow.motherDerivative point 1 0]

def LocalOrbit.fieldValue (flow : LocalOrbit initial initialTime) (point : BasePoint) : ℝ :=
  (∑ axis : Fin 3, (flow.motherMagnetic point axis*flow.motherCurl point axis).trace).re

def LocalOrbit.helicity (flow : LocalOrbit initial initialTime) (time : ℝ) : ℝ :=
  (MatrixResponse.value (flow.amplitude time • (1 : MatrixResponse.Coefficients))).re

theorem LocalOrbit.fieldValue_helicity (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) : flow.fieldValue point = flow.helicity (point 0) := by
  have curl : flow.motherCurl point = Helicity.bracketCurl (flow.motherConnection point) (flow.motherMagnetic point) := by
    funext axis
    fin_cases axis <;> simp [LocalOrbit.motherCurl, flow.motherDerivative_bracket point inside, Helicity.bracketCurl]
  have connection : MatrixResponse.connection (flow.amplitude (point 0) • (1 : MatrixResponse.Coefficients)) =
      flow.motherConnection point := by
    funext axis
    fin_cases axis <;> simp [MatrixResponse.connection, MatrixResponse.mother, MatrixResponse.color,
      LocalOrbit.motherConnection, LocalOrbit.configuration, radialReadout, radialWrite, gaugePotential]
  have magnetic : MatrixResponse.magnetic (flow.amplitude (point 0) • (1 : MatrixResponse.Coefficients)) =
      flow.motherMagnetic point := by
    funext axis
    rw [MatrixResponse.magnetic_coefficients]
    unfold LocalOrbit.motherMagnetic
    rw [flow.curvature point inside]
    fin_cases axis <;> simp [MatrixResponse.mother, MatrixResponse.color, MatrixResponse.cofactors,
      cross_apply, radialCurvature, magneticPair, pow_two]
  unfold LocalOrbit.fieldValue LocalOrbit.helicity MatrixResponse.value
  rw [curl, connection, magnetic]
  rfl

theorem LocalOrbit.helicity_eq (flow : LocalOrbit initial initialTime) (time : ℝ) :
    flow.helicity time = 3*(flow.amplitude time)^5 := by
  unfold LocalOrbit.helicity
  rw [MatrixResponse.value_scalar, Complex.ofReal_re]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

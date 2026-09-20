import H0mework.Physics.RadialDynamics.Observable

/-! The varying physical Q uses the actual spatial covariant derivative of
the profile curvature, not a reassigned finite-matter response operator. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics SU7MotherLieAlgebra SU7MotherGaugeTheory

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

def responseCurvature (parameter : ℝ) (point : BasePoint) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv
    (holonomicGaugeCurvature (radialWrite (responseProfile parameter)) point pair)

def curvatureCurve (parameter time : ℝ) : P286GaugeTwoForm :=
  responseVelocity parameter time • electricCoordinates -
    (responseProfile parameter time)^2 • magneticCoordinates

theorem responseCurvature_eq (parameter : ℝ) :
    responseCurvature parameter = fun point => curvatureCurve parameter (point 0) := by
  funext point pair
  unfold responseCurvature
  rw [radialWrite_curvature _ _ _ (responseProfile_hasDerivAt parameter (point 0))]
  fin_cases pair <;>
    simp [curvatureCurve, radialCurvature, electricCoordinates, magneticCoordinates, map_smul]

theorem curvatureCurve_hasDerivAt (parameter time : ℝ) :
    HasDerivAt (curvatureCurve parameter)
      ((parameter*impulseAcceleration time) • electricCoordinates -
        (2*responseProfile parameter time*responseVelocity parameter time) • magneticCoordinates) time := by
  unfold curvatureCurve
  have electric := (responseVelocity_hasDerivAt parameter time).smul_const electricCoordinates
  have magnetic := ((responseProfile_hasDerivAt parameter time).pow 2).smul_const magneticCoordinates
  convert electric.sub magnetic using 1 <;> first | rfl | simp

theorem curvature_spatialDerivative_zero (parameter : ℝ) (point : BasePoint) (axis : Fin 3) :
    fieldDirectionalDerivative (responseCurvature parameter) point axis.succ = 0 := by
  have composed := (curvatureCurve_hasDerivAt parameter (point 0)).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun candidate : BasePoint => curvatureCurve parameter (candidate 0)) _ point at composed
  unfold fieldDirectionalDerivative
  rw [responseCurvature_eq, composed.fderiv]
  change (coordinateDirection axis.succ) 0 •
    ((parameter*impulseAcceleration (point 0)) • electricCoordinates -
      (2*responseProfile parameter (point 0)*responseVelocity parameter (point 0)) • magneticCoordinates) = 0
  simp [coordinateDirection, Fin.succ_ne_zero]

def responseCovariantDerivative (parameter : ℝ) (point : BasePoint) (direction axis : Fin 3) : P286LieBlockData :=
  p286CoordinateEquiv.symm (pointwiseP286GaugeTwoFormCovariantDerivative
    (holonomicP286GaugeConnectionCoordinate (radialWrite (responseProfile parameter)) point)
    (responseCurvature parameter point)
    (fieldDirectionalDerivative (responseCurvature parameter) point) direction.succ (magneticPair axis))

def responseMagnetic (parameter : ℝ) (point : BasePoint) (axis : Fin 3) : Helicity.MotherMatrix :=
  p286LieBlockEmbed (holonomicGaugeCurvature (radialWrite (responseProfile parameter)) point (magneticPair axis))

def responseConnection (parameter : ℝ) (point : BasePoint) (axis : Fin 3) : Helicity.MotherMatrix :=
  p286LieBlockEmbed ((radialWrite (responseProfile parameter)).gaugeConnection point axis.succ)

theorem responseCovariantDerivative_bracket (parameter : ℝ) (point : BasePoint) (direction axis : Fin 3) :
    (p286LieBlockEmbed (responseCovariantDerivative parameter point direction axis) : Helicity.MotherMatrix) =
      Helicity.bracket (responseConnection parameter point direction) (responseMagnetic parameter point axis) := by
  unfold responseCovariantDerivative pointwiseP286GaugeTwoFormCovariantDerivative
  rw [curvature_spatialDerivative_zero, zero_add]
  simp only [p286GaugeTwoFormAdjoint, p286CoordinateLieBracket,
    responseCurvature, holonomicP286GaugeConnectionCoordinate, LinearEquiv.symm_apply_apply]
  rw [p286LieBlockEmbed_bracket]
  rfl

def responseCurl (parameter : ℝ) (point : BasePoint) : Fin 3 → P286LieBlockData :=
  ![responseCovariantDerivative parameter point 1 2 - responseCovariantDerivative parameter point 2 1,
    responseCovariantDerivative parameter point 2 0 - responseCovariantDerivative parameter point 0 2,
    responseCovariantDerivative parameter point 0 1 - responseCovariantDerivative parameter point 1 0]

def fieldValue (parameter : ℝ) (point : BasePoint) : ℝ :=
  (∑ axis : Fin 3, (responseMagnetic parameter point axis *
    (p286LieBlockEmbed (responseCurl parameter point axis) : Helicity.MotherMatrix)).trace).re

theorem fieldValue_eq (parameter : ℝ) (point : BasePoint) :
    fieldValue parameter point = physicalValue parameter (point 0) := by
  rw [physicalValue_field]
  have curl (axis : Fin 3) :
      (p286LieBlockEmbed (responseCurl parameter point axis) : Helicity.MotherMatrix) =
        Helicity.bracketCurl (responseConnection parameter point) (responseMagnetic parameter point) axis := by
    fin_cases axis <;>
      simp [responseCurl, p286LieBlockEmbed_sub, responseCovariantDerivative_bracket, Helicity.bracketCurl]
  unfold fieldValue
  simp_rw [curl]
  rfl

theorem fieldValue_response (point : BasePoint) :
    HasDerivAt (fun parameter => fieldValue parameter point) (helicityResponse (point 0)) 0 := by
  simp_rw [fieldValue_eq]
  rw [helicityResponse_eq]
  exact physicalValue_hasDerivAt _

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

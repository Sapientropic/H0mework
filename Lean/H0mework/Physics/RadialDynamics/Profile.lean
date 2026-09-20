import H0mework.Physics.RadialDynamics.EulerJet

/-! The two-jet consumed by the gauge Euler form is realized by the actual
time derivatives of the source constitutive readout. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics SU7MotherLieAlgebra

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

theorem auxiliaryCoordinates_hasDerivAt (profile velocity : ℝ → ℝ) (time acceleration : ℝ)
    (first : HasDerivAt profile (velocity time) time)
    (second : HasDerivAt velocity acceleration time) :
    HasDerivAt (fun t => auxiliaryCoordinates (profile t) (velocity t))
      (auxiliaryJet (profile time) (velocity time) acceleration 0) time := by
  simp_rw [auxiliaryCoordinates_eq]
  have electric := ((first.pow 2).div_const (Stage9C.Material.SpinPair.sourceCoupling *
    Stage9C.Material.SpinPair.lapse)).smul_const electricCoordinates
  have magnetic := ((second.const_mul Stage9C.Material.SpinPair.lapse).div_const
    Stage9C.Material.SpinPair.sourceCoupling).smul_const magneticCoordinates
  convert electric.add magnetic using 1 <;> first | rfl | simp [auxiliaryJet]

theorem radialReadout_auxiliaryDerivative (profile velocity : ℝ → ℝ)
    (first : ∀ time, HasDerivAt profile (velocity time) time)
    (point : BasePoint) (acceleration : ℝ)
    (second : HasDerivAt velocity acceleration (point 0)) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative (radialReadout profile) point direction =
      auxiliaryJet (profile (point 0)) (velocity (point 0)) acceleration direction := by
  have values : holonomicP286GaugeAuxiliaryCoordinate (radialReadout profile) =
      fun candidate => auxiliaryCoordinates (profile (candidate 0)) (velocity (candidate 0)) := by
    funext candidate pair
    exact congrArg (fun form => p286CoordinateEquiv (form pair))
      (radialReadout_auxiliary profile candidate (velocity (candidate 0)) (first _))
  have composed := (auxiliaryCoordinates_hasDerivAt profile velocity (point 0) acceleration
    (first _) second).hasFDerivAt.comp point
      (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun candidate : BasePoint =>
    auxiliaryCoordinates (profile (candidate 0)) (velocity (candidate 0))) _ point at composed
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [values, composed.fderiv]
  change (coordinateDirection direction) 0 •
    auxiliaryJet (profile (point 0)) (velocity (point 0)) acceleration 0 = _
  by_cases same : direction = 0
  · simp [same, coordinateDirection]
  · simp [auxiliaryJet, coordinateDirection, same, Ne.symm same]

theorem radialReadout_exterior (profile velocity : ℝ → ℝ)
    (first : ∀ time, HasDerivAt profile (velocity time) time)
    (point : BasePoint) (acceleration : ℝ)
    (second : HasDerivAt velocity acceleration (point 0)) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (radialReadout profile) point =
      pointwiseP286GaugeTwoFormExteriorCovariantDerivative
        (fun direction => p286CoordinateEquiv (Stage9C.Material.SpinPair.gaugePotential (profile (point 0)) direction))
        (auxiliaryCoordinates (profile (point 0)) (velocity (point 0)))
        (auxiliaryJet (profile (point 0)) (velocity (point 0)) acceleration) := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  congr 1
  · exact funext (fun pair => congrArg (fun form => p286CoordinateEquiv (form pair))
      (radialReadout_auxiliary profile point (velocity (point 0)) (first _)))
  · exact funext (radialReadout_auxiliaryDerivative profile velocity first point acceleration second)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

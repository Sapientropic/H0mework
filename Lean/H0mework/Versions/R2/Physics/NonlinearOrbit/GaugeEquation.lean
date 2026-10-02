import H0mework.Versions.R2.Physics.NonlinearOrbit.Current

/-! The complete original gauge Euler form vanishes on the jointly moving
configuration throughout the generated local interval. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeP286GaugeGeometricFirstVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory
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

theorem LocalOrbit.time_neighborhood (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) : ∀ᶠ candidate in 𝓝 point, candidate 0 ∈ flow.window :=
  (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds inside)

theorem LocalOrbit.auxiliaryDerivative (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative flow.configuration point direction =
      auxiliaryJet (flow.amplitude (point 0)) (flow.velocity (point 0)) (flow.acceleration (point 0)) direction := by
  have localValues : holonomicP286GaugeAuxiliaryCoordinate flow.configuration =ᶠ[𝓝 point]
      fun candidate => auxiliaryCoordinates (flow.amplitude (candidate 0)) (flow.velocity (candidate 0)) := by
    filter_upwards [flow.time_neighborhood point inside] with candidate belongs
    funext pair
    exact congrArg (fun form => p286CoordinateEquiv (form pair)) (flow.auxiliary candidate belongs)
  have composed := (auxiliaryCoordinates_hasDerivAt flow.amplitude flow.velocity (point 0) _
    (flow.amplitude_derivative _ inside) (flow.velocity_derivative _ inside)).hasFDerivAt.comp point
      (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun candidate : BasePoint =>
    auxiliaryCoordinates (flow.amplitude (candidate 0)) (flow.velocity (candidate 0))) _ point at composed
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [localValues.fderiv_eq, composed.fderiv]
  change (coordinateDirection direction) 0 •
    auxiliaryJet (flow.amplitude (point 0)) (flow.velocity (point 0)) (flow.acceleration (point 0)) 0 = _
  by_cases same : direction = 0
  · simp [same, coordinateDirection]
  · simp [auxiliaryJet, coordinateDirection, same, Ne.symm same]

theorem LocalOrbit.gaugeEuler_zero (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (inside : point 0 ∈ flow.window) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 flow.configuration point = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [flow.chargedThreeForm]
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  have value : holonomicP286GaugeAuxiliaryCoordinate flow.configuration point =
      auxiliaryCoordinates (flow.amplitude (point 0)) (flow.velocity (point 0)) := by
    funext pair
    exact congrArg (fun form => p286CoordinateEquiv (form pair)) (flow.auxiliary point inside)
  have derivative : p286GaugeAuxiliaryDirectionalDerivative flow.configuration point =
      auxiliaryJet (flow.amplitude (point 0)) (flow.velocity (point 0)) (flow.acceleration (point 0)) :=
    funext (flow.auxiliaryDerivative point inside)
  rw [value, derivative]
  change radialEuler point (flow.amplitude (point 0)) (flow.velocity (point 0)) (flow.acceleration (point 0)) = 0
  rw [radialEuler_eq, flow.gauge_force_zero]
  funext triple
  fin_cases triple <;> simp

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

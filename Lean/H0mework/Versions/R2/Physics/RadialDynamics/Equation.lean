import H0mework.Versions.R2.Physics.RadialDynamics.FieldResponse

/-! Actual profile derivatives enter the original gauge Euler jet, while
the original phase-independent charged current supplies its forcing term. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality SU7MotherLieAlgebra Stage9C.Material.SpinPair

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

def nativeGaugeJet (parameter : ℝ) (point : BasePoint) : P286GaugeThreeForm :=
  holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    (radialReadout (responseProfile parameter)) point +
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Runtime.configuration point)

theorem nativeGaugeJet_eq (parameter : ℝ) (point : BasePoint) :
    nativeGaugeJet parameter point = radialEuler point
      (responseProfile parameter (point 0)) (responseVelocity parameter (point 0))
      (parameter*impulseAcceleration (point 0)) := by
  unfold nativeGaugeJet radialEuler
  rw [radialReadout_exterior (responseProfile parameter) (responseVelocity parameter)
    (responseProfile_hasDerivAt parameter) point _ (responseVelocity_hasDerivAt parameter (point 0))]

theorem nativeGaugeJet_background (point : BasePoint) : nativeGaugeJet 0 point = 0 := by
  rw [nativeGaugeJet_eq]
  simpa [responseProfile, responseVelocity] using radialEuler_background point

def orientedSource : P286GaugeThreeForm :=
  ![p286CoordinateEquiv (sourceColorP286Generator 2),
    -p286CoordinateEquiv (sourceColorP286Generator 1),
    p286CoordinateEquiv (sourceColorP286Generator 0),0]

theorem nativeGaugeJet_factor (parameter : ℝ) (point : BasePoint) :
    nativeGaugeJet parameter point =
      force (responseProfile parameter (point 0)) (parameter*impulseAcceleration (point 0)) • orientedSource := by
  rw [nativeGaugeJet_eq, radialEuler_eq]
  funext index
  fin_cases index <;> simp [orientedSource]

theorem nativeGaugeJet_linearized_zero (point : BasePoint) :
    HasDerivAt (fun parameter => nativeGaugeJet parameter point) 0 0 := by
  have generated := (linearized_source_euler (point 0)).smul_const orientedSource
  rw [show (fun parameter => nativeGaugeJet parameter point) =
      fun parameter => force (gaugeScale+parameter*impulse (point 0))
        (parameter*impulseAcceleration (point 0)) • orientedSource from
    funext (fun parameter => nativeGaugeJet_factor parameter point)]
  convert generated using 1 <;> first | rfl | simp

theorem nonlinear_residual (parameter time : ℝ) :
    force (responseProfile parameter time) (parameter*impulseAcceleration time) =
      (6*gaugeScale*parameter^2*(impulse time)^2 + 2*parameter^3*(impulse time)^3)/
        (sourceCoupling*lapse) := by
  have zeroth := force_background
  have first := impulse_equation time
  rw [inertia_eq, stiffness_eq] at first
  unfold force at zeroth ⊢
  unfold responseProfile
  field_simp [ne_of_gt lapse_pos, sourceCoupling_eq] at zeroth first ⊢
  linear_combination zeroth + (1/3:ℝ)*parameter*first

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

import H0mework.Physics.Helicity.Acceptance

/-! Radial jets of the original nonabelian connection. The profile changes
the primitive connection; its electric curvature is an actual derivative. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def radialWrite (profile : ℝ → ℝ) : StageNineHolonomicConfiguration :=
  { Runtime.configuration with gaugeConnection := fun point => gaugePotential (profile (point 0)) }

theorem radialWrite_source : radialWrite (fun _ => gaugeScale) = Runtime.configuration := by
  unfold radialWrite
  rw [show (fun _ : BasePoint => gaugePotential gaugeScale) =
    Runtime.configuration.gaugeConnection by rw [Runtime.configuration_eq, actual_gaugeConnection]]

theorem radialWrite_actualEuler (point : BasePoint) :
    StageNineFormNativeP286GaugeGeometricFirstVariation.holonomicFormNativeP286GaugeEulerThreeForm
      positiveSmoothUnifiedSource 0 (radialWrite (fun _ => gaugeScale)) point = 0 := by
  rw [radialWrite_source, Runtime.configuration_eq]
  exact actual_gaugeEuler_zero point

theorem gaugePotential_smul (amplitude : ℝ) (direction : LorentzianIndex) :
    gaugePotential amplitude direction = amplitude • gaugePotential 1 direction := by
  fin_cases direction <;> simp [gaugePotential]

def radialCurvature (amplitude velocity : ℝ) : Fin 6 → P286LieBlockData :=
  ![velocity • sourceColorP286Generator 0, velocity • sourceColorP286Generator 1,
    velocity • sourceColorP286Generator 2, -(amplitude^2) • sourceColorP286Generator 0,
    -(amplitude^2) • sourceColorP286Generator 1, -(amplitude^2) • sourceColorP286Generator 2]

theorem radialWrite_derivative (profile : ℝ → ℝ) (point : BasePoint) (velocity : ℝ)
    (derivative : HasDerivAt profile velocity (point 0))
    (first second : LorentzianIndex) :
    p286ConnectionDerivative (radialWrite profile) point first second =
      (if first = 0 then velocity else 0) • gaugePotential 1 second := by
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  have composed := (derivative.hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
      ).smul_const (p286CoordinateEquiv (gaugePotential 1 second))
  change HasFDerivAt (fun candidate : BasePoint =>
    profile (candidate 0) • p286CoordinateEquiv (gaugePotential 1 second)) _ point at composed
  have fieldEq : (fun candidate : BasePoint => p286CoordinateEquiv
      ((radialWrite profile).gaugeConnection candidate second)) =
      fun candidate => profile (candidate 0) • p286CoordinateEquiv (gaugePotential 1 second) := by
    funext candidate
    change p286CoordinateEquiv (gaugePotential (profile (candidate 0)) second) = _
    rw [gaugePotential_smul (profile (candidate 0)), map_smul]
  rw [fieldEq, composed.fderiv]
  change p286CoordinateEquiv.symm
    (((coordinateDirection first) 0 * velocity) • p286CoordinateEquiv (gaugePotential 1 second)) = _
  simp only [coordinateDirection, PiLp.single_apply, map_smul, LinearEquiv.symm_apply_apply]
  by_cases same : first = 0
  · simp [same]
  · simp [same, Ne.symm same]

theorem radialWrite_curvature (profile : ℝ → ℝ) (point : BasePoint) (velocity : ℝ)
    (derivative : HasDerivAt profile velocity (point 0)) :
    holonomicGaugeCurvature (radialWrite profile) point = radialCurvature (profile (point 0)) velocity := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [radialWrite_derivative profile point velocity derivative,
    radialWrite_derivative profile point velocity derivative]
  fin_cases pair <;>
    simp [radialWrite, gaugePotential, radialCurvature, pairFirst, pairSecond,
      p286LieBracket_smul_left, p286LieBracket_smul_right,
      sourceColorP286Generator_bracket, smul_smul, pow_two]
  all_goals first
    | exact Or.inr (by simp [p286LieBracket, suLieBracket])
    | module

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

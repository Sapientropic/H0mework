import H0mework.Physics.SourceGauge.Current
import H0mework.Physics.Constitutive.P286GaugeGeometricFirstVariation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Gauge

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineResidualLinearPlebanskiTorsionReduction StageNineLorentzConnectionVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem auxiliary_coordinates (step : ℕ) :
    holonomicP286GaugeAuxiliaryCoordinate (fieldAt step) =
      fun _ pair => p286CoordinateEquiv (electric step pair) := by
  funext point pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [field_auxiliary]

theorem auxiliary_derivative_zero (step : ℕ) (point : BasePoint) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative (fieldAt step) point direction = 0 := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [auxiliary_coordinates]
  rw [(hasFDerivAt_const (𝕜 := ℝ) (fun pair => p286CoordinateEquiv (electric step pair)) point).fderiv]
  rfl

private theorem triad_exterior (amplitude auxiliary : ℝ) :
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (fun direction => p286CoordinateEquiv (gaugePotential amplitude direction))
      ![auxiliary • p286CoordinateEquiv (sourceColorP286Generator 0),
        auxiliary • p286CoordinateEquiv (sourceColorP286Generator 1),
        auxiliary • p286CoordinateEquiv (sourceColorP286Generator 2), 0, 0, 0] 0 =
      ![(2 * amplitude * auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 2),
        (-2 * amplitude * auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 1),
        (2 * amplitude * auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 0), 0] := by
  have bracket (first second : Fin 3) :
      p286CoordinateLieBracket (p286CoordinateEquiv (sourceColorP286Generator first))
        (p286CoordinateEquiv (sourceColorP286Generator second)) =
      p286CoordinateEquiv (p286LieBracket (sourceColorP286Generator first)
        (sourceColorP286Generator second)) := by simp [p286CoordinateLieBracket]
  funext triple
  fin_cases triple <;>
    simp [pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative, orderedP286GaugeTwoFormComponent,
      p286GaugeTwoFormAdjoint, gaugePotential, threeFormFirst, threeFormSecond, threeFormThird,
      orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond, Fin.sum_univ_six,
      map_smul, p286CoordinateLieBracket_smul_left, p286CoordinateLieBracket_smul_right,
      bracket, sourceColorP286Generator_bracket, smul_smul]
  all_goals module

/-- The source-generated gauge/spin balance is consumed by the actual
non-Abelian covariant derivative, including all three color directions. -/
theorem exterior_balance (step : ℕ) (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative (fieldAt step) point = -charged step := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  have connection : holonomicP286GaugeConnectionCoordinate (fieldAt step) point =
      fun direction => p286CoordinateEquiv (gaugePotential gaugeScale direction) := by
    funext direction
    unfold holonomicP286GaugeConnectionCoordinate
    rw [field_connection]
  have derivative : p286GaugeAuxiliaryDirectionalDerivative (fieldAt step) point = 0 :=
    funext (auxiliary_derivative_zero step point)
  rw [connection, auxiliary_coordinates, derivative]
  have auxiliary : (fun pair => p286CoordinateEquiv (electric step pair)) =
      ![auxiliaryScale step • p286CoordinateEquiv (sourceColorP286Generator 0),
        auxiliaryScale step • p286CoordinateEquiv (sourceColorP286Generator 1),
        auxiliaryScale step • p286CoordinateEquiv (sourceColorP286Generator 2), 0, 0, 0] := by
    funext pair
    fin_cases pair <;> simp [electric, map_smul]
  rw [auxiliary, triad_exterior]
  have balance : 2 * gaugeScale * auxiliaryScale step = 4 * clock step * spinScale := by
    have cubic := gauge_balance step
    unfold auxiliaryScale
    field_simp [ne_of_gt (coupling_pos step), ne_of_gt (clock_pos step)]
    nlinarith only [cubic]
  have negative : -2 * gaugeScale * auxiliaryScale step = -(4 * clock step * spinScale) := by
    linarith only [balance]
  rw [balance, negative]
  funext triple
  fin_cases triple <;> simp [charged, neg_smul]

theorem gauge_euler_zero (step : ℕ) (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual (sourceAt step) (fieldAt step) point).p286GaugeConnection = 0 := by
  change holonomicFormNativeP286GaugeEulerThreeForm (sourceAt step) 0 (fieldAt step) point = 0
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [exterior_balance, charged_three_form, neg_add_cancel]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Gauge

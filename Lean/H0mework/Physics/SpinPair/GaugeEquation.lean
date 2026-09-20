import H0mework.Physics.SpinPair.GaugeCurrent
import H0mework.Physics.Constitutive.P286GaugeGeometricFirstVariation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeAuxiliaryVariation StageNineP286SourceRelativeWardAlgebra
open StageNineResidualLinearPlebanskiTorsionReduction StageNineLorentzConnectionVariation
open StageNineFormNativeP286GaugeGeometricKinematics StageNineFormNativeP286GaugeGeometricFirstVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem actual_gaugeAuxiliaryCoordinate :
    holonomicP286GaugeAuxiliaryCoordinate actual = fun _ pair =>
      p286CoordinateEquiv (electricAuxiliary lapse gaugeScale pair) := by
  funext point pair
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [actual_gaugeAuxiliary]

theorem actual_gaugeAuxiliaryDerivative_zero (point : BasePoint) (direction : LorentzianIndex) :
    p286GaugeAuxiliaryDirectionalDerivative actual point direction = 0 := by
  unfold p286GaugeAuxiliaryDirectionalDerivative fieldDirectionalDerivative
  rw [actual_gaugeAuxiliaryCoordinate]
  rw [(hasFDerivAt_const (𝕜 := ℝ)
    (fun pair => p286CoordinateEquiv (electricAuxiliary lapse gaugeScale pair)) point).fderiv]
  rfl

private theorem triadExterior
    (amplitude auxiliary : ℝ) :
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (fun direction => p286CoordinateEquiv (gaugePotential amplitude direction))
      ![auxiliary • p286CoordinateEquiv (sourceColorP286Generator 0),
        auxiliary • p286CoordinateEquiv (sourceColorP286Generator 1),
        auxiliary • p286CoordinateEquiv (sourceColorP286Generator 2),0,0,0]
      0 =
      ![(2*amplitude*auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 2),
        (-2*amplitude*auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 1),
        (2*amplitude*auxiliary) • p286CoordinateEquiv (sourceColorP286Generator 0),0] := by
  have bracket (first second : Fin 3) :
      p286CoordinateLieBracket (p286CoordinateEquiv (sourceColorP286Generator first))
        (p286CoordinateEquiv (sourceColorP286Generator second)) =
      p286CoordinateEquiv (p286LieBracket (sourceColorP286Generator first)
        (sourceColorP286Generator second)) := by
    simp [p286CoordinateLieBracket]
  funext triple
  fin_cases triple <;>
    simp [pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
      pointwiseP286GaugeTwoFormCovariantDerivative, orderedP286GaugeTwoFormComponent,
      p286GaugeTwoFormAdjoint, gaugePotential, threeFormFirst, threeFormSecond, threeFormThird,
      orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond, Fin.sum_univ_six,
      map_smul, p286CoordinateLieBracket_smul_left, p286CoordinateLieBracket_smul_right,
      bracket, sourceColorP286Generator_bracket, smul_smul]
  all_goals module

theorem actual_gaugeExterior (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative actual point = -chargedThreeForm := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
  have connection : holonomicP286GaugeConnectionCoordinate actual point =
      fun direction => p286CoordinateEquiv (gaugePotential gaugeScale direction) := by
    funext direction
    unfold holonomicP286GaugeConnectionCoordinate
    rw [actual_gaugeConnection]
  have derivative : p286GaugeAuxiliaryDirectionalDerivative actual point = 0 :=
    funext (actual_gaugeAuxiliaryDerivative_zero point)
  rw [connection, actual_gaugeAuxiliaryCoordinate, derivative]
  have auxiliary : (fun pair => p286CoordinateEquiv (electricAuxiliary lapse gaugeScale pair)) =
      ![(gaugeScale^2/(sourceCoupling*lapse)) • p286CoordinateEquiv (sourceColorP286Generator 0),
        (gaugeScale^2/(sourceCoupling*lapse)) • p286CoordinateEquiv (sourceColorP286Generator 1),
        (gaugeScale^2/(sourceCoupling*lapse)) • p286CoordinateEquiv (sourceColorP286Generator 2),0,0,0] := by
    funext pair
    fin_cases pair <;> simp [electricAuxiliary, map_smul]
  rw [auxiliary, triadExterior]
  have balance : 2*gaugeScale*(gaugeScale^2/(sourceCoupling*lapse)) = 4*lapse*spinScale := by
    have coupling := sourceCoupling_eq
    have cubic := gauge_cubic_balance
    have nonzero := ne_of_gt lapse_pos
    field_simp
    nlinarith [cubic]
  have negative : -2*gaugeScale*(gaugeScale^2/(sourceCoupling*lapse)) = -(4*lapse*spinScale) := by
    linarith [balance]
  rw [balance, negative]
  funext triple
  fin_cases triple <;> simp [chargedThreeForm, neg_smul]

theorem actual_gaugeEuler_zero (point : BasePoint) :
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0 actual point = 0 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [actual_gaugeExterior, actual_chargedThreeForm, neg_add_cancel]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

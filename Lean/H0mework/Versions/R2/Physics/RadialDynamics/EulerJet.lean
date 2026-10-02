import H0mework.Versions.R2.Physics.RadialDynamics.Constitutive

/-! The original exterior-covariant Euler consumer applied to radial jets.
Its source current is retained with the action's sign and normalization. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeGeometricKinematics StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineP286SourceRelativeWardAlgebra StageNineResidualLinearPlebanskiTorsionReduction
open StageNineLorentzConnectionVariation
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def electricCoordinates : P286GaugeTwoForm :=
  ![p286CoordinateEquiv (sourceColorP286Generator 0),
    p286CoordinateEquiv (sourceColorP286Generator 1),
    p286CoordinateEquiv (sourceColorP286Generator 2),0,0,0]

def magneticCoordinates : P286GaugeTwoForm :=
  ![0,0,0,p286CoordinateEquiv (sourceColorP286Generator 0),
    p286CoordinateEquiv (sourceColorP286Generator 1),
    p286CoordinateEquiv (sourceColorP286Generator 2)]

def auxiliaryCoordinates (amplitude velocity : ℝ) : P286GaugeTwoForm :=
  fun pair => p286CoordinateEquiv (radialAuxiliary amplitude velocity pair)

theorem auxiliaryCoordinates_eq (amplitude velocity : ℝ) :
    auxiliaryCoordinates amplitude velocity =
      (amplitude^2/(sourceCoupling*lapse)) • electricCoordinates +
        (lapse*velocity/sourceCoupling) • magneticCoordinates := by
  unfold auxiliaryCoordinates
  rw [radialAuxiliary_eq]
  funext pair
  fin_cases pair <;> simp [electricCoordinates, magneticCoordinates, map_smul]

def auxiliaryJet (amplitude velocity acceleration : ℝ) : LorentzianIndex → P286GaugeTwoForm :=
  fun direction => if direction = 0 then
    (2*amplitude*velocity/(sourceCoupling*lapse)) • electricCoordinates +
      (lapse*acceleration/sourceCoupling) • magneticCoordinates else 0

def radialEuler (point : BasePoint) (amplitude velocity acceleration : ℝ) : P286GaugeThreeForm :=
  pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    (fun direction => p286CoordinateEquiv (gaugePotential amplitude direction))
    (auxiliaryCoordinates amplitude velocity) (auxiliaryJet amplitude velocity acceleration) +
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Runtime.configuration point)

def force (amplitude acceleration : ℝ) : ℝ :=
  lapse*acceleration/sourceCoupling + 2*amplitude^3/(sourceCoupling*lapse) - 4*lapse*spinScale

private theorem triadExterior (amplitude electric magnetic electricRate magneticRate : ℝ) :
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
      (fun direction => p286CoordinateEquiv (gaugePotential amplitude direction))
      (electric • electricCoordinates + magnetic • magneticCoordinates)
      (fun direction => if direction = 0 then
        electricRate • electricCoordinates + magneticRate • magneticCoordinates else 0) =
      ![(magneticRate+2*amplitude*electric) • p286CoordinateEquiv (sourceColorP286Generator 2),
        (-(magneticRate+2*amplitude*electric)) • p286CoordinateEquiv (sourceColorP286Generator 1),
        (magneticRate+2*amplitude*electric) • p286CoordinateEquiv (sourceColorP286Generator 0),0] := by
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
      electricCoordinates, magneticCoordinates, map_smul,
      p286CoordinateLieBracket_smul_left, p286CoordinateLieBracket_smul_right,
      bracket, sourceColorP286Generator_bracket, smul_smul]
  all_goals module

theorem radialEuler_eq (point : BasePoint) (amplitude velocity acceleration : ℝ) :
    radialEuler point amplitude velocity acceleration =
      ![force amplitude acceleration • p286CoordinateEquiv (sourceColorP286Generator 2),
        -force amplitude acceleration • p286CoordinateEquiv (sourceColorP286Generator 1),
        force amplitude acceleration • p286CoordinateEquiv (sourceColorP286Generator 0),0] := by
  unfold radialEuler auxiliaryJet
  rw [auxiliaryCoordinates_eq, triadExterior, Runtime.configuration_eq, actual_chargedThreeForm]
  have coeff : lapse*acceleration/sourceCoupling +
      2*amplitude*(amplitude^2/(sourceCoupling*lapse)) =
      force amplitude acceleration + 4*lapse*spinScale := by unfold force; ring
  rw [coeff]
  funext triple
  fin_cases triple <;> simp [chargedThreeForm] <;> module

theorem force_background : force gaugeScale 0 = 0 := by
  unfold force
  rw [gauge_cubic_balance]
  field_simp [ne_of_gt lapse_pos, sourceCoupling_eq]
  ring

theorem radialEuler_background (point : BasePoint) : radialEuler point gaugeScale 0 0 = 0 := by
  rw [radialEuler_eq, force_background]
  ext triple
  fin_cases triple <;> simp

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

import H0mework.Versions.AB.Physics.LowEnergyResponse.Yukawa
import H0mework.Physics.GaugeStanding.ScalarPairingSkew
import H0mework.Versions.AB.Physics.LowEnergyResponse.ScalarSignature

/-! ORIGINAL vacuum radial tangent, not an independently selected scalar.
Mixed Yukawa and gauge couplings vanish on this real direction; native temporal
sign and a growing scalar Euler profile are exposed without changing the action.
Full functional Jacobi decoupling is derived in the accompanying analytic note. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Response.Radial
open ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra
open StageNineHolonomicField StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open StageNineP286LinkedActiveScalarPairingSkew
noncomputable section

def direction : ScalarCoordinateCarrier :=
  sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource

private theorem pairing_symmetric (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second = scalarCoordinatePairingRe second first := by
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re]
  ring

theorem radial_gauge_cross_zero (matrix : SU7MotherLieMatrix) :
    scalarCoordinatePairingRe (scalarMotherLieAction matrix direction) direction = 0 := by
  have skew := scalarCoordinatePairingRe_scalarMotherLieAction_skew matrix direction direction
  rw [pairing_symmetric direction (scalarMotherLieAction matrix direction)] at skew
  linarith

theorem radial_yukawa_cross_zero (point : BasePoint) :
    Yukawa.linearVector point direction 0 = 0 := by
  simp only [Yukawa.linearVector, map_zero, zero_add, direction,
    sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply]
  exact Yukawa.background_zero point

theorem direction_nonzero : direction ≠ 0 := by
  intro zero
  have original := congrArg scalarCoordinateEquiv.symm zero
  exact positive_sourceGeneratedVacuumBase_nonzero (by
    simpa [direction, sourceGeneratedVacuumCoordinates] using original)

/-- This nonzero radial tangent is not an internal gauge-orbit tangent. -/
theorem radial_not_gauge (matrix : SU7MotherLieMatrix) :
    scalarMotherLieAction matrix direction ≠ direction := by
  intro equal
  have cross := radial_gauge_cross_zero matrix
  rw [equal] at cross
  have normZero : scalarCoordinateSquaredNorm direction = 0 :=
    (scalarCoordinateRealPairing_self direction).symm.trans cross
  exact direction_nonzero ((scalarCoordinateSquaredNorm_eq_zero_iff direction).mp normZero)

theorem background_action_zero (point : BasePoint) (mu : LorentzianIndex) :
    scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) direction = 0 := by
  have original := congrFun (actual_scalarCovariantDerivative_zero point) mu
  simpa [holonomicScalarCovariantDerivative, actual_scalar, fieldDirectionalDerivative,
    direction] using original

/-- Source-derived coordinate-time rate; not a new tunable mass. -/
def growthRate : ℝ := Real.sqrt (2 * lapse^2)
def amplitude (time : ℝ) : ℝ := Real.exp (growthRate * time)
def velocity (time : ℝ) : ℝ := growthRate * amplitude time
def acceleration (time : ℝ) : ℝ := growthRate^2 * amplitude time

theorem growthRate_pos : 0 < growthRate :=
  Real.sqrt_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos lapse_pos))

theorem growthRate_sq : growthRate^2 = 2 * lapse^2 :=
  Real.sq_sqrt (by positivity)

theorem coordinate_rate_sq : growthRate^2 = 108 / 125 := by
  rw [growthRate_sq, lapse_sq]
  norm_num

theorem first_derivative (time : ℝ) : HasDerivAt amplitude (velocity time) time := by
  change HasDerivAt (fun t : ℝ => Real.exp (growthRate * t))
    (growthRate * Real.exp (growthRate * time)) time
  simpa only [id_eq, mul_one, mul_comm] using
    (((hasDerivAt_id time).const_mul growthRate).exp)

theorem second_derivative (time : ℝ) : HasDerivAt velocity (acceleration time) time := by
  change HasDerivAt (fun t : ℝ => growthRate * amplitude t)
    (growthRate^2 * amplitude time) time
  simpa only [velocity, pow_two, mul_assoc] using
    ((first_derivative time).const_mul growthRate)

/-- The scalar Euler expression of -f'^2/(2N^2)-f^2 vanishes.
The functional connection to all nine fields remains explicit in the note. -/
theorem native_temporal_euler (time : ℝ) :
    acceleration time / lapse^2 - 2 * amplitude time = 0 := by
  unfold acceleration
  rw [growthRate_sq]
  field_simp [ne_of_gt lapse_pos]
  ring

theorem amplitude_grows (time : ℝ) (positive : 0 < time) : 1 < amplitude time := by
  exact Real.one_lt_exp_iff.mpr (mul_pos growthRate_pos positive)

end
end SaturationMonoid.PhysicsCore.LowEnergy.Response.Radial

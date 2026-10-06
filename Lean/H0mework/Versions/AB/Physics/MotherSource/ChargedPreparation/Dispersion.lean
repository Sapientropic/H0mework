import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Dynamics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual charged two-state Hamiltonian generates its energies and inertial scale. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Dispersion
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open LowEnergy.FullQuantum YangMills.FullPairing Stage10.ChargedPreparation.Dynamics
open scoped Matrix Topology
noncomputable section

theorem frequency_pos : 0 < frequency := by
  rw [frequency_gauge]
  exact mul_pos lapse_pos gaugeScale_pos

def rate (momentum : ℝ) : ℝ := Real.sqrt (frequency^2 + lapse^2*momentum^2)
def upperEnergy (momentum : ℝ) : ℝ := 2*frequency + rate momentum
def lowerEnergy (momentum : ℝ) : ℝ := 2*frequency - rate momentum

theorem rate_sq (momentum : ℝ) : (rate momentum)^2 = frequency^2 + lapse^2*momentum^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem rate_pos (momentum : ℝ) : 0 < rate momentum := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos frequency_pos)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem rate_zero : rate 0 = frequency := by
  simp [rate, Real.sqrt_sq_eq_abs, abs_of_pos frequency_pos]

theorem bandValues_smul (coefficient first second : ℂ) :
    bandValues (coefficient*first) (coefficient*second) = coefficient • bandValues first second := by
  funext i
  simp only [bandValues, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def eigenstate (momentum value : ℝ) : DiracExteriorMatterCarrier :=
  embed (bandValues (frequency : ℂ) ((value-lapse*momentum : ℝ) : ℂ))

private theorem band_eigen (point : BasePoint) (momentum value : ℝ)
    (square : value^2 = frequency^2 + lapse^2*momentum^2) :
    hamiltonian actual point ![0,0,momentum] (eigenstate momentum value) =
      ((2*frequency+value : ℝ) : ℂ) • eigenstate momentum value := by
  unfold eigenstate
  rw [physical_band, ← map_smul, ← bandValues_smul]
  have squareC : (value : ℂ)^2 = (frequency : ℂ)^2 + (lapse : ℂ)^2*(momentum : ℂ)^2 := by
    exact_mod_cast square
  congr 2
  · push_cast
    ring
  · push_cast
    linear_combination -squareC

theorem upper_eigen (point : BasePoint) (momentum : ℝ) :
    hamiltonian Stage10.Runtime.configuration point ![0,0,momentum]
        (eigenstate momentum (rate momentum)) =
      (upperEnergy momentum : ℂ) • eigenstate momentum (rate momentum) := by
  rw [Stage10.Runtime.configuration_eq]
  exact band_eigen point momentum (rate momentum) (rate_sq momentum)

theorem lower_eigen (point : BasePoint) (momentum : ℝ) :
    hamiltonian Stage10.Runtime.configuration point ![0,0,momentum]
        (eigenstate momentum (-rate momentum)) =
      (lowerEnergy momentum : ℂ) • eigenstate momentum (-rate momentum) := by
  rw [Stage10.Runtime.configuration_eq]
  exact band_eigen point momentum (-rate momentum) (by simpa using rate_sq momentum)

theorem eigenstate_nonzero (momentum value : ℝ) : eigenstate momentum value ≠ 0 := by
  intro zero
  have coordinate := congrArg (fun matter => coordinates matter (2,1)) zero
  simp [eigenstate, coordinates_embed, bandValues] at coordinate
  exact frequency_pos.ne' coordinate

theorem upper_zero : upperEnergy 0 = 3*frequency := by rw [upperEnergy, rate_zero]; ring
theorem lower_zero : lowerEnergy 0 = frequency := by rw [lowerEnergy, rate_zero]; ring

/-- Energy above the same band's original zero-momentum value. -/
def excitation (momentum : ℝ) : ℝ := upperEnergy momentum - upperEnergy 0

theorem excitation_exact (momentum : ℝ) :
    excitation momentum = lapse^2*momentum^2/(rate momentum+frequency) := by
  have denominator := add_pos (rate_pos momentum) frequency_pos
  unfold excitation
  rw [upperEnergy, upper_zero]
  apply (eq_div_iff denominator.ne').mpr
  nlinarith [rate_sq momentum]

def inertia : ℝ := frequency/lapse^2

theorem inertia_pos : 0 < inertia := div_pos frequency_pos (sq_pos_of_pos lapse_pos)

theorem excitation_quadratic_remainder (momentum : ℝ) :
    excitation momentum = momentum^2/(2*inertia) -
      lapse^4*momentum^4/(2*frequency*(rate momentum+frequency)^2) := by
  rw [excitation_exact]
  have d := add_pos (rate_pos momentum) frequency_pos
  unfold inertia
  field_simp [d.ne', frequency_pos.ne', lapse_pos.ne']
  nlinarith [rate_sq momentum]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Dispersion

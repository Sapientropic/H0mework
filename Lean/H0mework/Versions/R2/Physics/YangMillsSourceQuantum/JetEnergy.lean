import H0mework.Versions.R2.Physics.YangMillsSourceQuantum.TimeJet

/-! The original Legendre energy consumes the source quantum time jets.
The quantifiers remain those of the original complete coupled radial orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet

open Stage9C.Material.SpinPair
open Stage10.GaugeSpectrum Stage10.GaugeSpectrum.Dynamics
open Stage10.GaugeSpectrum.Nonlinear Stage10.GaugeSpectrum.Global

noncomputable section
variable {impulse : ℝ} (trajectory : CompleteOrbit impulse)

def jetEnergy (t : ℝ) : ℝ :=
  energy (radiusRead trajectory t) (momentumRead trajectory t) - energy gaugeScale 0

def jetRemainder (t : ℝ) : ℝ :=
  3 / (4 * sourceCoupling * lapse) * (radiusRead trajectory t - gaugeScale)^2 *
    (radiusRead trajectory t + gaugeScale)^2

theorem jetEnergy_physical (t : ℝ) :
    jetEnergy trajectory t = hamiltonian (trajectory.curve t) - hamiltonian (Nonlinear.seed 0) := by
  rw [jetEnergy, radiusRead_eq, momentumRead_eq]
  rfl

theorem jetRemainder_nonnegative (t : ℝ) : 0 ≤ jetRemainder trajectory t := by
  unfold jetRemainder
  rw [sourceCoupling_eq]
  exact mul_nonneg (mul_nonneg (le_of_lt (div_pos (by norm_num)
    (mul_pos (by norm_num) lapse_pos))) (sq_nonneg _)) (sq_nonneg _)

theorem jetEnergy_generated (t : ℝ) :
    jetEnergy trajectory t =
      (momentumRead trajectory t)^2 / (2 * inertia) +
        coercivity * (radiusRead trajectory t - gaugeScale)^2 + jetRemainder trajectory t := by
  have generated := potentialGap_eq (radiusRead trajectory t)
  unfold potentialGap at generated
  simp only [jetEnergy, energy_eq, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add]
  rw [show (momentumRead trajectory t)^2 / (2 * inertia) +
      potential (radiusRead trajectory t) - potential gaugeScale =
      (momentumRead trajectory t)^2 / (2 * inertia) +
        (potential (radiusRead trajectory t) - potential gaugeScale) by ring, generated]
  unfold coercivity jetRemainder
  ring

theorem jetEnergy_lower (t : ℝ) :
    (momentumRead trajectory t)^2 / (2 * inertia) +
      coercivity * (radiusRead trajectory t - gaugeScale)^2 ≤ jetEnergy trajectory t := by
  rw [jetEnergy_generated]
  exact le_add_of_nonneg_right (jetRemainder_nonnegative trajectory t)

theorem quantum_jet_physical_energy (sourceImpulse t : ℝ) :
    let source := completeOrbit sourceImpulse
    hamiltonian (source.curve t) - hamiltonian (Nonlinear.seed 0) =
      (-(2 * inertia / (3 * lapse)) * deriv (rateRead source) t)^2 / (2 * inertia) +
        coercivity * (spinScale - (2 / (3 * lapse)) * rateRead source t - gaugeScale)^2 +
          jetRemainder source t := by
  dsimp only
  rw [← jetEnergy_physical (completeOrbit sourceImpulse) t, jetEnergy_generated]
  rfl

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet

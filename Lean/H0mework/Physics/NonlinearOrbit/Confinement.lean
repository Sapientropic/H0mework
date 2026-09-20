import H0mework.Physics.NonlinearOrbit.Observable

/-! Exact source energy confines the nonlinear mechanical coordinates. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair

noncomputable section

def potentialGap (amplitude : ℝ) : ℝ := potential amplitude-potential gaugeScale

theorem potentialGap_eq (amplitude : ℝ) :
    potentialGap amplitude = 3/(4*sourceCoupling*lapse)*(amplitude-gaugeScale)^2*
      ((amplitude+gaugeScale)^2+2*gaugeScale^2) := by
  unfold potentialGap
  rw [potential_eq, potential_eq]
  have stationary := equilibrium
  rw [restoring_eq] at stationary
  linear_combination (amplitude-gaugeScale)*stationary

theorem potentialGap_nonnegative (amplitude : ℝ) : 0 ≤ potentialGap amplitude := by
  rw [potentialGap_eq, sourceCoupling_eq]
  exact mul_nonneg (mul_nonneg (le_of_lt (div_pos (by norm_num)
    (mul_pos (by norm_num) lapse_pos))) (sq_nonneg _)) (by positivity)

theorem potentialGap_lower (amplitude : ℝ) :
    (3*gaugeScale^2/(2*sourceCoupling*lapse))*(amplitude-gaugeScale)^2 ≤ potentialGap amplitude := by
  rw [potentialGap_eq]
  have coefficient : 0 ≤ 3/(4*sourceCoupling*lapse)*(amplitude-gaugeScale)^2 := by
    rw [sourceCoupling_eq]
    exact mul_nonneg (le_of_lt (div_pos (by norm_num) (mul_pos (by norm_num) lapse_pos))) (sq_nonneg _)
  have generated := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (a := 2*gaugeScale^2) (sq_nonneg (amplitude+gaugeScale))) coefficient
  convert generated using 1 <;> first | rfl | ring

theorem orbit_energy_balance (canonicalImpulse time : ℝ) (inside : time ∈ (orbit canonicalImpulse).window) :
    ((orbit canonicalImpulse).momentum time)^2/(2*inertia) + potentialGap ((orbit canonicalImpulse).amplitude time) =
      canonicalImpulse^2/(2*inertia) := by
  have conserved := (orbit canonicalImpulse).energy_conserved time inside
  change energy ((orbit canonicalImpulse).amplitude time) ((orbit canonicalImpulse).momentum time) =
    energy gaugeScale canonicalImpulse at conserved
  rw [energy_eq, energy_eq] at conserved
  unfold potentialGap
  linarith

theorem orbit_momentum_bound (canonicalImpulse time : ℝ) (inside : time ∈ (orbit canonicalImpulse).window) :
    ((orbit canonicalImpulse).momentum time)^2 ≤ canonicalImpulse^2 := by
  have conserved := orbit_energy_balance canonicalImpulse time inside
  have positive := potentialGap_nonnegative ((orbit canonicalImpulse).amplitude time)
  field_simp [ne_of_gt inertia_pos] at conserved
  nlinarith [inertia_pos]

theorem orbit_amplitude_bound (canonicalImpulse time : ℝ) (inside : time ∈ (orbit canonicalImpulse).window) :
    (3*gaugeScale^2/(2*sourceCoupling*lapse))*((orbit canonicalImpulse).amplitude time-gaugeScale)^2 ≤
      canonicalImpulse^2/(2*inertia) := by
  have conserved := orbit_energy_balance canonicalImpulse time inside
  have kinetic : 0 ≤ ((orbit canonicalImpulse).momentum time)^2/(2*inertia) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) inertia_pos))
  exact (potentialGap_lower _).trans (by linarith)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

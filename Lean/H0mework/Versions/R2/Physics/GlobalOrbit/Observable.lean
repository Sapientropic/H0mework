import H0mework.Versions.R2.Physics.GlobalOrbit.Field

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair

noncomputable section

variable {impulse : ℝ}

theorem CompleteOrbit.energy_balance (trajectory : CompleteOrbit impulse) (time : ℝ) :
    (trajectory.curve time).2.1^2/(2*inertia) + potentialGap (trajectory.curve time).1 = excess impulse := by
  have conserved := trajectory.energy_conserved time
  change energy (trajectory.curve time).1 (trajectory.curve time).2.1 = energy gaugeScale impulse at conserved
  rw [energy_eq, energy_eq] at conserved
  unfold potentialGap excess
  linarith

theorem CompleteOrbit.momentum_bound (trajectory : CompleteOrbit impulse) (time : ℝ) :
    (trajectory.curve time).2.1^2 ≤ impulse^2 := by
  have conserved := trajectory.energy_balance time
  have gap := potentialGap_nonnegative (trajectory.curve time).1
  unfold excess at conserved
  field_simp [ne_of_gt inertia_pos] at conserved
  nlinarith [inertia_pos]

theorem CompleteOrbit.amplitude_bound (trajectory : CompleteOrbit impulse) (time : ℝ) :
    coercivity*((trajectory.curve time).1-gaugeScale)^2 ≤ excess impulse := by
  have conserved := trajectory.energy_balance time
  have kinetic : 0 ≤ (trajectory.curve time).2.1^2/(2*inertia) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) inertia_pos))
  exact (potentialGap_lower _).trans (by linarith)

theorem CompleteOrbit.initialQ_derivative (trajectory : CompleteOrbit impulse) :
    HasDerivAt trajectory.helicity (15*gaugeScale^4*impulse/inertia) 0 := by
  have derivative := trajectory.helicity_derivative 0
  rw [trajectory.starts] at derivative
  convert derivative using 1
  change 15*gaugeScale^4*impulse/inertia = 15*gaugeScale^4*(impulse/inertia)
  ring

theorem CompleteOrbit.initialQ_nonzero (trajectory : CompleteOrbit impulse) (nonzero : impulse ≠ 0) :
    deriv trajectory.helicity 0 ≠ 0 := by
  rw [trajectory.initialQ_derivative.deriv]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt gaugeScale_pos))) nonzero)
    (ne_of_gt inertia_pos)

theorem CompleteOrbit.helicity_changes (trajectory : CompleteOrbit impulse) (nonzero : impulse ≠ 0) :
    ∃ time, trajectory.helicity time ≠ trajectory.helicity 0 := by
  by_contra unchanged
  push Not at unchanged
  have derivative := (hasDerivAt_const 0 (trajectory.helicity 0)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall unchanged)
  exact trajectory.initialQ_nonzero nonzero derivative.deriv

theorem CompleteOrbit.field_changes (trajectory : CompleteOrbit impulse) (nonzero : impulse ≠ 0) :
    ∃ point : BasePoint, trajectory.fieldValue point ≠ trajectory.fieldValue 0 := by
  obtain ⟨time, differs⟩ := trajectory.helicity_changes nonzero
  refine ⟨Stage9DEF.Dynamics.timeDisplacement time, ?_⟩
  rw [trajectory.fieldValue_helicity, trajectory.fieldValue_helicity]
  simpa using differs

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

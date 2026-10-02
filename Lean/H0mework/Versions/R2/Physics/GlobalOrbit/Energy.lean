import H0mework.Versions.R2.Physics.GlobalOrbit.Mechanical

/-! Original energy is preserved even before removing the smooth extension.
Its exact source confinement then removes the extension on the whole orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
open Stage9C.Material.SpinPair

noncomputable section

variable {impulse : ℝ}

theorem MechanicalFlow.position_derivative (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt (fun t => (flow.curve t).1) (cutoff impulse (flow.curve time)*(flow.curve time).2/inertia) time := by
  have projected := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time (flow.evolves time)
  convert projected using 1 <;> first | rfl | simp [compactField, mechanicalField_eq]; ring

theorem MechanicalFlow.momentum_derivative (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt (fun t => (flow.curve t).2) (-cutoff impulse (flow.curve time)*restoring (flow.curve time).1) time := by
  have projected := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time (flow.evolves time)
  convert projected using 1 <;> first | rfl | simp [compactField, mechanicalField_eq]

theorem MechanicalFlow.energy_derivative (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt (fun t => energy (flow.curve t).1 (flow.curve t).2) 0 time := by
  have kinetic := ((flow.momentum_derivative time).pow 2).div_const (2*inertia)
  have potential := (potential_hasDerivAt (flow.curve time).1).comp time (flow.position_derivative time)
  rw [← restoring_eq] at potential
  simp_rw [energy_eq]
  convert kinetic.add potential using 1 <;> first | rfl | ring

theorem MechanicalFlow.energy_conserved (flow : MechanicalFlow impulse) (time : ℝ) :
    energy (flow.curve time).1 (flow.curve time).2 = energy gaugeScale impulse := by
  have same := is_const_of_deriv_eq_zero (fun t => (flow.energy_derivative t).differentiableAt)
    (fun t => (flow.energy_derivative t).deriv) time 0
  simpa only [flow.starts, initialMechanical] using same

theorem MechanicalFlow.balance (flow : MechanicalFlow impulse) (time : ℝ) :
    (flow.curve time).2^2/(2*inertia) + potentialGap (flow.curve time).1 = excess impulse := by
  have conserved := flow.energy_conserved time
  rw [energy_eq, energy_eq] at conserved
  unfold potentialGap excess
  linarith

private theorem abs_le_of_square_bound (value bound : ℝ) (h : value^2 ≤ bound) : |value| ≤ bound+1 := by
  have nonnegative := (sq_nonneg value).trans h
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (value-1), sq_nonneg (value+1)]

theorem MechanicalFlow.cutoff_one (flow : MechanicalFlow impulse) (time : ℝ) : cutoff impulse (flow.curve time) = 1 := by
  have conserved := flow.balance time
  have gap := potentialGap_nonnegative (flow.curve time).1
  have momentumBound : (flow.curve time).2^2 ≤ impulse^2 := by
    unfold excess at conserved
    field_simp [ne_of_gt inertia_pos] at conserved
    nlinarith [inertia_pos]
  have kinetic : 0 ≤ (flow.curve time).2^2/(2*inertia) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) inertia_pos))
  have amplitudeBound : ((flow.curve time).1-gaugeScale)^2 ≤ excess impulse/coercivity := by
    apply (le_div_iff₀ coercivity_pos).mpr
    have lower := potentialGap_lower (flow.curve time).1
    change coercivity*((flow.curve time).1-gaugeScale)^2 ≤ _ at lower
    nlinarith
  apply (cutoff impulse).one_of_mem_closedBall
  change max |(flow.curve time).1-gaugeScale| |(flow.curve time).2-0| ≤ radius impulse
  rw [sub_zero]
  have excessBound := div_nonneg (excess_nonnegative impulse) (le_of_lt coercivity_pos)
  apply max_le
  · exact (abs_le_of_square_bound _ _ amplitudeBound).trans (by unfold radius; nlinarith [sq_nonneg impulse])
  · exact (abs_le_of_square_bound _ _ momentumBound).trans (by unfold radius; linarith)

theorem MechanicalFlow.original_evolves (flow : MechanicalFlow impulse) (time : ℝ) :
    HasDerivAt flow.curve (mechanicalField (flow.curve time)) time := by
  have original := flow.evolves time
  rw [compactField, flow.cutoff_one, one_smul] at original
  exact original

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global

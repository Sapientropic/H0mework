import H0mework.Physics.LowEnergyEvolution.VariationEstimate

/-! True first derivative in the initial condition, obtained from the source Taylor remainder. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation
open Set Filter Metric Asymptotics
open scoped Topology
noncomputable section

private def timeSign (time : ℝ) : ℝ := if 0 ≤ time then 1 else -1

private theorem timeSign_norm (time : ℝ) : |timeSign time| = 1 := by
  unfold timeSign
  split_ifs <;> norm_num

private theorem timeSign_mul_abs (time : ℝ) : timeSign time * |time| = time := by
  by_cases nonnegative : 0 ≤ time
  · simp [timeSign, nonnegative, abs_of_nonneg nonnegative]
  · simp [timeSign, nonnegative, abs_of_nonpos (le_of_lt (lt_of_not_ge nonnegative))]

private def amplification (family : UniformDevelopment baseState) (time : ℝ) : ℝ :=
  (((family.dependenceConstant:ℝ)+1)/growthBound) * (Real.exp (growthBound*|time|)-1)+1

private theorem amplification_positive (family : UniformDevelopment baseState) (time : ℝ) :
    0 < amplification family time := by
  have exponential : 0 ≤ Real.exp (growthBound*|time|)-1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg (le_of_lt growthBound_positive) (abs_nonneg time)))
  have positive := growthBound_positive
  unfold amplification
  positivity

theorem initial_derivative (family : UniformDevelopment baseState) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    HasFDerivAt (fun initial => family.curve initial time) (linearFlow time) baseState := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply IsLittleO.of_bound
  intro epsilon epsilonPositive
  let Q : ℝ := (family.dependenceConstant:ℝ)+1
  have QPositive : 0 < Q := by dsimp [Q]; positivity
  let eta := epsilon/amplification family time
  have etaPositive : 0 < eta := div_pos epsilonPositive (amplification_positive family time)
  have near : {z : State | ‖centeredGenerator z-jacobian z‖ ≤ eta*‖z‖} ∈ 𝓝 (0:State) :=
    centered_remainder.bound etaPositive
  obtain ⟨delta, deltaPositive, remainderSmall⟩ := Metric.mem_nhds_iff.mp near
  let radius := min family.initialRadius (delta/Q)
  have radiusPositive : 0 < radius := lt_min family.initialPositive (div_pos deltaPositive QPositive)
  filter_upwards [ball_mem_nhds (0:State) radiusPositive] with h hInside
  have normSmall : ‖h‖ < radius := by simpa only [Metric.mem_ball, dist_zero_right] using hInside
  have initialInside : baseState+h ∈ closedBall baseState family.initialRadius := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact le_of_lt (lt_of_lt_of_le normSmall (min_le_left _ _))
  have scaledSmall : Q*‖h‖ < delta := by
    have small : ‖h‖ < delta/Q := lt_of_lt_of_le normSmall (min_le_right _ _)
    have bound := (lt_div_iff₀ QPositive).mp small
    nlinarith
  have horizonInside : |time| < family.timeRadius := abs_lt.mpr inside
  have temporal (t : ℝ) (ht : t ∈ Icc 0 |time|) :
      timeSign time*t ∈ Ioo (-family.timeRadius) family.timeRadius := by
    apply abs_lt.mp
    rw [abs_mul, timeSign_norm, one_mul, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 horizonInside
  have remainder (t : ℝ) (ht : t ∈ Icc 0 |time|) :
      ‖centeredGenerator (displacement family (baseState+h) (timeSign time*t))-
        jacobian (displacement family (baseState+h) (timeSign time*t))‖ ≤ eta*Q*‖h‖ := by
    have bound := displacement_bound family (baseState+h) initialInside _ (temporal t ht)
    simp only [add_sub_cancel_left] at bound
    have enlarged : ‖displacement family (baseState+h) (timeSign time*t)‖ ≤ Q*‖h‖ :=
      bound.trans (mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) (norm_nonneg h))
    have small : displacement family (baseState+h) (timeSign time*t) ∈ ball (0:State) delta := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt enlarged scaledSmall
    have taylor := remainderSmall small
    exact taylor.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left enlarged (le_of_lt etaPositive))
  have estimate := norm_linearError_le family (baseState+h) initialInside (timeSign time) |time|
    (eta*Q*‖h‖) (timeSign_norm time) (abs_nonneg time) horizonInside remainder
  rw [timeSign_mul_abs] at estimate
  have identity : family.curve (baseState+h) time-family.curve baseState time-linearFlow time h =
      linearError family (baseState+h) time := by
    rw [uniform_background family time inside]
    simp only [linearError, displacement, add_sub_cancel_left]
  rw [identity]
  calc
    _ ≤ gronwallBound 0 growthBound (eta*Q*‖h‖) |time| := estimate
    _ = eta*(amplification family time-1)*‖h‖ := by
      rw [gronwallBound_of_K_ne_0 (ne_of_gt growthBound_positive)]
      dsimp [amplification, Q]
      ring
    _ ≤ eta*amplification family time*‖h‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) (le_of_lt etaPositive)) (norm_nonneg h)
    _ = epsilon*‖h‖ := by
      dsimp [eta]
      rw [div_mul_cancel₀ _ (ne_of_gt (amplification_positive family time))]

theorem initial_fderiv (family : UniformDevelopment baseState) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    fderiv ℝ (fun initial => family.curve initial time) baseState = linearFlow time :=
  (initial_derivative family time inside).fderiv

theorem initial_variation_evolves (family : UniformDevelopment baseState) (direction : State) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    HasDerivAt (fun t => fderiv ℝ (fun initial => family.curve initial t) baseState direction)
      (jacobian (fderiv ℝ (fun initial => family.curve initial time) baseState direction)) time := by
  have neighborhood : ∀ᶠ t in 𝓝 time, t ∈ Ioo (-family.timeRadius) family.timeRadius :=
    isOpen_Ioo.mem_nhds inside
  have equal : (fun t => fderiv ℝ (fun initial => family.curve initial t) baseState direction) =ᶠ[𝓝 time]
      fun t => linearFlow t direction := by
    filter_upwards [neighborhood] with t ht
    rw [initial_fderiv family t ht]
  rw [initial_fderiv family time inside]
  exact (linearFlow_derivative direction time).congr_of_eventuallyEq equal

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation

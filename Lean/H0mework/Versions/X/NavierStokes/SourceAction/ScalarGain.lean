import H0mework.Versions.X.NavierStokes.SourceAction.PositiveTime

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeScalarPositiveTime

open Set Filter MeasureTheory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall

noncomputable section

structure DissipativeWindow (left right viscosity kinetic activityBudget : ℝ) where
  energy : ℕ → ℝ → ℝ
  dissipation : ℕ → ℝ → ℝ
  activity : ℝ → ℝ
  rate : ℕ → ℝ
  ordered : left ≤ right
  viscosity_pos : 0 < viscosity
  kinetic_nonneg : 0 ≤ kinetic
  activityBudget_nonneg : 0 ≤ activityBudget
  rate_nonneg : ∀ order, 0 ≤ rate order
  energy_nonneg : ∀ order time, 0 ≤ energy order time
  dissipation_nonneg : ∀ order time, 0 ≤ dissipation order time
  activity_nonneg : ∀ time, 0 ≤ activity time
  energy_continuous : ∀ order, ContinuousOn (energy order) (Icc left right)
  dissipation_continuous : ∀ order, ContinuousOn (dissipation order) (Icc left right)
  activity_continuous : ContinuousOn activity (Icc left right)
  derivative_continuous : ∀ order, ContinuousOn (deriv (energy order)) (Icc left right)
  differentiable : ∀ order time, time ∈ Icc left right → DifferentiableAt ℝ (energy order) time
  action : ∀ order time, time ∈ Icc left right →
    deriv (energy order) time + viscosity * dissipation order time ≤ rate order * activity time * energy order time
  gain : ∀ order time, energy (order + 1) time ≤ 8 * dissipation order time
  initial_bound : ∀ time, time ∈ Icc left right → energy 0 time ≤ kinetic
  activity_paid : (∫ time in left..right, activity time) ≤ activityBudget

variable {left right viscosity kinetic activityBudget : ℝ}

private theorem activity_integral_le (window : DissipativeWindow left right viscosity kinetic activityBudget)
    {a b : ℝ} (after : left ≤ a) (ordered : a ≤ b) (before : b ≤ right) :
    (∫ time in a..b, window.activity time) ≤ activityBudget :=
  (intervalIntegral.integral_mono_interval after ordered before
    (Eventually.of_forall window.activity_nonneg)
    (ContinuousOn.intervalIntegrable_of_Icc window.ordered window.activity_continuous)).trans window.activity_paid

private theorem propagates (window : DissipativeWindow left right viscosity kinetic activityBudget)
    (order : ℕ) {a b : ℝ} (after : left ≤ a) (ordered : a ≤ b) (before : b ≤ right) :
    window.energy order b ≤ window.energy order a * Real.exp (window.rate order * activityBudget) := by
  have subset : Icc a b ⊆ Icc left right := Icc_subset_Icc after before
  have source := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (fun time inside => (window.differentiable order time (subset inside)).hasDerivAt)
    ((window.activity_continuous.const_mul (window.rate order)).mono subset)
    (fun time inside => le_trans (by
      have positive := mul_nonneg window.viscosity_pos.le (window.dissipation_nonneg order time)
      linarith : deriv (window.energy order) time ≤ deriv (window.energy order) time + viscosity * window.dissipation order time)
      (window.action order time (subset inside))) b ⟨ordered, le_rfl⟩
  rw [intervalIntegral.integral_const_mul] at source
  exact source.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (activity_integral_le window after ordered before)
      (window.rate_nonneg order))) (window.energy_nonneg order a))

private theorem dissipation_integral_le (window : DissipativeWindow left right viscosity kinetic activityBudget)
    (order : ℕ) {a b bound : ℝ} (after : left ≤ a) (ordered : a ≤ b) (before : b ≤ right)
    (boundNonnegative : 0 ≤ bound) (paid : ∀ time ∈ Icc a b, window.energy order time ≤ bound) :
    (∫ time in a..b, window.dissipation order time) ≤ bound * (1 + window.rate order * activityBudget) / viscosity := by
  have subset : Icc a b ⊆ Icc left right := Icc_subset_Icc after before
  have intDerivative := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ordered
    ((window.derivative_continuous order).mono subset)
  have intD := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ordered
    ((window.dissipation_continuous order).mono subset)
  have intA := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ordered (window.activity_continuous.mono subset)
  have pointwise (time : ℝ) (inside : time ∈ Icc a b) :
      deriv (window.energy order) time + viscosity * window.dissipation order time ≤
        (window.rate order * bound) * window.activity time := by
    apply (window.action order time (subset inside)).trans
    have actual := mul_le_mul_of_nonneg_left (paid time inside)
      (mul_nonneg (window.rate_nonneg order) (window.activity_nonneg time))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using actual
  have integrated := intervalIntegral.integral_mono_on ordered
    (intDerivative.add (intD.const_mul viscosity)) (intA.const_mul (window.rate order * bound)) pointwise
  have write : (∫ time in a..b, deriv (window.energy order) time) = window.energy order b - window.energy order a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ intDerivative
    intro time inside
    exact (window.differentiable order time (subset (by simpa only [uIcc_of_le ordered] using inside))).hasDerivAt
  rw [intervalIntegral.integral_add intDerivative (intD.const_mul viscosity),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, write] at integrated
  have total := integrated.trans (mul_le_mul_of_nonneg_left (activity_integral_le window after ordered before)
    (mul_nonneg (window.rate_nonneg order) boundNonnegative))
  apply (le_div_iff₀ window.viscosity_pos).mpr
  have initialLe := paid a ⟨le_rfl, ordered⟩
  have terminalNonnegative := window.energy_nonneg order b
  nlinarith

private theorem exists_next_energy_time (window : DissipativeWindow left right viscosity kinetic activityBudget)
    (order : ℕ) {delta bound : ℝ} (positive : 0 < delta) (fits : left + delta ≤ right)
    (boundNonnegative : 0 ≤ bound)
    (paid : ∀ time ∈ Icc (left + delta / 2) (left + delta), window.energy order time ≤ bound) :
    ∃ selected ∈ Icc (left + delta / 2) (left + delta), window.energy (order + 1) selected ≤
      (8 * (bound * (1 + window.rate order * activityBudget) / viscosity)) / (delta / 2) := by
  have halfPositive := half_pos positive
  have ordered : left + delta / 2 ≤ left + delta := by linarith
  have after : left ≤ left + delta / 2 := by linarith
  have subset : Icc (left + delta / 2) (left + delta) ⊆ Icc left right := Icc_subset_Icc after fits
  have intE := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ordered
    ((window.energy_continuous (order + 1)).mono subset)
  have intD := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) ordered
    ((window.dissipation_continuous order).mono subset)
  have integralLe := intervalIntegral.integral_mono_on ordered intE (intD.const_mul 8)
    (fun time _ => window.gain order time)
  rw [intervalIntegral.integral_const_mul] at integralLe
  have total := integralLe.trans (mul_le_mul_of_nonneg_left
    (dissipation_integral_le window order after ordered fits boundNonnegative paid) (by norm_num))
  obtain ⟨selected, selectedMem, average⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (f := window.energy (order + 1)) (g := fun _ => (1 : ℝ))
    (a := left + delta / 2) (b := left + delta)
    (by simpa only [uIcc_of_le ordered] using (window.energy_continuous (order + 1)).mono subset)
    (intervalIntegrable_const) (fun _ _ => zero_le_one)
  refine ⟨selected, by simpa only [uIcc_of_le ordered] using selectedMem, ?_⟩
  apply (le_div_iff₀ halfPositive).mpr
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at average
  rw [show left + delta - (left + delta / 2) = delta / 2 by ring] at average
  exact average.symm.le.trans total

def positiveBudget (viscosity kinetic activityBudget : ℝ) (rate : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => kinetic
  | order + 1, delta =>
      (8 * (positiveBudget viscosity kinetic activityBudget rate order (delta / 2) *
        (1 + rate order * activityBudget) / viscosity) / (delta / 2)) *
          Real.exp (rate (order + 1) * activityBudget)

theorem positiveBudget_nonnegative (window : DissipativeWindow left right viscosity kinetic activityBudget)
    (order : ℕ) {delta : ℝ} (positive : 0 < delta) :
    0 ≤ positiveBudget viscosity kinetic activityBudget window.rate order delta := by
  induction order generalizing delta with
  | zero => exact window.kinetic_nonneg
  | succ order previous =>
    have lower := previous (half_pos positive)
    have rate := window.rate_nonneg order
    have source := window.activityBudget_nonneg
    have viscosity := window.viscosity_pos
    dsimp only [positiveBudget]
    positivity

theorem energy_bound (window : DissipativeWindow left right viscosity kinetic activityBudget)
    (order : ℕ) (delta : ℝ) (positive : 0 < delta) (fits : left + delta ≤ right)
    (time : ℝ) (inside : time ∈ Icc (left + delta) right) :
    window.energy order time ≤ positiveBudget viscosity kinetic activityBudget window.rate order delta := by
  induction order generalizing delta time with
  | zero => exact window.initial_bound time ⟨by linarith [inside.1], inside.2⟩
  | succ order previous =>
    have halfPositive := half_pos positive
    have halfFits : left + delta / 2 ≤ right := by linarith
    have previousBound : ∀ actual ∈ Icc (left + delta / 2) (left + delta),
        window.energy order actual ≤ positiveBudget viscosity kinetic activityBudget window.rate order (delta / 2) := by
      intro actual actualInside
      exact previous (delta / 2) halfPositive halfFits actual ⟨actualInside.1, actualInside.2.trans fits⟩
    obtain ⟨selected, selectedInside, selectedBound⟩ := exists_next_energy_time window order positive fits
      (positiveBudget_nonnegative window order halfPositive) previousBound
    have propagated := propagates window (order + 1) (by linarith [selectedInside.1])
      (selectedInside.2.trans inside.1) inside.2
    exact propagated.trans (mul_le_mul_of_nonneg_right selectedBound (Real.exp_pos _).le)

end
end SaturationMonoid.NavierStokes.NativeScalarPositiveTime

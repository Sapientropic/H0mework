import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Weighted
import H0mework.Versions.X.NavierStokes.StressNegativeOne.Momentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeResolvent
open NativeWholeH1Mixed NativeWholeH1Pairing NativeUnheatedSourceGradient

noncomputable section
variable {nu : Viscosity}

def nonlinear (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State := by
  classical
  exact if nonnegative : 0 ≤ time then
    if regular : H1 (physical seed time nonnegative) then
      negativeAction (physical seed time nonnegative) (physical seed time nonnegative) regular regular
    else 0
  else 0

theorem nonlinear_original_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, ∀ wave : Wave, nonlinear seed time wave =
      if 0 ≤ time then NativeUnheatedGlobalNegativeOne.rate seed time wave +
        nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) •
          velocity seed time wave) else 0 := by
  filter_upwards [physical_H1_ae seed] with time generated
  intro wave
  by_cases nonnegative : 0 ≤ time
  · have regular := generated nonnegative
    simp only [nonlinear, dif_pos nonnegative, dif_pos regular, if_pos nonnegative,
      NativeUnheatedGlobalNegativeOne.rate, NativeNegativeOneMomentum.momentum,
      lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply]
    change _ = negativeAction (physical seed time nonnegative) (physical seed time nonnegative) regular regular wave -
      nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) • velocity seed time wave) +
        nu.coeff • (Real.sqrt (integerWaveViscousMultiplier wave.1) • velocity seed time wave)
    rw [sub_add_cancel]
  · simp only [nonlinear, dif_neg nonnegative, if_neg nonnegative, lp.coeFn_zero, Pi.zero_apply]

theorem nonlinear_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (nonlinear seed) (volume : Measure ℝ) := by
  have rows (wave : Wave) : AEStronglyMeasurable (fun time => nonlinear seed time wave) (volume : Measure ℝ) := by
    let read := lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave
    have source := (read.continuous.comp_aestronglyMeasurable (NativeUnheatedGlobalNegativeOne.rate_measurable seed)).add
      (((read.continuous.comp_aestronglyMeasurable (velocity_measurable seed)).const_smul
        (Real.sqrt (integerWaveViscousMultiplier wave.1))).const_smul nu.coeff)
    have piece := source.restrict.piecewise (s := Ici (0 : ℝ)) (g := fun _ => (0 : ComplexCoordinateEuclidean))
      measurableSet_Ici aestronglyMeasurable_const
    apply piece.congr
    filter_upwards [nonlinear_original_ae seed] with time same
    exact (same wave).symm
  let part (observed : Finset Wave) (time : ℝ) : State :=
    ∑ wave ∈ observed, lp.single 2 wave (nonlinear seed time wave)
  have measurable (observed : Finset Wave) : AEStronglyMeasurable (part observed) (volume : Measure ℝ) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Wave)) measurable
  exact Eventually.of_forall (fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (nonlinear seed time))

theorem nonlinear_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖nonlinear seed time‖ ≤ Real.sqrt NativeMovingCriticalProductWeights.constant * mass seed time := by
  by_cases nonnegative : 0 ≤ time
  · by_cases regular : H1 (physical seed time nonnegative)
    · rw [nonlinear, dif_pos nonnegative, dif_pos regular]
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (mass_nonnegative seed time))).mp
      rw [mul_pow, Real.sq_sqrt NativeMovingCriticalProductWeights.constant_nonnegative]
      have paid := negativeAction_bound (physical seed time nonnegative) (physical seed time nonnegative) regular regular
      rw [physical_mass] at paid
      exact paid.trans_eq (by ring)
    · rw [nonlinear, dif_pos nonnegative, dif_neg regular, norm_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (mass_nonnegative seed time)
  · rw [nonlinear, dif_neg nonnegative, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (mass_nonnegative seed time)

theorem nonlinear_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (nonlinear seed) (volume.restrict (Icc 0 horizon)) :=
  ((mass_integrable seed horizon nonnegative).const_mul (Real.sqrt NativeMovingCriticalProductWeights.constant)).mono'
    (nonlinear_measurable seed).restrict (Eventually.of_forall (nonlinear_bound seed))

theorem nonlinear_slot_tail_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon, ‖tail radius (nonlinear seed time)‖) atTop (𝓝 0) :=
  integral_tail_tendsto (nonlinear_integrable seed horizon nonnegative)

theorem nonlinear_velocity_tail_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon,
      ‖nonlinear seed time‖ * ‖tail radius (velocity seed time)‖) atTop (𝓝 0) :=
  weighted_tail_tendsto (velocity_measurable seed).restrict (nonlinear_integrable seed horizon nonnegative).norm
    (NativeUnifiedCompleteSource.budget seed) (velocity_bound seed)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail

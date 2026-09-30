import H0mework.NavierStokes.WindowSourcePreparation.Source
import H0mework.NavierStokes.UnheatedWriterPair.IntegralBilinear

set_option autoImplicit false
open scoped Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowPreparationAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeWindowPreparationSource NativeForwardWindowWrite
noncomputable section
variable {nu : Viscosity}

theorem state_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonpositive : time ≤ 0) :
    NativeGlobalHilbertAction.sourceState seed time = NativeGlobalHilbertAction.sourceState seed 0 := by
  rw [← stateCLM_original, complete_nonpositive seed time nonpositive, stateCLM_original]

theorem state_clipped (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    NativeGlobalHilbertAction.sourceState seed time = NativeGlobalHilbertAction.sourceState seed (max time 0) := by
  by_cases positive : 0 ≤ time
  · rw [max_eq_left positive]
  · rw [max_eq_right (le_of_not_ge positive)]
    exact state_nonpositive seed time (le_of_not_ge positive)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ≥0 :=
  ⟨NativeGlobalHilbertAction.sourceBudget seed,
    (norm_nonneg _).trans (NativeGlobalHilbertAction.sourceAction_bound seed 0)⟩

theorem state_lipschitz (seed : GeneratedWholeRestartCurrent nu) :
    LipschitzWith (bound seed) (NativeGlobalHilbertAction.sourceState seed) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  rw [state_clipped seed first, state_clipped seed last]
  have paid := NativeGlobalHilbertAction.sourceState_dist_le seed (max last 0) (max first 0)
    (le_max_right _ _) (le_max_right _ _)
  have clipped : |max first 0-max last 0| ≤ dist first last := by
    simpa only [NNReal.coe_one, one_mul, id_eq, Real.dist_eq] using
      (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul first last
  exact paid.trans (mul_le_mul_of_nonneg_left clipped (bound seed).2)

def action (seed : GeneratedWholeRestartCurrent nu) : ℝ → WholeRestartVelocityEndpointState :=
  (Ioi (0 : ℝ)).indicator (fun time => momentumCLM nu (NativeUnifiedCompleteSource.source seed time))

theorem action_positive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (positive : 0 < time) :
    action seed time = momentumCLM nu (NativeUnifiedCompleteSource.source seed time) :=
  indicator_of_mem positive _

theorem action_nonpositive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonpositive : time ≤ 0) :
    action seed time = 0 := indicator_of_notMem (not_lt.mpr nonpositive) _

theorem action_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (action seed) (volume : Measure ℝ) :=
  ((momentumCLM nu).continuous.comp_aestronglyMeasurable
    (NativeUnifiedCompleteSource.source_measurable seed)).indicator measurableSet_Ioi

theorem action_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖action seed time‖ ≤ ‖momentumCLM nu‖*NativeUnifiedCompleteSource.budget seed := by
  by_cases positive : 0 < time
  · rw [action_positive seed time positive]
    exact ((momentumCLM nu).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed time) (norm_nonneg _))
  · rw [action_nonpositive seed time (le_of_not_gt positive), norm_zero]
    exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (NativeUnifiedCompleteSource.source_bound seed 0))

theorem action_integrable (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    IntervalIntegrable (action seed) volume first last := by
  apply IntegrableOn.intervalIntegrable
  exact IntegrableOn.of_bound (isCompact_uIcc.measure_lt_top (μ := volume)) (action_measurable seed).restrict
    (‖momentumCLM nu‖*NativeUnifiedCompleteSource.budget seed) (Eventually.of_forall (action_bound seed))

theorem state_derivative (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, HasDerivAt (NativeGlobalHilbertAction.sourceState seed) (action seed time) time := by
  filter_upwards [NativeUnifiedCompleteSource.source_hasDerivAt_ae seed, volume.ae_ne (0 : ℝ)] with time actual nonzero
  by_cases positive : 0 < time
  · rw [action_positive seed time positive]
    exact actual positive
  · have negative : time < 0 := lt_of_le_of_ne (le_of_not_gt positive) nonzero
    rw [action_nonpositive seed time negative.le]
    apply (hasDerivAt_const time (NativeGlobalHilbertAction.sourceState seed 0)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds negative] with nearby before
    exact state_nonpositive seed nearby before.le

theorem state_integral (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    NativeGlobalHilbertAction.sourceState seed last-NativeGlobalHilbertAction.sourceState seed first =
      ∫ time in first..last, action seed time := by
  apply NativeUnheatedIntegralBilinear.integral_of_ac_derivative _ _
    (state_lipschitz seed).lipschitzOnWith.absolutelyContinuousOnInterval (action_integrable seed first last)
  filter_upwards [state_derivative seed] with time actual
  exact fun _ => actual

theorem action_correction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    action seed time = momentumCLM nu (NativeUnifiedCompleteSource.source seed time)-
      (Iic (0 : ℝ)).indicator (fun _ => momentumCLM nu (NativeUnifiedCompleteSource.source seed 0)) time := by
  by_cases positive : 0 < time
  · rw [action_positive seed time positive,
      indicator_of_notMem (show time ∉ Iic (0 : ℝ) from not_le.mpr positive), sub_zero]
  · have nonpositive := le_of_not_gt positive
    rw [action_nonpositive seed time nonpositive,
      indicator_of_mem (show time ∈ Iic (0 : ℝ) from nonpositive),
      complete_nonpositive seed time nonpositive, sub_self]

end
end SaturationMonoid.NavierStokes.NativeWindowPreparationAction

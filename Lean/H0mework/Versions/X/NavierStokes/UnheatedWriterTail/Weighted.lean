import H0mework.Versions.X.NavierStokes.UnheatedWriterOne.Rate
import H0mework.NavierStokes.StressEvolutionTemporalVariation.MovingProjection

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeGalerkinMovingProjection
open NativeUnheatedSourceGradient

noncomputable section

def tail (radius : ℕ) (value : State) : State :=
  value - wholeRestartVelocityEndpointGalerkinInitialVelocity radius value

theorem projection_continuous (radius : ℕ) :
    Continuous (wholeRestartVelocityEndpointGalerkinInitialVelocity radius) := by
  have lip : LipschitzWith 1 (wholeRestartVelocityEndpointGalerkinInitialVelocity radius) := by
    apply LipschitzWith.of_dist_le_mul
    intro first last
    simpa only [dist_eq_norm, ← projection_sub, NNReal.coe_one, one_mul] using
      projection_norm_le radius (first - last)
  exact lip.continuous

theorem tail_continuous (radius : ℕ) : Continuous (tail radius) :=
  continuous_id.sub (projection_continuous radius)

theorem tail_norm_bound (radius : ℕ) (value : State) : ‖tail radius value‖ ≤ 2 * ‖value‖ := by
  change ‖value - wholeRestartVelocityEndpointGalerkinInitialVelocity radius value‖ ≤ _
  calc
    _ ≤ ‖value‖ + ‖wholeRestartVelocityEndpointGalerkinInitialVelocity radius value‖ := norm_sub_le _ _
    _ ≤ ‖value‖ + ‖value‖ := by
      have bounded := NativeGalerkinMovingProjection.projection_norm_le radius value
      linarith only [bounded]
    _ = _ := by ring

theorem tail_tendsto (value : State) : Tendsto (fun radius => tail radius value) atTop (𝓝 0) := by
  simpa only [tail, sub_self] using (tendsto_const_nhds (x := value)).sub (wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto value)

theorem integral_tail_tendsto {f : ℝ → State} {μ : Measure ℝ} (integrable : Integrable f μ) :
    Tendsto (fun radius => ∫ time, ‖tail radius (f time)‖ ∂μ) atTop (𝓝 0) := by
  have actual := tendsto_integral_of_dominated_convergence (fun time => 2 * ‖f time‖)
    (fun radius => ((tail_continuous radius).comp_aestronglyMeasurable integrable.aestronglyMeasurable).norm)
    (integrable.norm.const_mul 2)
    (fun radius => Eventually.of_forall (fun time => by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using tail_norm_bound radius (f time)))
    (Eventually.of_forall (fun time => by simpa only [norm_zero] using (tail_tendsto (f time)).norm))
  simpa only [integral_zero] using actual

theorem weighted_tail_tendsto {f : ℝ → State} {weight : ℝ → ℝ} {μ : Measure ℝ}
    (measurable : AEStronglyMeasurable f μ) (paid : Integrable weight μ)
    (cap : ℝ) (bounded : ∀ time, ‖f time‖ ≤ cap) :
    Tendsto (fun radius => ∫ time, weight time * ‖tail radius (f time)‖ ∂μ) atTop (𝓝 0) := by
  have actual := tendsto_integral_of_dominated_convergence (fun time => ‖weight time‖ * (2 * cap))
    (fun radius => paid.aestronglyMeasurable.mul (((tail_continuous radius).comp_aestronglyMeasurable measurable).norm))
    (paid.norm.mul_const (2 * cap))
    (fun radius => Eventually.of_forall (fun time => by
      change ‖weight time * ‖tail radius (f time)‖‖ ≤ _
      rw [norm_mul, Real.norm_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left ((tail_norm_bound radius (f time)).trans
        (mul_le_mul_of_nonneg_left (bounded time) (by norm_num))) (norm_nonneg _)))
    (Eventually.of_forall (fun time => by
      simpa only [Pi.mul_apply, norm_zero, mul_zero] using (tendsto_const_nhds (x := weight time)).mul (tail_tendsto (f time)).norm))
  simpa only [Pi.mul_apply, integral_zero] using! actual

variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State :=
  (NativeUnifiedCompleteSource.source seed time).fst

theorem velocity_measurable (seed : GeneratedWholeRestartCurrent nu) :
    AEStronglyMeasurable (velocity seed) (volume : Measure ℝ) := by
  let read := WithLp.fstL 2 ℝ State NativeCompleteStressCarrier.Space
  change AEStronglyMeasurable (read ∘ NativeUnifiedCompleteSource.source seed) volume
  exact read.continuous.comp_aestronglyMeasurable (NativeUnifiedCompleteSource.source_measurable seed)

theorem velocity_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖velocity seed time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed time)

theorem source_weighted_tail_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon,
      (1 + mass seed time) * ‖tail radius (velocity seed time)‖) atTop (𝓝 0) :=
  weighted_tail_tendsto (velocity_measurable seed).restrict
    ((integrable_const 1).add (mass_integrable seed horizon nonnegative))
    (NativeUnifiedCompleteSource.budget seed) (velocity_bound seed)

theorem source_rate_tail_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon,
      ‖NativeUnheatedGlobalNegativeOne.rate seed time‖ * ‖tail radius (velocity seed time)‖) atTop (𝓝 0) :=
  weighted_tail_tendsto (velocity_measurable seed).restrict
    (NativeUnheatedGlobalNegativeOne.rate_integrable seed horizon nonnegative).norm
    (NativeUnifiedCompleteSource.budget seed) (velocity_bound seed)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceWeightedTail

import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Triangular
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.StrongProduct

/-! A continuous majorant makes the strong source integral norm-continuous, enabling variation of constants. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (B : ℝ → E →L[ℂ] E) (continuousB : ∀ v, Continuous (fun t => B t v))
    (bound : ℝ → ℝ) (continuousBound : Continuous bound) (bounded : ∀ t v, ‖B t v‖≤bound t*‖v‖)

omit [CompleteSpace E] in
theorem insertionOperator_difference (start first second : ℝ) :
    insertionOperator B continuousB bound continuousBound bounded start second-
      insertionOperator B continuousB bound continuousBound bounded start first=
      insertionOperator B continuousB bound continuousBound bounded first second := by
  apply ContinuousLinearMap.ext
  intro v
  change insertionIntegral B start second v-insertionIntegral B start first v=insertionIntegral B first second v
  have relation := intervalIntegral.integral_add_adjacent_intervals
    ((continuousB v).intervalIntegrable (μ := volume) start first)
    ((continuousB v).intervalIntegrable (μ := volume) first second)
  exact sub_eq_iff_eq_add.mpr (relation.symm.trans (add_comm _ _))

omit [CompleteSpace E] in
theorem insertionOperator_norm_bound (start time : ℝ) :
    ‖insertionOperator B continuousB bound continuousBound bounded start time‖≤|∫ r in start..time, bound r| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro v
  exact insertionIntegral_bound B bound continuousBound bounded start time v

omit [CompleteSpace E] in
theorem insertionOperator_continuous (start : ℝ) :
    Continuous (insertionOperator B continuousB bound continuousBound bounded start) := by
  apply continuous_iff_continuousAt.mpr
  intro time
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have derivative := intervalIntegral.integral_hasDerivAt_right
    (continuousBound.intervalIntegrable (μ := volume) time time)
    continuousBound.aestronglyMeasurable.stronglyMeasurableAtFilter continuousBound.continuousAt
  have majorant : Tendsto (fun t => |∫ r in time..t, bound r|) (𝓝 time) (𝓝 0) := by
    have continuousAbs := derivative.continuousAt.abs
    change Tendsto (fun t => |∫ r in time..t, bound r|) (𝓝 time) (𝓝 |∫ r in time..time, bound r|) at continuousAbs
    simpa only [intervalIntegral.integral_same,abs_zero] using continuousAbs
  apply squeeze_zero (fun t => norm_nonneg _)
    (fun t => ?_) majorant
  rw [insertionOperator_difference B continuousB bound continuousBound bounded start time t]
  exact insertionOperator_norm_bound B continuousB bound continuousBound bounded time t

omit [CompleteSpace E] in
theorem strong_operator_product (U : ℝ → E →L[ℂ] E)
    (joint : Continuous (fun tv : ℝ × E => U tv.1 tv.2)) (x : ℝ → E) (v d : E) (time : ℝ)
    (fixed : HasDerivAt (fun t => U t (x time)) d time) (curve : HasDerivAt x v time) :
    HasDerivAt (fun t => U t (x t)) (U time v+d) time := by
  have pair : Tendsto (fun t => (t,slope x time t)) (𝓝[≠] time) (𝓝 (time,v)) := by
    rw [nhds_prod_eq]
    exact ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 time) (𝓝 time)).mono_left nhdsWithin_le_nhds).prodMk curve.tendsto_slope
  have moving : Tendsto (fun t => U t (slope x time t)) (𝓝[≠] time) (𝓝 (U time v)) := by
    have composed := (joint.tendsto (time,v)).comp pair
    simpa only [Function.comp_def] using! composed
  have decomposition (t : ℝ) :
      slope (fun s => U s (x s)) time t=U t (slope x time t)+slope (fun s => U s (x time)) time t := by
    simp only [slope_def_module,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,map_sub]
    module
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact (moving.add fixed.tendsto_slope).congr (fun t => (decomposition t).symm)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing

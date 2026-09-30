import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import H0mework.Versions.X.NavierStokes.UnheatedWriterTail.Weighted
import H0mework.Versions.X.NavierStokes.UnheatedWriterOne.Write

set_option autoImplicit false
open scoped Topology ENNReal BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowTimeIncrementWeight
open Set Filter MeasureTheory
noncomputable section

def translation (shift : ℝ) : C(ℝ,ℝ) := ⟨fun time => time-shift,continuous_id.sub continuous_const⟩

theorem translation_continuous : Continuous translation :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)

theorem translation_preserving (shift : ℝ) : MeasurePreserving (translation shift) volume volume := by
  simpa only [translation,ContinuousMap.coe_mk,sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-shift)

def error (weight : ℝ → ℝ) (shift : ℝ) : ℝ := ∫ time, ‖weight (time-shift)-weight time‖

theorem error_tendsto (weight : ℝ → ℝ) (paid : Integrable weight) :
    Tendsto (error weight) (𝓝 0) (𝓝 0) := by
  let original := paid.toL1 weight
  let moved := fun shift => Lp.compMeasurePreserving (translation shift) (translation_preserving shift) original
  have varying : Continuous moved := continuous_const.compMeasurePreservingLp translation_continuous translation_preserving (by norm_num)
  have read (shift : ℝ) : dist (moved shift) original = error weight shift := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving original (translation_preserving shift),paid.coeFn_toL1,
      (translation_preserving shift).quasiMeasurePreserving.ae paid.coeFn_toL1] with time shifted same source
    simp only [moved,Function.comp_def,translation,ContinuousMap.coe_mk,dist_eq_norm] at shifted source ⊢
    rw [shifted,source,same]
  have actual := (varying.dist (continuous_const (y := original))).tendsto (0 : ℝ)
  simpa only [read,error,sub_zero,sub_self,norm_zero,integral_zero] using! actual

theorem bounded_product_integrable {weight field : ℝ → ℝ} (paid : Integrable weight)
    (measurable : AEStronglyMeasurable field (volume : Measure ℝ)) (cap : ℝ) (bounded : ∀ time, ‖field time‖ ≤ cap) :
    Integrable (fun time => weight time*field time) := by
  apply (paid.norm.mul_const cap).mono' (paid.aestronglyMeasurable.mul measurable)
  filter_upwards with time
  change ‖weight time*field time‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (bounded time) (norm_nonneg _)

theorem shifted_payment {weight field : ℝ → ℝ} (paid : Integrable weight)
    (measurable : AEStronglyMeasurable field (volume : Measure ℝ)) (cap : ℝ) (bounded : ∀ time, ‖field time‖ ≤ cap)
    (shift : ℝ) : |(∫ time, weight time*field (time+shift))-(∫ time, weight time*field time)| ≤ cap*error weight shift := by
  have first := bounded_product_integrable (paid.comp_sub_right shift) measurable cap bounded
  have last := bounded_product_integrable paid measurable cap bounded
  have recenter := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun time => weight (time-shift)*field time) shift
  simp only [add_sub_cancel_right] at recenter
  rw [recenter,← integral_sub first last]
  change ‖∫ time, weight (time-shift)*field time-weight time*field time‖ ≤ _
  apply (norm_integral_le_integral_norm _).trans
  rw [error,← integral_const_mul]
  apply integral_mono (first.sub last).norm (((paid.comp_sub_right shift).sub paid).norm.const_mul cap)
  intro time
  change ‖weight (time-shift)*field time-weight time*field time‖ ≤ cap*‖weight (time-shift)-weight time‖
  rw [← sub_mul,norm_mul]
  exact (mul_le_mul_of_nonneg_left (bounded time) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem relative_absorption (K : ℝ) (coefficient wedge : Fin 3 → ℝ) (cap : ℝ) (positive : 0 ≤ cap)
    (bounded : ∀ j, |coefficient j| ≤ cap) :
    |(1/2 : ℝ)*K*(∑ j : Fin 3, coefficient j*wedge j)| ≤
      (cap/4)*(∑ j : Fin 3, wedge j^2)+(3*cap/4)*K^2 := by
  have per (j : Fin 3) : |(1/2 : ℝ)*K*coefficient j*wedge j| ≤ cap/4*(K^2+wedge j^2) := by
    have product := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bounded j) (abs_nonneg K)) (abs_nonneg (wedge j))
    have square := mul_nonneg positive (sq_nonneg (|K|-|wedge j|))
    rw [sub_sq,sq_abs,sq_abs] at square
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
    nlinarith
  have expanded : (1/2 : ℝ)*K*(∑ j : Fin 3, coefficient j*wedge j) =
      ∑ j : Fin 3, (1/2 : ℝ)*K*coefficient j*wedge j := by rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [expanded]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _ => per j)).trans_eq
  simp only [Fin.sum_univ_three]
  ring

theorem relative_absorption_at (K : ℝ) (coefficient wedge : Fin 3 → ℝ) (viscosity cap : ℝ)
    (positive : 0 < viscosity) (bounded : ∀ j, |coefficient j| ≤ cap) :
    |(1/2 : ℝ)*K*(∑ j : Fin 3, coefficient j*wedge j)| ≤
      (viscosity/4)*(∑ j : Fin 3, wedge j^2)+(3*cap^2/(4*viscosity))*K^2 := by
  have scaled := relative_absorption (cap/viscosity*K) (fun j => viscosity/cap*coefficient j) wedge viscosity positive.le
  by_cases zero : cap = 0
  · have vanish (j) : coefficient j = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [zero] using bounded j) (abs_nonneg _))
    simp only [vanish,zero_mul,Finset.sum_const_zero,mul_zero,abs_zero,zero,zero_pow (by decide : 2 ≠ 0),zero_div,add_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg (wedge j))
  · have capPositive : 0 < cap := lt_of_le_of_ne ((abs_nonneg (coefficient 0)).trans (bounded 0)) (Ne.symm zero)
    have generated := scaled (fun j => by
      rw [abs_mul,abs_of_pos (div_pos positive capPositive)]
      exact (mul_le_mul_of_nonneg_left (bounded j) (div_pos positive capPositive).le).trans_eq (div_mul_cancel₀ _ zero))
    have same : (1/2 : ℝ)*(cap/viscosity*K)*(∑ j : Fin 3, viscosity/cap*coefficient j*wedge j) =
        (1/2 : ℝ)*K*(∑ j : Fin 3, coefficient j*wedge j) := by
      simp only [Fin.sum_univ_three]
      field_simp
    rw [same] at generated
    convert generated using 1
    field_simp

end
end SaturationMonoid.NavierStokes.NativeWindowTimeIncrementWeight

namespace SaturationMonoid.NavierStokes.NativeWindowTimeIncrementSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open NativeResolventCompactness NativeUnheatedSourceWeightedTail NativeUnheatedSourceGradient
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativeEndpointVelocityCarrier NativePhysicalFourier
noncomputable section
variable {nu : Viscosity}

def weight (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ → ℝ :=
  (Icc 0 horizon).indicator (fun time => 1+mass seed time)

theorem weight_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon time : ℝ) : 0 ≤ weight seed horizon time := by
  by_cases inside : time ∈ Icc 0 horizon
  · simp only [weight,indicator_of_mem inside]
    positivity [mass_nonnegative seed time]
  · simp only [weight,indicator_of_notMem inside,le_refl]

theorem weight_integrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (weight seed horizon) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact (integrable_const 1).add (mass_integrable seed horizon nonnegative)

theorem weighted_integral (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (field : ℝ → ℝ) :
    (∫ time, weight seed horizon time*field time) = ∫ time in Icc 0 horizon, (1+mass seed time)*field time := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with time
  by_cases inside : time ∈ Icc 0 horizon <;> simp [weight,inside]

def low (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) : State :=
  wholeRestartVelocityEndpointGalerkinInitialVelocity radius (velocity seed time)

theorem low_continuous (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) : Continuous (low seed radius) := by
  unfold low wholeRestartVelocityEndpointGalerkinInitialVelocity wholeRestartKineticFiniteProjection
  simp only [velocity,NativeUnifiedCompleteSource.velocity_read,NativeAbsoluteEventualControl.velocity]
  apply continuous_finsetSum
  intro wave _
  exact (lp.isometry_single (p := (2 : ℝ≥0∞)) wave).continuous.comp
    (NativeFiniteMacroGlobal.coordinate_continuous (NativeEventualTailControl.terminal seed) wave)

theorem low_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    ‖low seed radius time‖ ≤ NativeUnifiedCompleteSource.budget seed :=
  (NativeGalerkinMovingProjection.projection_norm_le radius _).trans (velocity_bound seed time)

def payment (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ) : ℝ :=
  ∫ time, weight seed horizon time*‖velocity seed (time+shift)-velocity seed time‖

def lowPayment (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon shift : ℝ) : ℝ :=
  ∫ time, weight seed horizon time*‖low seed radius (time+shift)-low seed radius time‖

def tailPayment (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) : ℝ :=
  ∫ time, weight seed horizon time*‖tail radius (velocity seed time)‖

theorem increment_bound (seed : GeneratedWholeRestartCurrent nu) (first last : ℝ) :
    ‖velocity seed first-velocity seed last‖ ≤ 2*NativeUnifiedCompleteSource.budget seed :=
  (norm_sub_le _ _).trans ((add_le_add (velocity_bound seed first) (velocity_bound seed last)).trans_eq (by ring))

theorem low_increment_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (first last : ℝ) :
    ‖low seed radius first-low seed radius last‖ ≤ 2*NativeUnifiedCompleteSource.budget seed :=
  (norm_sub_le _ _).trans ((add_le_add (low_bound seed radius first) (low_bound seed radius last)).trans_eq (by ring))

theorem low_increment_continuous (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (shift : ℝ) :
    Continuous (fun time => low seed radius (time+shift)-low seed radius time) := by
  simpa only [Function.comp_def,Pi.add_def,Pi.sub_def,id_eq] using
    ((low_continuous seed radius).comp (continuous_id.add (continuous_const (y := shift)))).sub (low_continuous seed radius)

theorem low_payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (lowPayment seed radius horizon) (𝓝 0) (𝓝 0) := by
  have measurable (shift : ℝ) : AEStronglyMeasurable
      (fun time => weight seed horizon time*‖low seed radius (time+shift)-low seed radius time‖) (volume : Measure ℝ) :=
    (weight_integrable seed horizon nonnegative).aestronglyMeasurable.mul
      (low_increment_continuous seed radius shift).norm.aestronglyMeasurable
  have actual := tendsto_integral_filter_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun time => weight seed horizon time*(2*NativeUnifiedCompleteSource.budget seed))
    (Eventually.of_forall measurable)
    (Eventually.of_forall fun shift => Eventually.of_forall fun time => by
      rw [norm_mul,Real.norm_of_nonneg (weight_nonnegative seed horizon time),Real.norm_of_nonneg (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (low_increment_bound seed radius (time+shift) time) (weight_nonnegative seed horizon time))
    ((weight_integrable seed horizon nonnegative).mul_const _)
    (Eventually.of_forall fun time => by
      have addition : Tendsto (fun h : ℝ => time+h) (𝓝 0) (𝓝 time) := by
        simpa only [add_zero,id_eq] using (tendsto_const_nhds (x := time)).add (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0))
      have one := ((low_continuous seed radius).tendsto time).comp addition
      simpa only [Function.comp_def,add_zero,sub_self,norm_zero,mul_zero] using (one.sub_const (low seed radius time)).norm.const_mul (weight seed horizon time))
  simpa only [lowPayment,integral_zero] using! actual

theorem tail_payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => tailPayment seed radius horizon) atTop (𝓝 0) := by
  simp only [tailPayment,weighted_integral]
  exact source_weighted_tail_tendsto seed horizon nonnegative

theorem increment_split_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time shift : ℝ) :
    ‖velocity seed (time+shift)-velocity seed time‖ ≤ ‖tail radius (velocity seed (time+shift))‖+
      ‖tail radius (velocity seed time)‖+‖low seed radius (time+shift)-low seed radius time‖ := by
  have exactSplit : velocity seed (time+shift)-velocity seed time =
      (tail radius (velocity seed (time+shift))-tail radius (velocity seed time))+
        (low seed radius (time+shift)-low seed radius time) := by unfold tail low; abel
  have tailBound := norm_sub_le (tail radius (velocity seed (time+shift))) (tail radius (velocity seed time))
  have joint := norm_add_le (tail radius (velocity seed (time+shift))-tail radius (velocity seed time))
    (low seed radius (time+shift)-low seed radius time)
  have same := congrArg norm exactSplit
  linarith only [same,joint,tailBound]

end
end SaturationMonoid.NavierStokes.NativeWindowTimeIncrementSource

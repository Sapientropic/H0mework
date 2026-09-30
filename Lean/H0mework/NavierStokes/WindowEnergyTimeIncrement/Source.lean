import H0mework.NavierStokes.WindowEnergyTimeIncrement.Weight
import H0mework.NavierStokes.UnheatedWriterTail.Weighted
import H0mework.NavierStokes.UnheatedWriterOne.Write
import H0mework.NavierStokes.WindowEnergyCrossHistory.Action

set_option autoImplicit false
open scoped Topology BigOperators ENNReal
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

theorem payment_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon shift : ℝ) (nonnegative : 0 ≤ horizon) :
    payment seed horizon shift ≤ 2*tailPayment seed radius horizon+
      (2*NativeUnifiedCompleteSource.budget seed)*NativeWindowTimeIncrementWeight.error (weight seed horizon) shift+
      lowPayment seed radius horizon shift := by
  have paid := weight_integrable seed horizon nonnegative
  have tailMeas := ((tail_continuous radius).comp_aestronglyMeasurable (velocity_measurable seed)).norm
  have tailBound (time : ℝ) : ‖‖tail radius (velocity seed time)‖‖ ≤ 2*NativeUnifiedCompleteSource.budget seed := by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (tail_norm_bound radius _).trans (mul_le_mul_of_nonneg_left (velocity_bound seed time) (by norm_num))
  have first := NativeWindowTimeIncrementWeight.bounded_product_integrable paid
    (tailMeas.comp_measurePreserving (measurePreserving_add_right volume shift)) _ (fun time => tailBound (time+shift))
  have last := NativeWindowTimeIncrementWeight.bounded_product_integrable paid tailMeas _ tailBound
  have lowInt := NativeWindowTimeIncrementWeight.bounded_product_integrable paid
    (low_increment_continuous seed radius shift).norm.aestronglyMeasurable
    _ (fun time => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using low_increment_bound seed radius (time+shift) time)
  have originalInt := NativeWindowTimeIncrementWeight.bounded_product_integrable paid
    (((velocity_measurable seed).comp_measurePreserving (measurePreserving_add_right volume shift)).sub (velocity_measurable seed)).norm
    _ (fun time => by simpa only [Function.comp_def,Pi.sub_apply,Real.norm_of_nonneg (norm_nonneg _)] using increment_bound seed (time+shift) time)
  have upper := integral_mono originalInt ((first.add last).add lowInt) (fun time => by
    change weight seed horizon time*‖velocity seed (time+shift)-velocity seed time‖ ≤
      weight seed horizon time*‖tail radius (velocity seed (time+shift))‖+weight seed horizon time*‖tail radius (velocity seed time)‖+
        weight seed horizon time*‖low seed radius (time+shift)-low seed radius time‖
    rw [← mul_add,← mul_add]
    apply mul_le_mul_of_nonneg_left _ (weight_nonnegative seed horizon time)
    exact increment_split_bound seed radius time shift)
  rw [integral_add' (first.add last) lowInt,integral_add' first last] at upper
  have transfer := NativeWindowTimeIncrementWeight.shifted_payment paid tailMeas _ tailBound shift
  have one := (le_abs_self _).trans transfer
  change _-tailPayment seed radius horizon ≤ _ at one
  change payment seed horizon shift ≤ _ at upper
  unfold lowPayment tailPayment at *
  simp only [Function.comp_def] at upper
  linarith only [upper,one]

theorem payment_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ) : 0 ≤ payment seed horizon shift :=
  integral_nonneg fun time => mul_nonneg (weight_nonnegative seed horizon time) (norm_nonneg _)

theorem payment_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (payment seed horizon) (𝓝 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  obtain ⟨radius,small⟩ := ((tail_payment_tendsto seed horizon nonnegative).eventually
    (Iio_mem_nhds (show (0 : ℝ) < epsilon/4 by linarith))).exists
  have translated := NativeWindowTimeIncrementWeight.error_tendsto (weight seed horizon) (weight_integrable seed horizon nonnegative)
  have bounded := ((tendsto_const_nhds (x := 2*tailPayment seed radius horizon)).add
    (translated.const_mul (2*NativeUnifiedCompleteSource.budget seed))).add (low_payment_tendsto seed radius horizon nonnegative)
  have smallLimit : 2*tailPayment seed radius horizon+(2*NativeUnifiedCompleteSource.budget seed)*0+0 < epsilon := by
    linarith
  filter_upwards [bounded.eventually (Iio_mem_nhds smallLimit)] with shift nearby
  rw [dist_eq_norm,sub_zero,Real.norm_of_nonneg (payment_nonnegative seed horizon shift)]
  exact (payment_bound seed radius horizon shift nonnegative).trans_lt nearby

theorem projected_payment_le (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon shift : ℝ)
    (nonnegative : 0 ≤ horizon) : lowPayment seed radius horizon shift ≤ payment seed horizon shift := by
  have sourceMeas := (((velocity_measurable seed).comp_measurePreserving (measurePreserving_add_right volume shift)).sub
    (velocity_measurable seed)).norm
  have originalInt := NativeWindowTimeIncrementWeight.bounded_product_integrable (weight_integrable seed horizon nonnegative)
    sourceMeas _ (fun time => by simpa only [Function.comp_def,Pi.sub_apply,Real.norm_of_nonneg (norm_nonneg _)] using increment_bound seed (time+shift) time)
  have projectedInt := NativeWindowTimeIncrementWeight.bounded_product_integrable (weight_integrable seed horizon nonnegative)
    (low_increment_continuous seed radius shift).norm.aestronglyMeasurable _
    (fun time => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using low_increment_bound seed radius (time+shift) time)
  apply integral_mono projectedInt originalInt
  intro time
  apply mul_le_mul_of_nonneg_left _ (weight_nonnegative seed horizon time)
  change ‖wholeRestartVelocityEndpointGalerkinInitialVelocity radius (velocity seed (time+shift))-
    wholeRestartVelocityEndpointGalerkinInitialVelocity radius (velocity seed time)‖ ≤ ‖velocity seed (time+shift)-velocity seed time‖
  rw [← NativeGalerkinMovingProjection.projection_sub]
  exact NativeGalerkinMovingProjection.projection_norm_le radius _

theorem exists_uniform_projected_payment (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ)
    (nonnegative : 0 ≤ horizon) (positive : 0 < epsilon) :
    ∀ᶠ shift in 𝓝 (0 : ℝ), ∀ radius : ℕ, lowPayment seed radius horizon shift < epsilon := by
  filter_upwards [(payment_tendsto seed horizon nonnegative).eventually (Iio_mem_nhds positive)] with shift small radius
  exact (projected_payment_le seed radius horizon shift nonnegative).trans_lt small

theorem velocity_polynomial (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (coordinate : Coordinate) (point : Torus) : NativeWindowCrossHistoryAction.velocity seed F time coordinate point =
      (∑ wave ∈ F, wholeVelocity (velocity seed time) wave coordinate*UnitAddTorus.mFourier wave point).re := by
  rw [NativeWindowCrossHistoryAction.velocity,NativeWindowStressHeatTime.field_original]
  simp only [NativeWindowFiniteGramFourier.read,NativeWindowFiniteGramFourier.complexRead,
    ContinuousLinearMap.comp_apply,sum_apply]
  change ((∑ wave ∈ F, NativeForwardWindowPairingReadout.velocityRead wave coordinate
    (NativeUnifiedCompleteSource.source seed time) • UnitAddTorus.mFourier wave) point).re = _
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rfl

theorem low_advector_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector)
    (first last : ℝ) (coordinate : Coordinate) (point : Torus) :
    |NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) first coordinate point-
      NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) last coordinate point| ≤
        (wholeRestartModes radius).card*‖low seed radius first-low seed radius last‖ := by
  have row (wave : IntegerWavevector) (inside : wave ∈ wholeRestartModes radius) (time : ℝ) :
      wholeVelocity (low seed radius time) wave coordinate = wholeVelocity (velocity seed time) wave coordinate := by
    by_cases zero : wave = 0
    · subst wave; simp
    · rw [wholeVelocity_nonzero _ ⟨wave,zero⟩,wholeVelocity_nonzero _ ⟨wave,zero⟩,
        low,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,if_pos inside]
  rw [velocity_polynomial,velocity_polynomial,← Complex.sub_re,← Finset.sum_sub_distrib]
  apply (Complex.abs_re_le_norm _).trans
  have perWave (wave : IntegerWavevector) (inside : wave ∈ F ∩ wholeRestartModes radius) :
      ‖wholeVelocity (velocity seed first) wave coordinate*UnitAddTorus.mFourier wave point-
        wholeVelocity (velocity seed last) wave coordinate*UnitAddTorus.mFourier wave point‖ ≤
          ‖low seed radius first-low seed radius last‖ := by
    rw [← row wave (Finset.mem_inter.mp inside).2 first,← row wave (Finset.mem_inter.mp inside).2 last,← sub_mul,norm_mul]
    have linear : wholeVelocity (low seed radius first-low seed radius last) wave coordinate =
        wholeVelocity (low seed radius first) wave coordinate-wholeVelocity (low seed radius last) wave coordinate := by
      change (wholeVelocityCLM (low seed radius first-low seed radius last)) wave coordinate = _
      rw [map_sub,lp.coeFn_sub]
      rfl
    rw [← linear]
    have coefficient := (norm_le_pi_norm (wholeVelocity (low seed radius first-low seed radius last) wave) coordinate).trans
      ((lp.norm_apply_le_norm (by norm_num) _ wave).trans (wholeVelocity_norm_le (low seed radius first-low seed radius last)))
    have character : ‖UnitAddTorus.mFourier wave point‖ ≤ 1 :=
      (UnitAddTorus.mFourier wave).norm_coe_le_norm point |>.trans_eq UnitAddTorus.mFourier_norm
    exact (mul_le_mul coefficient character (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  calc
    _ ≤ ∑ wave ∈ F ∩ wholeRestartModes radius, ‖wholeVelocity (velocity seed first) wave coordinate*UnitAddTorus.mFourier wave point-
        wholeVelocity (velocity seed last) wave coordinate*UnitAddTorus.mFourier wave point‖ := norm_sum_le _ _
    _ ≤ ∑ _wave ∈ F ∩ wholeRestartModes radius, ‖low seed radius first-low seed radius last‖ := Finset.sum_le_sum perWave
    _ ≤ (wholeRestartModes radius).card*‖low seed radius first-low seed radius last‖ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : F ∩ wholeRestartModes radius ⊆ _)) (norm_nonneg _)

theorem exists_uniform_low_advector (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon epsilon : ℝ)
    (positive : 0 < epsilon) : ∃ delta > 0, ∀ first ∈ Icc 0 horizon, ∀ last ∈ Icc 0 horizon,
      dist first last < delta → ∀ F : Finset IntegerWavevector, ∀ coordinate : Coordinate, ∀ point : Torus,
      |NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) first coordinate point-
        NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) last coordinate point| < epsilon := by
  let C : ℝ := (wholeRestartModes radius).card+1
  have Cp : 0 < C := by dsimp [C]; positivity
  obtain ⟨delta,dp,small⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (low_continuous seed radius).continuousOn) (epsilon/C) (div_pos positive Cp)
  refine ⟨delta,dp,fun first firstIn last lastIn near F coordinate point => ?_⟩
  have close := small first firstIn last lastIn near
  rw [dist_eq_norm] at close
  have product := (mul_lt_mul_of_pos_left close Cp).trans_eq (mul_div_cancel₀ epsilon Cp.ne')
  exact (low_advector_bound seed radius F first last coordinate point).trans_lt
    ((mul_le_mul_of_nonneg_right (show ((wholeRestartModes radius).card : ℝ) ≤ C by dsimp [C]; linarith) (norm_nonneg _)).trans_lt product)

open NativeWindowCrossHistoryAction in
theorem exists_low_relative_absorption (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) :
    ∃ delta > 0, ∀ first ∈ Icc 0 horizon, ∀ last ∈ Icc 0 horizon, dist first last < delta →
      ∀ F : Finset IntegerWavevector, ∀ point : Torus,
      let v := NativeWindowCrossHistoryAction.velocity seed F first
      let w := NativeWindowCrossHistoryAction.velocity seed F last
      let d := wedge v w (gradient seed F first) (gradient seed F last)
      |(1/2 : ℝ)*pair v w point*(∑ j : Coordinate,
        (NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) first j point-
          NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) last j point)*d j point)| ≤
        (nu.coeff/4)*(∑ j : Coordinate, (d j point)^2)+(3*nu.coeff/4)*(pair v w point)^2 := by
  obtain ⟨delta,positive,source⟩ := exists_uniform_low_advector seed radius horizon nu.coeff nu.coeff_pos
  refine ⟨delta,positive,fun first firstIn last lastIn nearby F point => ?_⟩
  exact NativeWindowTimeIncrementWeight.relative_absorption _ _ _ _ nu.coeff_pos.le
    (fun j => (source first firstIn last lastIn nearby F j point).le)

theorem payment_original (seed : GeneratedWholeRestartCurrent nu) (horizon shift : ℝ) :
    payment seed horizon shift = ∫ time in Icc 0 horizon, (1+mass seed time)*
      ‖NativeAbsoluteEventualControl.velocity seed (time+shift)-NativeAbsoluteEventualControl.velocity seed time‖ := by
  rw [payment,weighted_integral]
  simp only [velocity,NativeUnifiedCompleteSource.velocity_read]

open NativeWindowCrossHistoryAction in
theorem relative_split (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (F : Finset IntegerWavevector) (first last : ℝ) :
    let v := NativeWindowCrossHistoryAction.velocity seed F first
    let w := NativeWindowCrossHistoryAction.velocity seed F last
    let a := NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) first
    let b := NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) last
    let d := wedge v w (gradient seed F first) (gradient seed F last)
    increment v w (gradient seed F first) (gradient seed F last) =
      (∑ j : Coordinate, (a j-b j)*d j)+(∑ j : Coordinate, ((v j-a j)-(w j-b j))*d j) := by
  dsimp only
  rw [increment,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime in
theorem difference_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    velocity seed (step.2.clockAdvance+first)-velocity seed (step.2.clockAdvance+last) =
      velocity step.1 first-velocity step.1 last := by
  simp only [velocity,NativeUnifiedCompleteSource.source_generated_next seed step generated first first0,
    NativeUnifiedCompleteSource.source_generated_next seed step generated last last0]

def lowCap (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) : ℝ :=
  (wholeRestartModes radius).card*(2*NativeUnifiedCompleteSource.budget seed)

open NativeWindowCrossHistoryAction in
theorem low_relative_absorption (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (first last : ℝ)
    (F : Finset IntegerWavevector) (point : Torus) :
    let v := NativeWindowCrossHistoryAction.velocity seed F first
    let w := NativeWindowCrossHistoryAction.velocity seed F last
    let d := wedge v w (gradient seed F first) (gradient seed F last)
    |(1/2 : ℝ)*pair v w point*(∑ j : Coordinate,
      (NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) first j point-
        NativeWindowCrossHistoryAction.velocity seed (F ∩ wholeRestartModes radius) last j point)*d j point)| ≤
      (nu.coeff/4)*(∑ j : Coordinate, (d j point)^2)+(3*lowCap seed radius^2/(4*nu.coeff))*(pair v w point)^2 := by
  apply NativeWindowTimeIncrementWeight.relative_absorption_at _ _ _ _ _ nu.coeff_pos
  intro j
  exact (low_advector_bound seed radius F first last j point).trans
    (mul_le_mul_of_nonneg_left (low_increment_bound seed radius first last) (Nat.cast_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeWindowTimeIncrementSource

import H0mework.NavierStokes.WindowEnergyApproximation.Source
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowFiniteStressUniform
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressCarrier NativeCompleteStressAction NativeForwardWindowJets NativeWindowFiniteStressConvergence
open NativeWindowSobolevStress (quarter)
noncomputable section
variable {nu : Viscosity}

def kernelBound (order : ℕ) : ℝ := 1+Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order)
theorem kernelBound_positive (order : ℕ) : 0 < kernelBound order := by unfold kernelBound; positivity

theorem kernel_bounded (order : ℕ) (shift : ℝ) : ‖kernelJet order shift‖ ≤ kernelBound order := by
  by_cases zero : kernelJet order shift=0
  · rw [zero,norm_zero]; exact (kernelBound_positive order).le
  have square := NativeUnheatedWindowGradient.kernel_square_le order shift (NativeUnheatedWindowJensen.kernel_support order shift zero)
  have bound : ‖kernelJet order shift‖ ≤ Real.sqrt (NativeUnheatedWindowGradient.kernelCeiling order) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs,sq_abs] using square
  exact bound.trans (by unfold kernelBound; linarith)

def average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) (field : ℝ → E) : E :=
  ∫ sample in Icc 0 (horizon+2), kernelJet order (time-sample) • field sample

theorem average_original {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) (inside : time ∈ Icc 0 horizon) (field : ℝ → E) :
    average order time horizon field = ∫ shift, kernelJet order shift • field (time-shift) := by
  rw [average,setIntegral_eq_integral_of_forall_compl_eq_zero (fun sample outside => ?_)]
  · have changed := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).integral_comp
      (measurableEmbedding_subLeft time) (fun sample => kernelJet order (time-sample) • field sample)
    simpa only [sub_sub_cancel] using changed.symm
  · have zero : kernelJet order (time-sample)=0 := by
      by_contra nonzero
      have support := NativeUnheatedWindowJensen.kernel_support order (time-sample) nonzero
      exact outside ⟨by linarith [inside.1,support.2],by linarith [inside.2,support.1]⟩
    rw [zero,zero_smul]

theorem average_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) {field : ℝ → E} (paid : Integrable field (volume.restrict (Icc 0 (horizon+2)))) :
    Integrable (fun sample => kernelJet order (time-sample) • field sample) (volume.restrict (Icc 0 (horizon+2))) :=
  paid.bdd_smul (kernelBound order) (((kernelJet_smooth order).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun sample => kernel_bounded order (time-sample))

def window (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) : Space :=
  ∫ shift, kernelJet order shift • finiteAt seed (integerWaveFrequencyCube radius) (time-shift)

theorem window_original (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) : window seed radius order time =
      average order time horizon (finiteAt seed (integerWaveFrequencyCube radius)) :=
  (average_original order time horizon inside _).symm

theorem source_average (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) : average order time horizon (source seed) =
      NativeWindowSobolevStress.state seed order time (by linarith [inside.1]) := by
  have positive : 0 ≤ horizon+2 := by linarith [inside.1,inside.2]
  have integrable := average_integrable order time horizon (source_integrable seed (horizon+2) positive)
  have original : average order time horizon (NativeUnifiedCompleteSource.source seed) = jet seed order time :=
    average_original order time horizon inside _
  have paidFull : Integrable (NativeUnifiedCompleteSource.source seed) (volume.restrict (Icc 0 (horizon+2))) :=
    (memLp_one_iff_integrable).mp (NativeUnifiedCompleteSource.source_Lp seed 1 isCompact_Icc).1
  have originalPaid := average_integrable order time horizon paidFull
  apply lp.ext
  funext wave
  let observed := lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  let readOriginal : FullSpace →L[ℝ] Tensor := (weightedRead wave).comp
    (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  change observed (average order time horizon (source seed)) = _
  rw [average,← observed.integral_comp_comm integrable]
  calc
    _ = ∫ sample in Icc 0 (horizon+2), readOriginal (kernelJet order (time-sample) • NativeUnifiedCompleteSource.source seed sample) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (source_row_ae seed),ae_restrict_mem measurableSet_Icc] with sample actual member
      simp only [map_smul]
      change kernelJet order (time-sample) • source seed sample wave = _
      rw [actual member.1 wave]
      congr 1
      ext entry
      change quarter wave • ((weight wave)⁻¹ • (NativeUnifiedCompleteSource.source seed sample).snd wave entry) = _
      simp only [readOriginal,weightedRead,ContinuousLinearMap.comp_apply,smul_apply,WithLp.sndL_apply,mul_smul]
      rfl
    _ = readOriginal (jet seed order time) := by rw [readOriginal.integral_comp_comm originalPaid,← average,original]
    _ = _ := by
      ext entry
      change (quarter wave*(weight wave)⁻¹) • (jet seed order time).snd wave entry =
        quarter wave • ((weight wave)⁻¹ • (jet seed order time).snd wave entry)
      exact mul_smul _ _ _

def error (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) : ℝ :=
  ∫ sample in Icc 0 (horizon+2), ‖finiteAt seed (integerWaveFrequencyCube radius) sample-source seed sample‖

theorem error_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => error seed radius horizon) atTop (𝓝 0) := by
  have actual := tendsto_integral_of_dominated_convergence
    (fun sample => 2*cap*NativeUnheatedSourceGradient.mass seed sample)
    (fun radius => ((finiteAt_continuous seed (integerWaveFrequencyCube radius)).aestronglyMeasurable.sub
      (source_measurable seed (horizon+2))).norm)
    ((NativeUnheatedSourceGradient.mass_integrable seed (horizon+2) (by linarith)).const_mul (2*cap))
    (fun radius => by
      filter_upwards [ae_restrict_of_ae (source_bound_ae seed),ae_restrict_mem measurableSet_Icc] with sample bound member
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans ((add_le_add ((bound member.1).2 _) (bound member.1).1).trans_eq (by ring)))
    (by
      filter_upwards [ae_restrict_of_ae (source_tendsto_ae seed),ae_restrict_mem measurableSet_Icc] with sample limit member
      exact tendsto_iff_norm_sub_tendsto_zero.mp (limit member.1))
  simpa only [error,integral_zero,Pi.sub_apply] using actual

theorem error_bound (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) :
    ‖window seed radius order time-NativeWindowSobolevStress.state seed order time (by linarith [inside.1])‖ ≤
      kernelBound order*error seed radius horizon := by
  have positive : 0 ≤ horizon+2 := by linarith [inside.1,inside.2]
  have left : Integrable (finiteAt seed (integerWaveFrequencyCube radius)) (volume.restrict (Icc 0 (horizon+2))) :=
    (finiteAt_continuous seed (integerWaveFrequencyCube radius)).integrableOn_Icc
  have right := source_integrable seed (horizon+2) positive
  rw [window_original seed radius order time horizon inside,← source_average seed order time horizon inside,
    average,average,← integral_sub (average_integrable order time horizon left) (average_integrable order time horizon right)]
  apply (norm_integral_le_integral_norm _).trans
  rw [error,← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact (left.sub right).norm.const_mul (kernelBound order)
  · filter_upwards with sample
    rw [← smul_sub,norm_smul]
    exact mul_le_mul_of_nonneg_right (kernel_bounded order (time-sample)) (norm_nonneg _)

theorem uniform_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    TendstoUniformly (fun radius => fun time : Icc (0 : ℝ) horizon => window seed radius order time)
      (fun time => NativeWindowSobolevStress.state seed order time (by linarith [time.property.1])) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  have limit : Tendsto (fun radius => kernelBound order*error seed radius horizon) atTop (𝓝 0) := by
    simpa only [mul_zero] using (error_tendsto seed horizon nonnegative).const_mul (kernelBound order)
  filter_upwards [limit.eventually (gt_mem_nhds positive)] with radius small time
  rw [dist_comm,dist_eq_norm]
  exact (error_bound seed radius order time horizon time.property).trans_lt small

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) : ‖window seed radius order time‖ ≤
      kernelBound order*cap*NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (horizon+2) := by
  have positive : 0 ≤ horizon+2 := by linarith [inside.1,inside.2]
  rw [window_original seed radius order time horizon inside,average]
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => kernelJet order (time-sample) • finiteAt seed (integerWaveFrequencyCube radius) sample)
    ((NativeUnheatedSourceGradient.mass_integrable seed (horizon+2) positive).const_mul (kernelBound order*cap))
    (by
      filter_upwards [ae_restrict_of_ae (source_bound_ae seed),ae_restrict_mem measurableSet_Icc] with sample bound member
      rw [norm_smul]
      exact (mul_le_mul (kernel_bounded order (time-sample)) ((bound member.1).2 (integerWaveFrequencyCube radius))
        (norm_nonneg _) (kernelBound_positive order).le).trans_eq (by ring))
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (NativeUnheatedSourceGradient.mass_integral_bound seed (horizon+2) positive)
    (mul_nonneg (kernelBound_positive order).le cap_nonnegative))

theorem window_row (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) : window seed radius order time wave =
      ∫ shift, kernelJet order shift • (quarter wave • tensor
        (read (NativeUnheatedWindowStress.finiteStress seed (integerWaveFrequencyCube radius) (time-shift)) wave)) := by
  let observed := lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  have paid : Integrable (finiteAt seed (integerWaveFrequencyCube radius)) (volume.restrict (Icc 0 (time+2))) :=
    (finiteAt_continuous seed (integerWaveFrequencyCube radius)).integrableOn_Icc
  change observed (window seed radius order time) = _
  rw [window_original seed radius order time time ⟨nonnegative,le_rfl⟩,average,
    ← observed.integral_comp_comm (average_integrable order time time paid)]
  have actual (sample : ℝ) : observed (kernelJet order (time-sample) • finiteAt seed (integerWaveFrequencyCube radius) sample) =
      kernelJet order (time-sample) • (quarter wave • tensor
        (read (NativeUnheatedWindowStress.finiteStress seed (integerWaveFrequencyCube radius) sample) wave)) := by
    rw [map_smul]
    congr 1
    rw [show observed (finiteAt seed (integerWaveFrequencyCube radius) sample) = finiteAt seed (integerWaveFrequencyCube radius) sample wave by rfl,
      finiteAt_row]
    ext entry
    change (quarter wave*(weight wave)⁻¹) • (NativeUnheatedWindowStress.finiteStress seed (integerWaveFrequencyCube radius) sample wave entry) =
      quarter wave • ((weight wave)⁻¹ • (NativeUnheatedWindowStress.finiteStress seed (integerWaveFrequencyCube radius) sample wave entry))
    exact mul_smul _ _ _
  simp_rw [actual]
  exact average_original order time time ⟨nonnegative,le_rfl⟩ _

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem window_next (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    window seed radius order (step.2.clockAdvance+time) = window step.1 radius order time := by
  unfold window
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : kernelJet order shift=0
  · rw [zero,zero_smul,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    congr 1
    rw [finiteAt,finiteAt,← NativeUnifiedCompleteSource.velocity_read,← NativeUnifiedCompleteSource.velocity_read,
      add_sub_assoc,NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith [support.2])]

end
end SaturationMonoid.NavierStokes.NativeWindowFiniteStressUniform

import H0mework.Versions.X.NavierStokes.WindowSourceSobolev.PreparationSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Convolution
namespace SaturationMonoid.NavierStokes.NativeWindowPreparedSobolevWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressCarrier NativeCompleteStressAction NativeForwardWindowJets
open NativeWindowFiniteStressConvergence (source finiteAt weightedRead)
open NativeWindowFiniteStressUniform (window kernelBound kernelBound_positive kernel_bounded)
open NativeWindowPreparedSobolevSource (envelope source_bound_ae source_tendsto_ae source_measurable source_integrable finiteAt_integrable envelope_integrable)
open NativeWindowSobolevStress (quarter)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section

def average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) (field : ℝ → E) : E :=
  ∫ sample in Icc (-1 : ℝ) (horizon+2), kernelJet order (time-sample) • field sample

theorem average_original {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) (field : ℝ → E) :
    average order time horizon field = ∫ shift, kernelJet order shift • field (time-shift) := by
  rw [average,setIntegral_eq_integral_of_forall_compl_eq_zero (fun sample outside => ?_)]
  · have changed := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).integral_comp
      (measurableEmbedding_subLeft time) (fun sample => kernelJet order (time-sample) • field sample)
    simpa only [sub_sub_cancel] using changed.symm
  · have zero : kernelJet order (time-sample) = 0 := by
      by_contra nonzero
      have support := NativeUnheatedWindowJensen.kernel_support order (time-sample) nonzero
      exact outside ⟨by linarith [inside.1,support.2],by linarith [inside.2,support.1]⟩
    rw [zero,zero_smul]

theorem average_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (time horizon : ℝ) {field : ℝ → E}
    (paid : Integrable field (volume.restrict (Icc (-1 : ℝ) (horizon+2)))) :
    Integrable (fun sample => kernelJet order (time-sample) • field sample)
      (volume.restrict (Icc (-1 : ℝ) (horizon+2))) :=
  paid.bdd_smul (kernelBound order) (((kernelJet_smooth order).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun sample => kernel_bounded order (time-sample))

def complete (order : ℕ) (time : ℝ) : Space :=
  ∫ shift, kernelJet order shift • source stackedShortCurrent (time-shift)

theorem complete_average (order : ℕ) (time horizon : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    complete order time = average order time horizon (source stackedShortCurrent) :=
  (average_original order time horizon inside _).symm

theorem window_average (radius order : ℕ) (time horizon : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    window stackedShortCurrent radius order time =
      average order time horizon (finiteAt stackedShortCurrent (integerWaveFrequencyCube radius)) :=
  (average_original order time horizon inside _).symm

theorem complete_row (order : ℕ) (time : ℝ) (valid : -2 ≤ time) (wave : IntegerWavevector) :
    complete order time wave = quarter wave • tensor (read (jet stackedShortCurrent order time).snd wave) := by
  let horizon := max time 0
  have inside : time ∈ Icc (-2 : ℝ) horizon := ⟨valid,le_max_left _ _⟩
  have positive : 0 ≤ horizon := le_max_right _ _
  have integrable := average_integrable order time horizon (source_integrable horizon positive)
  have original : average order time horizon (NativeUnifiedCompleteSource.source stackedShortCurrent) =
      jet stackedShortCurrent order time := average_original order time horizon inside _
  have paidFull : Integrable (NativeUnifiedCompleteSource.source stackedShortCurrent)
      (volume.restrict (Icc (-1 : ℝ) (horizon+2))) :=
    (memLp_one_iff_integrable).mp (NativeUnifiedCompleteSource.source_Lp stackedShortCurrent 1 isCompact_Icc).1
  have originalPaid := average_integrable order time horizon paidFull
  let observed := lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  let readOriginal : FullSpace →L[ℝ] Tensor := (weightedRead wave).comp
    (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState Space)
  change observed (complete order time) = _
  rw [complete_average order time horizon inside,average,← observed.integral_comp_comm integrable]
  calc
    _ = ∫ sample in Icc (-1 : ℝ) (horizon+2),
        readOriginal (kernelJet order (time-sample) • NativeUnifiedCompleteSource.source stackedShortCurrent sample) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae NativeWindowPreparedSobolevSource.source_row_ae] with sample actual
      simp only [map_smul]
      change kernelJet order (time-sample) • source stackedShortCurrent sample wave = _
      rw [actual wave]
      congr 1
      ext entry
      change quarter wave • ((weight wave)⁻¹ • (NativeUnifiedCompleteSource.source stackedShortCurrent sample).snd wave entry) = _
      simp only [readOriginal,weightedRead,ContinuousLinearMap.comp_apply,smul_apply,WithLp.sndL_apply,mul_smul]
      rfl
    _ = readOriginal (jet stackedShortCurrent order time) := by
      rw [readOriginal.integral_comp_comm originalPaid,← average,original]
    _ = _ := by
      ext entry
      change (quarter wave*(weight wave)⁻¹) • (jet stackedShortCurrent order time).snd wave entry =
        quarter wave • ((weight wave)⁻¹ • (jet stackedShortCurrent order time).snd wave entry)
      exact mul_smul _ _ _

theorem complete_existing (order : ℕ) (time : ℝ) (valid : -1 ≤ time) :
    complete order time = NativeWindowSobolevStress.state stackedShortCurrent order time valid := by
  apply lp.ext
  funext wave
  rw [complete_row order time (by linarith) wave]
  apply PiLp.ext
  intro entry
  exact (NativeWindowSobolevStress.state_row stackedShortCurrent order time valid wave entry.1 entry.2).symm

def error (radius : ℕ) (horizon : ℝ) : ℝ := ∫ sample in Icc (-1 : ℝ) (horizon+2),
  ‖finiteAt stackedShortCurrent (integerWaveFrequencyCube radius) sample-source stackedShortCurrent sample‖

theorem error_tendsto (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => error radius horizon) atTop (𝓝 0) := by
  have actual := tendsto_integral_of_dominated_convergence (fun sample => 2*envelope sample)
    (fun radius => ((NativeWindowFiniteStressConvergence.finiteAt_continuous stackedShortCurrent
      (integerWaveFrequencyCube radius)).aestronglyMeasurable.sub source_measurable.restrict).norm)
    ((envelope_integrable horizon nonnegative).const_mul 2)
    (fun radius => by
      filter_upwards [ae_restrict_of_ae source_bound_ae] with sample bound
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans ((add_le_add (bound.2 _) bound.1).trans_eq (by ring)))
    (by
      filter_upwards [ae_restrict_of_ae source_tendsto_ae] with sample limit
      exact tendsto_iff_norm_sub_tendsto_zero.mp limit)
  simpa only [error,integral_zero,Pi.sub_apply] using actual

theorem window_error_bound (radius order : ℕ) (time horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (inside : time ∈ Icc (-2 : ℝ) horizon) :
    ‖window stackedShortCurrent radius order time-complete order time‖ ≤ kernelBound order*error radius horizon := by
  have left := finiteAt_integrable horizon nonnegative (integerWaveFrequencyCube radius)
  have right := source_integrable horizon nonnegative
  rw [window_average radius order time horizon inside,complete_average order time horizon inside,
    average,average,← integral_sub (average_integrable order time horizon left) (average_integrable order time horizon right)]
  apply (norm_integral_le_integral_norm _).trans
  rw [error,← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact (left.sub right).norm.const_mul (kernelBound order)
  · filter_upwards with sample
    rw [← smul_sub,norm_smul]
    exact mul_le_mul_of_nonneg_right (kernel_bounded order (time-sample)) (norm_nonneg _)

theorem uniform_tendsto (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    TendstoUniformly (fun radius => fun time : Icc (-2 : ℝ) horizon => window stackedShortCurrent radius order time)
      (fun time => complete order time) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  have limit : Tendsto (fun radius => kernelBound order*error radius horizon) atTop (𝓝 0) := by
    simpa only [mul_zero] using (error_tendsto horizon nonnegative).const_mul (kernelBound order)
  filter_upwards [limit.eventually (gt_mem_nhds positive)] with radius small time
  rw [dist_comm,dist_eq_norm]
  exact (window_error_bound radius order time horizon nonnegative time.property).trans_lt small

def budget (order : ℕ) (horizon : ℝ) : ℝ := kernelBound order*∫ sample in Icc (-1 : ℝ) (horizon+2), envelope sample

theorem complete_bound (order : ℕ) (time horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (inside : time ∈ Icc (-2 : ℝ) horizon) : ‖complete order time‖ ≤ budget order horizon := by
  rw [complete_average order time horizon inside,average]
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => kernelJet order (time-sample) • source stackedShortCurrent sample)
    ((envelope_integrable horizon nonnegative).const_mul (kernelBound order)) (by
      filter_upwards [ae_restrict_of_ae source_bound_ae] with sample bound
      rw [norm_smul]
      exact mul_le_mul (kernel_bounded order (time-sample)) bound.1 (norm_nonneg _) (kernelBound_positive order).le)
  simpa only [integral_const_mul,budget] using paid

theorem window_bound (radius order : ℕ) (time horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (inside : time ∈ Icc (-2 : ℝ) horizon) : ‖window stackedShortCurrent radius order time‖ ≤ budget order horizon := by
  rw [window_average radius order time horizon inside,average]
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => kernelJet order (time-sample) • finiteAt stackedShortCurrent (integerWaveFrequencyCube radius) sample)
    ((envelope_integrable horizon nonnegative).const_mul (kernelBound order)) (by
      filter_upwards [ae_restrict_of_ae source_bound_ae] with sample bound
      rw [norm_smul]
      exact mul_le_mul (kernel_bounded order (time-sample)) (bound.2 _) (norm_nonneg _) (kernelBound_positive order).le)
  simpa only [integral_const_mul,budget] using paid

theorem window_row (radius order : ℕ) (time : ℝ) (valid : -2 ≤ time) (wave : IntegerWavevector) :
    window stackedShortCurrent radius order time wave =
      ∫ shift, kernelJet order shift • (quarter wave • tensor
        (read (NativeUnheatedWindowStress.finiteStress stackedShortCurrent (integerWaveFrequencyCube radius) (time-shift)) wave)) := by
  let horizon := max time 0
  have inside : time ∈ Icc (-2 : ℝ) horizon := ⟨valid,le_max_left _ _⟩
  let observed := lp.evalCLM ℝ (fun _ : IntegerWavevector => Tensor) 2 wave
  have paid := average_integrable order time horizon
    (finiteAt_integrable horizon (le_max_right _ _) (integerWaveFrequencyCube radius))
  change observed (window stackedShortCurrent radius order time) = _
  rw [window_average radius order time horizon inside,average,← observed.integral_comp_comm paid]
  have actual (sample : ℝ) :
      observed (kernelJet order (time-sample) • finiteAt stackedShortCurrent (integerWaveFrequencyCube radius) sample) =
        kernelJet order (time-sample) • (quarter wave • tensor
          (read (NativeUnheatedWindowStress.finiteStress stackedShortCurrent (integerWaveFrequencyCube radius) sample) wave)) := by
    rw [map_smul]
    congr 1
    rw [show observed (finiteAt stackedShortCurrent (integerWaveFrequencyCube radius) sample) =
      finiteAt stackedShortCurrent (integerWaveFrequencyCube radius) sample wave by rfl,
      NativeWindowFiniteStressConvergence.finiteAt_row]
    ext entry
    change (quarter wave*(weight wave)⁻¹) •
        (NativeUnheatedWindowStress.finiteStress stackedShortCurrent (integerWaveFrequencyCube radius) sample wave entry) =
      quarter wave • ((weight wave)⁻¹ •
        (NativeUnheatedWindowStress.finiteStress stackedShortCurrent (integerWaveFrequencyCube radius) sample wave entry))
    exact mul_smul _ _ _
  simp_rw [actual]
  exact average_original order time horizon inside _

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem complete_next (order : ℕ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep RationalVorticityEvaluator.butterflyGainViscosity) stackedShortCurrent)
    (generated : generatedWholeRestartEndpointMacroRespond stackedShortCurrent = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    complete order (response.2.clockAdvance+time) =
      NativeWindowSobolevStress.state response.1 order time (by linarith) := by
  have shifted : -1 ≤ response.2.clockAdvance+time := by linarith [response.2.clockAdvance_pos]
  rw [complete_existing order _ shifted]
  exact NativeWindowSobolevStress.state_next stackedShortCurrent order response generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeWindowPreparedSobolevWindow

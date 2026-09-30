import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedTemporalWork
import H0mework.Versions.X.NavierStokes.WindowEnergyCutoffHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedForcingDefect
open Set Filter MeasureTheory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
noncomputable section

theorem average_defect_norm_bound (radius : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    (∫shift,‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius (time-shift)‖
      ∂NativeForwardWindowPairingReadout.averageMeasure) ≤
      NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound 0*
        NativeWindowPreparedSobolevWindow.error radius horizon := by
  let F := integerWaveFrequencyCube radius
  rw [NativeForwardWindowPairingReadout.density_integral]
  change (∫shift,NativeForwardWindowJets.kernelJet 0 shift •
    ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius (time-shift)‖) ≤ _
  rw [← NativeWindowPreparedSobolevWindow.average_original 0 time horizon inside
    (fun sample => ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖)]
  change (∫sample in Icc (-1 : ℝ) (horizon+2),
    NativeForwardWindowJets.kernelJet 0 (time-sample) •
      ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖) ≤ _
  have left := NativeWindowPreparedSobolevSource.finiteAt_integrable horizon nonnegative F
  have right := NativeWindowPreparedSobolevSource.source_integrable horizon nonnegative
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => NativeForwardWindowJets.kernelJet 0 (time-sample) •
      ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖)
    ((left.sub right).norm.const_mul
      (NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound 0)) (by
      filter_upwards with sample
      simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero,norm_smul,
        Real.norm_of_nonneg (NativeForwardWindowSource.kernel_nonnegative _),
        Real.norm_of_nonneg (norm_nonneg _)]
      change NativeForwardWindowSource.kernel (time-sample)*
        ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖ ≤
        (NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound 0)*
          ‖NativeWindowFiniteStressConvergence.finiteAt stackedShortCurrent F sample-
            NativeWindowFiniteStressConvergence.source stackedShortCurrent sample‖
      have defect := NativeWindowCutoffHalfSource.defect_bound stackedShortCurrent radius sample
      have kernelBound : NativeForwardWindowSource.kernel (time-sample) ≤
          NativeWindowFiniteStressUniform.kernelBound 0 := by
        simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero,
          Real.norm_of_nonneg (NativeForwardWindowSource.kernel_nonnegative _)] using
          NativeWindowFiniteStressUniform.kernel_bounded 0 (time-sample)
      have bounded := mul_le_mul kernelBound defect
        (norm_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive 0).le
      have identity : NativeWindowFiniteStressUniform.kernelBound 0*
          (NativeWindowCutoffHalfAction.cap*
            ‖NativeWindowFiniteStressConvergence.finiteAt stackedShortCurrent F sample-
              NativeWindowFiniteStressConvergence.source stackedShortCurrent sample‖) =
          (NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound 0)*
            ‖NativeWindowFiniteStressConvergence.finiteAt stackedShortCurrent F sample-
              NativeWindowFiniteStressConvergence.source stackedShortCurrent sample‖ := by ring
      exact bounded.trans_eq identity)
  have nonnegativeIntegral : 0 ≤ (∫sample in Icc (-1 : ℝ) (horizon+2),
      NativeForwardWindowJets.kernelJet 0 (time-sample) •
        ‖NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖) := by
    apply integral_nonneg
    intro sample
    simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero,smul_eq_mul]
    exact mul_nonneg (NativeForwardWindowSource.kernel_nonnegative _) (norm_nonneg _)
  rw [Real.norm_of_nonneg nonnegativeIntegral] at paid
  simpa only [Pi.sub_apply,integral_const_mul,NativeWindowPreparedSobolevWindow.error,mul_assoc] using paid

theorem window_bound (radius order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (time : ℝ) (inside : time ∈ Icc (-2 : ℝ) horizon) :
    ‖NativeWindowCutoffHalfSource.window stackedShortCurrent radius order time‖ ≤
      NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound order*
        NativeWindowPreparedSobolevWindow.error radius horizon := by
  let F := integerWaveFrequencyCube radius
  change ‖∫shift,NativeForwardWindowJets.kernelJet order shift •
    NativeWindowCutoffHalfSource.defect stackedShortCurrent radius (time-shift)‖ ≤ _
  rw [← NativeWindowPreparedSobolevWindow.average_original order time horizon inside]
  change ‖∫sample in Icc (-1 : ℝ) (horizon+2),
    NativeForwardWindowJets.kernelJet order (time-sample) •
      NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample‖ ≤ _
  have left := NativeWindowPreparedSobolevSource.finiteAt_integrable horizon nonnegative F
  have right := NativeWindowPreparedSobolevSource.source_integrable horizon nonnegative
  have paid := norm_integral_le_of_norm_le
    (f := fun sample : ℝ => NativeForwardWindowJets.kernelJet order (time-sample) •
      NativeWindowCutoffHalfSource.defect stackedShortCurrent radius sample)
    ((left.sub right).norm.const_mul
      (NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound order)) (by
      filter_upwards with sample
      rw [norm_smul]
      have defect := NativeWindowCutoffHalfSource.defect_bound stackedShortCurrent radius sample
      exact (mul_le_mul (NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)) defect
        (norm_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive order).le).trans_eq
          (by simp only [Pi.sub_apply]; ring))
  simpa only [Pi.sub_apply,integral_const_mul,NativeWindowPreparedSobolevWindow.error,mul_assoc] using paid

theorem window_uniform_tendsto (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    TendstoUniformly
      (fun radius => fun time : Icc (-2 : ℝ) horizon =>
        NativeWindowCutoffHalfSource.window stackedShortCurrent radius order time)
      (fun _ => (0 : NativeResolventCompactness.State)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  have limit : Tendsto (fun radius =>
      NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound order*
        NativeWindowPreparedSobolevWindow.error radius horizon) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (NativeWindowPreparedSobolevWindow.error_tendsto horizon nonnegative).const_mul
        (NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressUniform.kernelBound order)
  filter_upwards [limit.eventually (gt_mem_nhds positive)] with radius small time
  rw [dist_comm,dist_zero_right]
  exact (window_bound radius order horizon nonnegative time time.property).trans_lt small

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedForcingDefect

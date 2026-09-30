import H0mework.NavierStokes.WindowHistoryOseen.Equation
import H0mework.NavierStokes.WindowEnergyCutoffHalf.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForcing
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeResolventCompactness NativeWholeResolvent NativePhysicalPairing NativeResolventAdjoint
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeEndpointVelocityCarrier
open NativeWindowTraceWholeHistory (H)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def test (M : ℕ) (v : physicalSpace (modes M)) : State →L[ℝ] ℝ :=
  ∑ k∈modes M,∑ i : Coordinate,(innerSL ℝ (v.1 k i)).comp (NativeUnheatedHalfNonlinear.decode k i)

theorem test_apply (M : ℕ) (v : physicalSpace (modes M)) (data : State) : test M v data=
    ∑ k∈modes M,∑ i : Coordinate,inner ℝ (NativeUnheatedHalfNonlinear.decode k i data) (v.1 k i) := by
  simp only [test,sum_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm]

private theorem projected_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    wholeVelocity (NativeWholeH1Approximation.project M (NativeUnheatedSourceQuadraticApprox.physicalSource seed time)).1=
      complexSharpSupportProjection (integerWaveFrequencyCube M) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := by
  rw [NativeWholeH1Approximation.project_whole]
  apply lp.ext
  funext k
  rw [NativeWholeH1Mixed.restrict_row,complexSharpSupportProjection_apply,
    NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
  by_cases zero : k=0
  · subst k
    simp only [wholeVelocity_zero]
    split_ifs <;> rfl
  · simp only [modes,ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget.puncturedIntegerWaveFrequencyCube,
      Finset.mem_erase,ne_eq,zero,not_false_eq_true,true_and]
    rfl

private theorem quadratic_decode (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (k : IntegerWavevector) (k0 : k≠0) (i : Coordinate) :
    NativeUnheatedTriadRows.decode k i (NativeUnheatedSourceQuadraticApprox.value M seed time)=
      NativeTimeJetCarrier.projectedDivergenceCLM k (NativeHigherTimeJets.mixedFlux
        (complexSharpSupportProjection (integerWaveFrequencyCube M) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst))
        (complexSharpSupportProjection (integerWaveFrequencyCube M) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)) k) i := by
  rw [NativeUnheatedTriadRows.decode_apply,wholeVelocity_nonzero _ ⟨k,k0⟩]
  change NativeUnheatedPairNegativeKernel.root k •
    ((NativeUnheatedPairNegativeKernel.root k)⁻¹ • NativeWholeH1Mixed.row
      (NativeWholeH1Approximation.project M (NativeUnheatedSourceQuadraticApprox.physicalSource seed time))
      (NativeWholeH1Approximation.project M (NativeUnheatedSourceQuadraticApprox.physicalSource seed time)) k i)=_
  rw [smul_smul,mul_inv_cancel₀ (NativeUnheatedPairNegativeKernel.root_positive k k0).ne',one_smul]
  change NativeTimeJetCarrier.projectedDivergenceCLM k (NativeHigherTimeJets.mixedFlux _ _ k) i=_
  rw [projected_source seed M time nonnegative]

theorem forcing_pairing (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ,0 ≤ time →∀ M,∀ v : physicalSpace (modes M),
      pairing (modes M) (NativeWindowStageNineSource.forcing seed M time) v=
        test M v (NativeWindowCutoffHalfSource.defect seed M time) := by
  filter_upwards [NativeWindowCutoffHalfSource.defect_original_ae seed] with time defect nonnegative M v
  rw [NativeWindowStageNineSource.forcing,NativeWindowStageNineSource.lift_pairing,test_apply]
  apply Finset.sum_congr rfl
  intro k member
  apply Finset.sum_congr rfl
  intro i _
  have covered : k ∈ wholeRestartModes M := by
    simpa only [modes,wholeRestartModes] using member
  rw [map_sub,defect nonnegative M k i,if_pos covered]
  rw [quadratic_decode seed M time nonnegative k (fun zero => modes_zero M (zero ▸ member)) i]
  rfl

theorem test_window (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (v : physicalSpace (modes M)) :
    test M v (NativeWindowCutoffHalfSource.window seed M order time)=
      ∫ lag,NativeForwardWindowJets.kernelJet order lag • test M v (NativeWindowCutoffHalfSource.defect seed M (time-lag)) := by
  have paid := NativeWindowFiniteStressUniform.average_integrable order time time
    (NativeWindowCutoffHalfSource.defect_integrable seed M (time+2) (by linarith))
  rw [NativeWindowCutoffHalfSource.window,← NativeWindowFiniteStressUniform.average_original order time time ⟨nonnegative,le_rfl⟩]
  have read := (test M v).integral_comp_comm paid
  change test M v (∫ sample in Icc 0 (time+2),NativeForwardWindowJets.kernelJet order (time-sample) •
    NativeWindowCutoffHalfSource.defect seed M sample)=_
  rw [← read]
  simp only [map_smul]
  exact NativeWindowFiniteStressUniform.average_original order time time ⟨nonnegative,le_rfl⟩ _

theorem history_pairing (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0 ≤ time) (v : physicalSpace (modes M)) :
    inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v))
      (NativeWindowHistoryOseen.forcingHistory seed M time)=test M v (NativeWindowCutoffHalfSource.window seed M 0 time) := by
  have source := (withDensity_absolutelyContinuous volume (fun lag => (NativeForwardWindowPairingReadout.density lag : ℝ≥0∞))).ae_le
    ((Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (forcing_pairing seed))
  have actual : (fun lag => inner ℝ
      (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v) lag)
      (NativeWindowHistoryOseen.forcingHistory seed M time lag)) =ᵐ[averageMeasure]
      fun lag => test M v (NativeWindowCutoffHalfSource.defect seed M (time-lag)) := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae (includeCLM (modes M) (modes_closed M) v),
      NativeWindowHistoryOseen.forcingHistory_ae seed M time,source,NativeWindowTraceEndpointWindow.average_interval]
      with lag fixed force original support
    have sample0 : 0 ≤ time-lag := by linarith [support.2]
    rw [fixed,force,NativeWindowHistoryOseen.forcingValue_original seed M (time-lag) sample0,
      include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include,pairing_symmetric]
    exact original sample0 M v
  have integralRead : (∫ lag,test M v (NativeWindowCutoffHalfSource.defect seed M (time-lag)) ∂averageMeasure)=
      test M v (NativeWindowCutoffHalfSource.window seed M 0 time) :=
    (NativeForwardWindowPairingReadout.density_integral _).trans (test_window seed M 0 time nonnegative v).symm
  exact (L2.inner_def (𝕜 := ℝ) _ _).trans ((integral_congr_ae actual).trans integralRead)

theorem source_effect_small (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∀ M ≥ low,∀ time ∈ Icc 0 horizon,∀ v : physicalSpace (modes M),
      |inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v))
        (NativeWindowHistoryOseen.forcingHistory seed M time)| ≤ epsilon*‖test M v‖ := by
  have small := Metric.tendstoUniformly_iff.mp (NativeWindowCutoffHalfSource.window_uniform_tendsto seed 0 horizon nonnegative) epsilon positive
  obtain ⟨low,paid⟩ := eventually_atTop.mp small
  refine ⟨low,fun M above time inside v => ?_⟩
  have normSmall : ‖NativeWindowCutoffHalfSource.window seed M 0 time‖ ≤ epsilon := by
    simpa only [dist_zero_left] using (paid M above ⟨time,inside⟩).le
  rw [history_pairing seed M time inside.1,← Real.norm_eq_abs]
  exact ((test M v).le_opNorm _).trans ((mul_le_mul_of_nonneg_left normSmall (norm_nonneg (test M v))).trans_eq (mul_comm _ _))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem effect_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : physicalSpace (modes M))
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v))
      (NativeWindowHistoryOseen.forcingHistory seed M (step.2.clockAdvance+time))=
    inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v))
      (NativeWindowHistoryOseen.forcingHistory step.1 M time) :=
  congrArg (fun h : H => inner ℝ (NativeWindowTraceWholeHistory.constant (includeCLM (modes M) (modes_closed M) v)) h)
    (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanForcing

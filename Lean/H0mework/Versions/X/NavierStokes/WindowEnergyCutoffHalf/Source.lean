import H0mework.Versions.X.NavierStokes.WindowEnergyCutoffHalf.Action
import H0mework.Versions.X.NavierStokes.WindowEnergyApproximation.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowCutoffHalfSource
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open NativeResolventCompactness NativeEndpointVelocityCarrier NativeWholeH1Mixed
open NativeWindowCutoffHalfAction NativeGalerkinMovingProjection
open NativeWindowFiniteStressConvergence NativeWindowFiniteStressUniform
noncomputable section
variable {nu : Viscosity}

def finiteAction (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) : State :=
  actionCLM (finiteAt seed (integerWaveFrequencyCube radius) time)

def completeAction (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : State := actionCLM (source seed time)

def defect (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) : State :=
  wholeRestartVelocityEndpointGalerkinInitialVelocity radius (completeAction seed time-finiteAction seed radius time)

theorem complete_existing_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → completeAction seed time = NativeUnheatedHalfNonlinear.source seed time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative
  have h := regular nonnegative
  have hp : NativeUnheatedStressProduct.H1 (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) := h
  have generated := (full_existing (NativeUnheatedSourceGradient.physical seed time nonnegative) h).trans
    (NativeUnheatedHalfNonlinear.source_ofPhysical seed time nonnegative h).symm
  simpa only [completeAction,source,dif_pos hp] using! generated

theorem finite_decode (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedHalfNonlinear.decode wave coordinate (finiteAction seed radius time) =
      NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux
        (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst))
        (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)) wave) coordinate := by
  rw [finiteAction,finiteAt,finite_read,NativeUnifiedCompleteSource.velocity_read]

theorem projection_decode (radius : ℕ) (value : State) (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedHalfNonlinear.decode wave coordinate (wholeRestartVelocityEndpointGalerkinInitialVelocity radius value) =
      if wave ∈ wholeRestartModes radius then NativeUnheatedHalfNonlinear.decode wave coordinate value else 0 := by
  by_cases zero : wave=0
  · subst wave
    simp [NativeUnheatedHalfNonlinear.decode,NativeUnheatedHalfNonlinear.quarter,NativeUnheatedPairNegativeKernel.root,
      integerWaveViscousMultiplier,integerWaveNormSq]
  · change NativeUnheatedHalfNonlinear.quarter wave • wholeVelocity (wholeRestartVelocityEndpointGalerkinInitialVelocity radius value) wave coordinate = _
    rw [wholeVelocity_nonzero _ ⟨wave,zero⟩,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
    split_ifs with inside
    · change NativeUnheatedHalfNonlinear.quarter wave • value ⟨wave,zero⟩ coordinate =
        NativeUnheatedHalfNonlinear.quarter wave • wholeVelocity value wave coordinate
      rw [wholeVelocity_nonzero _ ⟨wave,zero⟩]
    · change NativeUnheatedHalfNonlinear.quarter wave • (0:ℂ) = 0
      exact smul_zero _

theorem defect_original_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ radius wave coordinate,
      NativeUnheatedHalfNonlinear.decode wave coordinate (defect seed radius time) =
        if wave ∈ wholeRestartModes radius then NativeUnheatedTriadRows.action seed time wave coordinate-
          NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux
            (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst))
            (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)) wave) coordinate
        else 0 := by
  filter_upwards [complete_existing_ae seed] with time original nonnegative radius wave coordinate
  rw [defect,projection_decode,map_sub,original nonnegative,NativeUnheatedHalfNonlinear.decode_source,finite_decode]

theorem defect_bound (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (time : ℝ) :
    ‖defect seed radius time‖ ≤ NativeWindowCutoffHalfAction.cap*‖finiteAt seed (integerWaveFrequencyCube radius) time-source seed time‖ := by
  apply (projection_norm_le radius _).trans
  change ‖actionCLM (source seed time)-actionCLM (finiteAt seed (integerWaveFrequencyCube radius) time)‖ ≤ _
  rw [← map_sub]
  exact (action_bound _).trans_eq (by rw [norm_sub_rev])

theorem defect_measurable (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) :
    AEStronglyMeasurable (defect seed radius) (volume.restrict (Icc 0 horizon)) :=
  (NativeUnheatedSourceWeightedTail.projection_continuous radius).comp_aestronglyMeasurable
    ((actionCLM.continuous.comp_aestronglyMeasurable (source_measurable seed horizon)).sub
      (actionCLM.continuous.comp_aestronglyMeasurable (finiteAt_continuous seed (integerWaveFrequencyCube radius)).aestronglyMeasurable.restrict))

theorem defect_domination_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ radius, ‖defect seed radius time‖ ≤
      (2*NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressConvergence.cap)*NativeUnheatedSourceGradient.mass seed time := by
  filter_upwards [source_bound_ae seed] with time bound nonnegative radius
  apply (defect_bound seed radius time).trans
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) cap_positive.le).trans
  have paid := mul_le_mul_of_nonneg_left (add_le_add ((bound nonnegative).2 (integerWaveFrequencyCube radius))
    (bound nonnegative).1) cap_positive.le
  exact paid.trans_eq (by ring)

theorem defect_integrable (seed : GeneratedWholeRestartCurrent nu) (radius : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Integrable (defect seed radius) (volume.restrict (Icc 0 horizon)) := by
  apply ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul
    (2*NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressConvergence.cap)).mono' (defect_measurable seed radius horizon)
  filter_upwards [ae_restrict_of_ae (defect_domination_ae seed),ae_restrict_mem measurableSet_Icc] with time bound inside
  exact bound inside.1 radius

theorem defect_tendsto_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → Tendsto (fun radius => defect seed radius time) atTop (𝓝 0) := by
  filter_upwards [source_tendsto_ae seed] with time actual nonnegative
  apply squeeze_zero_norm (fun radius => defect_bound seed radius time)
  simpa only [sub_self,norm_zero,mul_zero] using
    (((actual nonnegative).sub_const (source seed time)).norm.const_mul NativeWindowCutoffHalfAction.cap)

theorem defect_integral_tendsto (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun radius => ∫ time in Icc 0 horizon, ‖defect seed radius time‖) atTop (𝓝 0) := by
  have generated := tendsto_integral_of_dominated_convergence
    (fun time => (2*NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressConvergence.cap)*NativeUnheatedSourceGradient.mass seed time)
    (fun radius => (defect_measurable seed radius horizon).norm)
    ((NativeUnheatedSourceGradient.mass_integrable seed horizon nonnegative).const_mul (2*NativeWindowCutoffHalfAction.cap*NativeWindowFiniteStressConvergence.cap))
    (fun radius => by
      filter_upwards [ae_restrict_of_ae (defect_domination_ae seed),ae_restrict_mem measurableSet_Icc] with time bound inside
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using bound inside.1 radius)
    (by
      filter_upwards [ae_restrict_of_ae (defect_tendsto_ae seed),ae_restrict_mem measurableSet_Icc] with time actual inside
      simpa only [norm_zero] using (actual inside.1).norm)
  simpa only [integral_zero] using generated

def window (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) : State :=
  ∫ shift, NativeForwardWindowJets.kernelJet order shift • defect seed radius (time-shift)

theorem window_bound (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time horizon : ℝ)
    (inside : time ∈ Icc 0 horizon) : ‖window seed radius order time‖ ≤
      kernelBound order*(∫ sample in Icc 0 (horizon+2), ‖defect seed radius sample‖) := by
  have paid := defect_integrable seed radius (horizon+2) (by linarith [inside.1,inside.2])
  rw [window,← average_original order time horizon inside,NativeWindowFiniteStressUniform.average]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (average_integrable order time horizon paid).norm (paid.norm.const_mul (kernelBound order))
  filter_upwards with sample
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (kernel_bounded order (time-sample)) (norm_nonneg _)

theorem window_uniform_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    TendstoUniformly (fun radius => fun time : Icc (0:ℝ) horizon => window seed radius order time) (fun _ => (0:State)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon positive
  have limit : Tendsto (fun radius => kernelBound order*(∫ sample in Icc 0 (horizon+2), ‖defect seed radius sample‖)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (defect_integral_tendsto seed (horizon+2) (by linarith)).const_mul (kernelBound order)
  filter_upwards [limit.eventually (gt_mem_nhds positive)] with radius small time
  rw [dist_comm,dist_zero_right]
  exact (window_bound seed radius order time horizon time.property).trans_lt small

theorem window_original (seed : GeneratedWholeRestartCurrent nu) (radius order : ℕ) (time : ℝ) (nonnegative : 0 ≤ time)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    NativeUnheatedHalfNonlinear.decode wave coordinate (window seed radius order time) =
      ∫ sample in Icc 0 (time+2), NativeForwardWindowJets.kernelJet order (time-sample) •
        (if wave ∈ wholeRestartModes radius then NativeUnheatedTriadRows.action seed sample wave coordinate-
          NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux
            (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst))
            (complexSharpSupportProjection (integerWaveFrequencyCube radius) (wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst)) wave) coordinate else 0) := by
  have paid := average_integrable order time time (defect_integrable seed radius (time+2) (by linarith))
  rw [window,← average_original order time time ⟨nonnegative,le_rfl⟩,NativeWindowFiniteStressUniform.average,
    ← (NativeUnheatedHalfNonlinear.decode wave coordinate).integral_comp_comm paid]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (defect_original_ae seed),ae_restrict_mem measurableSet_Icc] with sample original inside
  rw [map_smul,original inside.1]

open SourceGeneratedNativeResponseDisposition
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem complete_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    completeAction seed (step.2.clockAdvance+time) = completeAction step.1 time := by
  classical
  have actual := NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative
  exact congrArg (fun state : NativeCompleteStressAction.FullSpace => actionCLM
    (if regular : NativeUnheatedStressProduct.H1 (wholeVelocity state.fst) then full state.fst regular else 0)) actual

theorem finite_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) (radius : ℕ) :
    finiteAction seed radius (step.2.clockAdvance+time) = finiteAction step.1 radius time := by
  have actual := congrArg (fun state : NativeCompleteStressAction.FullSpace => actionCLM (finite state.fst (integerWaveFrequencyCube radius)))
    (NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative)
  simpa only [finiteAction,finiteAt,NativeUnifiedCompleteSource.velocity_read] using! actual

theorem defect_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) (radius : ℕ) :
    defect seed radius (step.2.clockAdvance+time) = defect step.1 radius time := by
  rw [defect,defect,complete_next seed step generated time nonnegative,finite_next seed step generated time nonnegative radius]

theorem window_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) (radius order : ℕ) :
    window seed radius order (step.2.clockAdvance+time) = window step.1 radius order time := by
  unfold window
  apply integral_congr_ae
  filter_upwards with shift
  by_cases zero : NativeForwardWindowJets.kernelJet order shift=0
  · rw [zero,zero_smul,zero_smul]
  · have support := NativeUnheatedWindowJensen.kernel_support order shift zero
    rw [show step.2.clockAdvance+time-shift=step.2.clockAdvance+(time-shift) by ring,
      defect_next seed step generated (time-shift) (by linarith [support.2]) radius]

end
end SaturationMonoid.NavierStokes.NativeWindowCutoffHalfSource

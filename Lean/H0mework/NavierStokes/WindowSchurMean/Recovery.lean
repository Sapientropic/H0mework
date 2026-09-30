import H0mework.NavierStokes.WindowSchurMean.ForceResolution

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanRecovery
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory history)
open NativeWindowHistoryMeanForceResolution (error resolved)
noncomputable section
variable {nu : Viscosity}

theorem mean_norm_le (v : H) : ‖mean v‖≤‖v‖ := by
  have paid:=NativeWindowHistoryMeanProjection.energy_split v
  have read:‖NativeWindowHistoryMeanProjection.projection v‖=‖mean v‖ :=
    NativeWindowHistoryMeanProjection.embed_norm (mean v)
  rw [read] at paid
  exact (sq_le_sq₀ (norm_nonneg (mean v)) (norm_nonneg v)).mp (by
    linarith only [paid,sq_nonneg ‖NativeWindowHistoryMeanProjection.residual v‖])

theorem source_error_norm (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0≤horizon) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,‖error seed M time‖≤epsilon := by
  obtain ⟨low,paid⟩:=NativeWindowHistoryMeanForceResolution.source_error_small seed horizon nonnegative
    (epsilon^2) (sq_pos_of_pos positive)
  refine ⟨low,fun M above time inside => ?_⟩
  have mass:‖error seed M time‖^2≤NativeWindowHistorySchurTemporalControl.energy nu M (error seed M time) :=
    le_add_of_nonneg_right (mul_nonneg nu.coeff_pos.le
      (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (error seed M time)))
  exact (sq_le_sq₀ (norm_nonneg (error seed M time)) positive.le).mp (mass.trans (paid M above time inside))

theorem source_mean_error_norm (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (nonnegative : 0≤horizon) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∀ M≥low,∀ time∈Icc 0 horizon,‖mean (error seed M time)‖≤epsilon := by
  obtain ⟨low,paid⟩:=source_error_norm seed horizon nonnegative epsilon positive
  exact ⟨low,fun M above time inside => (mean_norm_le _).trans (paid M above time inside)⟩

theorem source_error_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    Tendsto (fun M => error seed M time) atTop (𝓝 (0 : H)) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon positive
  obtain ⟨low,paid⟩:=source_error_norm seed time nonnegative (epsilon/2) (half_pos positive)
  exact ⟨low,fun M above => by
    rw [dist_zero_right (E := H)]
    exact (paid M above time ⟨nonnegative,le_rfl⟩).trans_lt (half_lt_self positive)⟩

theorem finite_mean_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun M => (mean (finiteHistory seed time M)).1) atTop
      (𝓝 (NativeForwardWindowSource.source seed time).fst) := by
  have original:=wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto
    (NativeForwardWindowSource.source seed time).fst
  simpa only [NativeWindowHistoryMeanTime.source_mean,NativeWindowHistoryMeanTime.jet,
    NativeWindowHistoryMeanTime.read_original,NativeForwardWindowEvolution.velocityJet,
    NativeForwardWindowJets.jet_zero] using original

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    Tendsto (fun M => (mean (resolved seed M time)).1) atTop
      (𝓝 (NativeForwardWindowSource.source seed time).fst) := by
  let read:=wholePhysical.subtypeL.comp mean
  have small:=read.continuous.tendsto (0 : H) |>.comp (source_error_tendsto seed time nonnegative)
  have combined:=(finite_mean_tendsto seed time).sub small
  simpa only [NativeWindowHistoryMeanForceResolution.resolved_mean,Submodule.coe_sub,
    read,Function.comp_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,map_zero,sub_zero] using combined

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem mean_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    mean (resolved seed M (step.2.clockAdvance+time))=mean (resolved step.1 M time) :=
  congrArg mean (NativeWindowHistoryMeanForceResolution.resolved_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanRecovery

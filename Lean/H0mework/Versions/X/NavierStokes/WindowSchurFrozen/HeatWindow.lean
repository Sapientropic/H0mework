import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.HeatDual
import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.Window

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryHeatWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryFrozenInverse (kernel physical)
open NativeWindowHistoryInverseWindow (average)
open NativeWindowHistoryHeatDual (energy heatEnergy form)
open NativeUnheatedStressPairEvolution (kernelWeight)
noncomputable section
variable {nu : Viscosity}

theorem included (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    kernel seed M time (includeCLM (modes M) (modes_closed M) f)=includeCLM (modes M) (modes_closed M) (physical seed M time f) :=
  NativeWindowHistoryOseen.lift_included M _ f

private theorem applied_continuous {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : ℝ → E →L[ℝ] F) (continuous : Continuous A) (v : E) :
    Continuous (fun t => A t v) := continuous.clm_apply continuous_const

theorem physical_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (f : physicalSpace (modes M)) :
    Continuous (fun s => physical seed M s f) := by
  have applied := applied_continuous (E := wholePhysical) (F := wholePhysical) (kernel seed M)
    (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) (includeCLM (modes M) (modes_closed M) f)
  have projected : Continuous (fun s => restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (kernel seed M s (includeCLM (modes M) (modes_closed M) f))) :=
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)).continuous.comp applied
  simpa only [included,restrict_include] using! projected

private theorem weighted_integrable (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    IntervalIntegrable (fun s => kernelWeight order time 0 s • physical seed M s f) volume (time+1) (time+2) :=
  ((physical_continuous seed M f).intervalIntegrable (time+1) (time+2)).continuousOn_smul
    (NativeUnheatedStressPairEvolution.kernelWeight_continuous order time 0).continuousOn

def value (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) : physicalSpace (modes M) :=
  ∫s in time+1..time+2,kernelWeight order time 0 s • physical seed M s f

private theorem operator_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (order : ℕ) (time : ℝ) (f : E) :
    (∫s in time+1..time+2,kernelWeight order time 0 s • A s) f=
      ∫s in time+1..time+2,kernelWeight order time 0 s • A s f := by
  have paid := ((continuous.intervalIntegrable (μ := volume) (time+1) (time+2)).continuousOn_smul
    (NativeUnheatedStressPairEvolution.kernelWeight_continuous order time 0).continuousOn)
  have source := ((ContinuousLinearMap.apply ℝ E f).intervalIntegral_comp_comm paid).symm
  change (∫s in time+1..time+2,kernelWeight order time 0 s • A s) f=
    ∫s in time+1..time+2,(kernelWeight order time 0 s • A s) f at source
  simpa only [smul_apply] using source

theorem whole_read (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : wholePhysical) :
    includeCLM (modes M) (modes_closed M) (value seed M order time (restrictCLM (modes M) (modes_zero M) (modes_closed M) f))=
      average seed M order time f := by
  let input:=restrictCLM (modes M) (modes_zero M) (modes_closed M) f
  have first := (includeCLM (modes M) (modes_closed M)).intervalIntegral_comp_comm (weighted_integrable seed M order time input)
  have last := operator_integral (E := wholePhysical) (kernel seed M)
    (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) order time f
  have original := congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A f)
    (NativeWindowHistoryInverseWindow.average_original seed M order time)
  have middle : (∫s in time+1..time+2,includeCLM (modes M) (modes_closed M) (kernelWeight order time 0 s • physical seed M s input))=
    ∫s in time+1..time+2,kernelWeight order time 0 s • kernel seed M s f := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [map_smul]
    rfl
  exact first.symm.trans (middle.trans (original.trans last).symm)

theorem physical_read (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    includeCLM (modes M) (modes_closed M) (value seed M order time f)=
      average seed M order time (includeCLM (modes M) (modes_closed M) f) := by
  simpa only [restrict_include] using whole_read seed M order time (includeCLM (modes M) (modes_closed M) f)

theorem time_word_read (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    includeCLM (modes M) (modes_closed M) (value seed M order time f)=
      iteratedDeriv order (average seed M 0) time (includeCLM (modes M) (modes_closed M) f) := by
  rw [NativeWindowHistoryInverseWindow.average_iterated]
  exact physical_read seed M order time f

private theorem energy_integral (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    energy nu M (value seed M order time f)=
      ∫s in time+1..time+2,kernelWeight order time 0 s*form nu M (value seed M order time f) (physical seed M s f) := by
  have source := (LinearMap.toContinuousLinearMap (form nu M (value seed M order time f))).intervalIntegral_comp_comm
    (weighted_integrable seed M order time f)
  have paired : form nu M (value seed M order time f) (value seed M order time f)=
      ∫s in time+1..time+2,kernelWeight order time 0 s*form nu M (value seed M order time f) (physical seed M s f) := by
    simpa only [value,map_smul,smul_eq_mul] using! source.symm
  exact (NativeWindowHistoryHeatDual.form_self nu M _).symm.trans paired

private theorem square_absorption (x b K : ℝ) (x0 : 0≤x) (b0 : 0≤b)
    (paid : x≤K*Real.sqrt x*Real.sqrt b) : x≤K^2*b := by
  have squared := pow_le_pow_left₀ x0 paid 2
  rw [mul_pow,mul_pow,Real.sq_sqrt x0,Real.sq_sqrt b0] at squared
  by_cases zero : x=0
  · rw [zero]
    exact mul_nonneg (sq_nonneg K) b0
  · have positive : 0<x := lt_of_le_of_ne x0 (Ne.symm zero)
    by_contra no
    have contradict := mul_pos positive (sub_pos.mpr (lt_of_not_ge no))
    nlinarith only [squared,contradict]

theorem energy_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    energy nu M (value seed M order time f)≤NativeWindowFiniteStressUniform.kernelBound order^2*heatEnergy nu M f := by
  let v:=value seed M order time f
  have e0 := NativeWindowHistoryHeatDual.energy_nonnegative nu M v
  have h0 := NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f
  have point (s : ℝ) (_ : s∈uIoc (time+1) (time+2)) :
      ‖kernelWeight order time 0 s*form nu M v (physical seed M s f)‖≤
      NativeWindowFiniteStressUniform.kernelBound order*Real.sqrt (energy nu M v)*Real.sqrt (heatEnergy nu M f) := by
    have cauchy := NativeWindowHistoryHeatDual.form_bound nu M v (physical seed M s f)
    have source := Real.sqrt_le_sqrt (NativeWindowHistoryHeatDual.source_bound seed M s f)
    have innerBound := cauchy.trans (mul_le_mul_of_nonneg_left source (Real.sqrt_nonneg _))
    have kernelBound := NativeWindowFiniteStressUniform.kernel_bounded order (time-s)
    rw [norm_mul,Real.norm_eq_abs]
    change _≤_
    exact (mul_le_mul (by simpa only [kernelWeight,zero_add,Real.norm_eq_abs] using kernelBound) innerBound (abs_nonneg _)
      (NativeWindowFiniteStressUniform.kernelBound_positive order).le).trans_eq (by ring)
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const point
  have paid : energy nu M v≤NativeWindowFiniteStressUniform.kernelBound order*Real.sqrt (energy nu M v)*Real.sqrt (heatEnergy nu M f) := by
    rw [← energy_integral seed M order time f] at integralBound
    change ‖energy nu M v‖≤_ at integralBound
    simpa only [show time+2-(time+1)=(1:ℝ) by ring,abs_one,mul_one,Real.norm_of_nonneg e0] using integralBound
  exact square_absorption _ _ _ e0 h0 paid

def sourceInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (NativeWindowHistorySchurCompletion.commonForce seed M time)

theorem source_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (value seed M 0 time (sourceInput seed M time))=
      NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M) :=
  (whole_read seed M 0 time (NativeWindowHistorySchurCompletion.commonForce seed M time)).trans
    (NativeWindowHistoryInverseWindow.source_mean seed M time).symm

theorem source_input_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,heatEnergy nu M (sourceInput seed M time)≤C := by
  obtain ⟨low,D,D0,paid⟩ := NativeWindowHistorySchurSampleControl.source_common_force_bound seed horizon nonnegative
  refine ⟨low,2*D,mul_nonneg (by norm_num) D0,fun M above time inside => ?_⟩
  let f:=sourceInput seed M time
  let v:=NativeWindowHistoryHeatDual.heat nu M f
  have paired := paid M above time inside v
  rw [include_inner] at paired
  change |heatEnergy nu M f|≤(1/2 : ℝ)*pairing (modes M) v v+(nu.coeff/4)*curlPair (modes M) v.1 v.1+D at paired
  rw [abs_of_nonneg (NativeWindowHistoryHeatDual.heatEnergy_nonnegative nu M f)] at paired
  have source := NativeWindowHistoryHeatDual.heatEnergy_self nu M f
  have mass : pairing (modes M) v v=‖coefficients (modes M) v‖^2 := real_inner_self_eq_norm_sq (coefficients (modes M) v)
  have gradient : 0≤nu.coeff*curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact mul_nonneg nu.coeff_pos.le (sq_nonneg _)
  change heatEnergy nu M f=‖coefficients (modes M) v‖^2+nu.coeff*curlPair (modes M) v.1 v.1 at source
  change heatEnergy nu M f≤2*D
  nlinarith only [paired,source,mass,gradient]

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,∀ order : ℕ,
      energy nu M (value seed M order time (sourceInput seed M time))≤NativeWindowFiniteStressUniform.kernelBound order^2*C := by
  obtain ⟨low,C,C0,paid⟩ := source_input_bound seed horizon nonnegative
  exact ⟨low,C,C0,fun M above time inside order => (energy_bound seed M order time (sourceInput seed M time)).trans
    (mul_le_mul_of_nonneg_left (paid M above time inside) (sq_nonneg _))⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time)
    (f : physicalSpace (modes M)) :
    value seed M order (step.2.clockAdvance+time) f=value step.1 M order time f := by
  have operators := congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A (includeCLM (modes M) (modes_closed M) f))
    (NativeWindowHistoryInverseWindow.average_next seed M order step generated time time0)
  have same := (physical_read seed M order (step.2.clockAdvance+time) f).trans
    (operators.trans (physical_read step.1 M order time f).symm)
  simpa only [restrict_include] using congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M)) same

theorem sourceInput_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    sourceInput seed M (step.2.clockAdvance+time)=sourceInput step.1 M time :=
  congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M))
    (NativeWindowHistoryInverseWindow.commonForce_next seed M step generated time time0)

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    value seed M order (step.2.clockAdvance+time) (sourceInput seed M (step.2.clockAdvance+time))=
      value step.1 M order time (sourceInput step.1 M time) := by
  rw [sourceInput_next seed M step generated time time0,value_next seed M order step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryHeatWindow

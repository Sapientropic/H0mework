import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.Kernel
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.SampleControl

set_option autoImplicit false
open scoped BigOperators Topology Convolution ENNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryInverseWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action forwardFiber)
open NativeWindowTraceWholeHistory (projected projection finiteHistory)
open NativeWindowHistoryMeanProjection (embed mean)
open NativeWindowHistorySchurCompletion (completion commonForce complete)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeForwardWindowJets (kernelJet kernelJet_smooth kernelJet_compact)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

section SmoothOperator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private def smooth (f : ℝ → E →L[ℝ] E) (order : ℕ) : ℝ → E →L[ℝ] E :=
  kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f

omit [CompleteSpace E] in
private theorem smooth_derivative (f : ℝ → E →L[ℝ] E) (continuous : Continuous f) (order : ℕ) (time : ℝ) :
    HasDerivAt (smooth f order) (smooth f (order+1) time) time := by
  have source := (kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) (continuous.locallyIntegrable (μ := (volume : Measure ℝ))) time
  simpa only [smooth,kernelJet,iteratedDeriv_succ] using source

omit [CompleteSpace E] in
private theorem smooth_original (f : ℝ → E →L[ℝ] E) (order : ℕ) (time : ℝ) :
    smooth f order time=∫sample in time+1..time+2,NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample • f sample :=
  NativeWindowStressHeatTime.kernel_integral _ _ _

omit [CompleteSpace E] in
private theorem smooth_bound (f : ℝ → E →L[ℝ] E) (bounded : ∀ t,‖f t‖≤1) (order : ℕ) (time : ℝ) :
    ‖smooth f order time‖≤NativeWindowFiniteStressUniform.kernelBound order := by
  rw [smooth_original]
  have point (sample : ℝ) (_ : sample∈uIoc (time+1) (time+2)) :
      ‖NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample • f sample‖≤
        NativeWindowFiniteStressUniform.kernelBound order := by
    rw [norm_smul]
    have first := NativeWindowFiniteStressUniform.kernel_bounded order (time-sample)
    simpa only [NativeUnheatedStressPairEvolution.kernelWeight,zero_add,mul_one] using
      mul_le_mul first (bounded sample) (norm_nonneg (f sample)) (NativeWindowFiniteStressUniform.kernelBound_positive order).le
  have paid := intervalIntegral.norm_integral_le_of_norm_le_const point
  simpa only [show time+2-(time+1)=(1:ℝ) by ring,abs_one,mul_one] using paid

omit [CompleteSpace E] in
private theorem smooth_contDiff (f : ℝ → E →L[ℝ] E) (continuous : Continuous f) (order : ℕ) :
    ContDiff ℝ ∞ (smooth f order) :=
  (kernelJet_compact order).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (kernelJet_smooth order) (continuous.locallyIntegrable (μ := (volume : Measure ℝ)))

omit [CompleteSpace E] in
private theorem curve_integrable (f : ℝ → E →L[ℝ] E) (continuous : Continuous f) (time : ℝ) :
    Integrable (fun lag => f (time-lag)) averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time f continuous 1).integrable le_rfl

omit [CompleteSpace E] in
private theorem smooth_zero (f : ℝ → E →L[ℝ] E) (time : ℝ) :
    smooth f 0 time=∫lag,f (time-lag) ∂averageMeasure := by
  rw [NativeForwardWindowPairingReadout.density_integral]
  rfl

private theorem evaluate_integral (f : ℝ → E →L[ℝ] E) (continuous : Continuous f) (time : ℝ) (v : E) :
    (∫lag,f (time-lag) ∂averageMeasure) v=∫lag,f (time-lag) v ∂averageMeasure :=
  ((ContinuousLinearMap.apply ℝ E v).integral_comp_comm (curve_integrable f continuous time)).symm
omit [CompleteSpace E] in
private theorem zero_pair (x y : E →L[ℝ] E) : (0 : ℝ) • x=(0 : ℝ) • y := by simp
end SmoothOperator

abbrev Operator := wholePhysical →L[ℝ] wholePhysical

def average (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → Operator :=
  smooth (E := wholePhysical) (kernel seed M) order

theorem average_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (average seed M order) (average seed M (order+1) time) time := by
  simpa only [average] using! smooth_derivative (E := wholePhysical) (kernel seed M)
    (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) order time

theorem average_iterated (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) :
    iteratedDeriv order (average seed M 0)=average seed M order := by
  induction order with
  | zero => simp only [iteratedDeriv_zero]
  | succ order ih =>
    rw [iteratedDeriv_succ,ih]
    funext time
    exact (average_hasDerivAt seed M order time).deriv

theorem average_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    average seed M order time=∫sample in time+1..time+2,NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample • kernel seed M sample := by
  simpa only [average] using! smooth_original (E := wholePhysical) (kernel seed M) order time

theorem average_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖average seed M order time‖≤NativeWindowFiniteStressUniform.kernelBound order := by
  simpa only [average] using! smooth_bound (E := wholePhysical) (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_norm seed M) order time

theorem time_word_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (average seed M 0) time‖≤NativeWindowFiniteStressUniform.kernelBound order := by
  rw [average_iterated]
  exact average_bound seed M order time

theorem average_contDiff (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) :
    ContDiff ℝ ∞ (average seed M order) := by
  simpa only [average] using! smooth_contDiff (E := wholePhysical) (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) order

theorem average_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    average seed M 0 time=∫lag,kernel seed M (time-lag) ∂averageMeasure := by
  simpa only [average] using! smooth_zero (E := wholePhysical) (kernel seed M) time

private theorem applied_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : wholePhysical) :
    (∫lag,kernel seed M (time-lag) ∂averageMeasure) f=∫lag,kernel seed M (time-lag) f ∂averageMeasure := by
  simpa only [] using! evaluate_integral (E := wholePhysical) (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) time f

private theorem solved_history (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : H) (f : wholePhysical)
    (equation : x-action seed M time x=embed f) (supported : projected M x=x) :
    x=ᵐ[averageMeasure] fun lag => kernel seed M (time-lag) f := by
  filter_upwards [Lp.coeFn_sub x (action seed M time x),NativeWindowHistoryOseen.action_ae seed M time x,
    NativeWindowTraceWholeHistory.constant_ae f,(projection M).coeFn_compLpL x] with lag subtract acted fixed project
  have source:=congrArg (fun h : H => h lag) equation
  have range:=congrArg (fun h : H => h lag) supported
  rw [subtract,Pi.sub_apply,acted] at source
  have original : x lag-forwardFiber seed M (time-lag) (x lag)=f := source.trans fixed
  have originalRange : projection M (x lag)=x lag := project.symm.trans range
  exact originalRange.symm.trans ((NativeWindowHistoryFrozenInverse.kernel_inverse seed M (time-lag) (x lag)).symm.trans
    (congrArg (kernel seed M (time-lag)) original))

private theorem mean_solved (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : H) (f : wholePhysical)
    (equation : x-action seed M time x=embed f) (supported : projected M x=x) :
    mean x=average seed M 0 time f := by
  rw [NativeWindowHistoryMeanProjection.mean_original,average_zero,applied_integral]
  exact integral_congr_ae (solved_history seed M time x f equation supported)

theorem completion_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    completion seed M time=ᵐ[averageMeasure] fun lag => kernel seed M (time-lag) (commonForce seed M time) :=
  solved_history seed M time (completion seed M time) (commonForce seed M time)
    (NativeWindowHistorySchurCompletion.completion_equation seed M time)
    (NativeWindowHistorySchurCompletion.completion_projected seed M time)

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (finiteHistory seed time M)=average seed M 0 time (commonForce seed M time) :=
  (NativeWindowHistorySchurCompletion.completion_mean seed M time).symm.trans
    (mean_solved seed M time (completion seed M time) (commonForce seed M time)
      (NativeWindowHistorySchurCompletion.completion_equation seed M time)
      (NativeWindowHistorySchurCompletion.completion_projected seed M time))

theorem source_velocity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (average seed M 0 time (commonForce seed M time)).1=NativeWindowHistoryMeanTime.jet seed M 0 time :=
  (congrArg (fun x : wholePhysical => x.1) (source_mean seed M time).symm).trans
    (NativeWindowHistoryMeanTime.source_mean seed M time)

private theorem complete_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    projected M (complete seed M time (includeCLM (modes M) (modes_closed M) v))=
      complete seed M time (includeCLM (modes M) (modes_closed M) v) := by
  have first:=NativeWindowHistoryMeanProjection.comp_embed (projection M) (includeCLM (modes M) (modes_closed M) v)
  have point : projection M (includeCLM (modes M) (modes_closed M) v)=includeCLM (modes M) (modes_closed M) v := by
    simp only [projection,ContinuousLinearMap.comp_apply,restrict_include]
  have fixed:=first.trans (congrArg embed point)
  have last:=NativeWindowHistorySchurCompletion.response_projected seed M time (includeCLM (modes M) (modes_closed M) v)
  simpa only [complete,projected,map_add] using! congrArg₂ (fun x y : H => x+y) fixed last

theorem schur_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    average seed M 0 time (includeCLM (modes M) (modes_closed M) v-
      NativeWindowHistorySchurAction.effective seed M time (includeCLM (modes M) (modes_closed M) v))=
      includeCLM (modes M) (modes_closed M) v :=
  (mean_solved seed M time (complete seed M time (includeCLM (modes M) (modes_closed M) v)) _
    (NativeWindowHistorySchurCompletion.complete_equation seed M time (includeCLM (modes M) (modes_closed M) v))
    (complete_projected seed M time v)).symm.trans
      (NativeWindowHistorySchurCompletion.complete_mean seed M time (includeCLM (modes M) (modes_closed M) v))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem average_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    average seed M order (step.2.clockAdvance+time)=average step.1 M order time := by
  change (∫lag,kernelJet order lag • kernel seed M (step.2.clockAdvance+time-lag))=
    (∫lag,kernelJet order lag • kernel step.1 M (time-lag))
  apply integral_congr_ae
  filter_upwards with lag
  by_cases zero : kernelJet order lag=0
  · rw [zero]
    simpa only [] using! zero_pair (E := wholePhysical) (kernel seed M (step.2.clockAdvance+time-lag)) (kernel step.1 M (time-lag))
  · have nonnegative : 0≤time-lag := by linarith [NativeForwardWindowJets.kernelJet_nonpositive order lag zero]
    rw [add_sub_assoc,NativeWindowHistoryFrozenInverse.kernel_next seed M step generated (time-lag) nonnegative]

theorem commonForce_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    commonForce seed M (step.2.clockAdvance+time)=commonForce step.1 M time := by
  have states:=NativeWindowHistorySchurCompletion.completion_next seed M step generated time time0
  have operators:=NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  have actions:=congrArg₂ (fun (A : H →L[ℝ] H) (h : H) => A h) operators.1 states
  have same:embed (commonForce seed M (step.2.clockAdvance+time))=embed (commonForce step.1 M time) :=
    (NativeWindowHistorySchurCompletion.completion_equation seed M (step.2.clockAdvance+time)).symm.trans
      ((congrArg₂ (fun x y : H => x-y) states actions).trans
        (NativeWindowHistorySchurCompletion.completion_equation step.1 M time))
  simpa only [NativeWindowHistoryMeanProjection.mean_embed] using congrArg mean same

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryInverseWindow

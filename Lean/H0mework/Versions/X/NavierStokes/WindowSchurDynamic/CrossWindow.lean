import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianControl
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonForceBounds

set_option autoImplicit false
open scoped Topology Convolution ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCrossWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_closed)
open NativeWindowHistoryOseen (H velocityPath)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeForwardWindowJets (kernelJet kernelJet_smooth kernelJet_compact)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def heat (nu : Viscosity) (M : ℕ) : wholePhysical →L[ℝ] wholePhysical :=
  ContinuousLinearMap.id ℝ wholePhysical+nu.coeff • laplacianFiber nu M

def row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample : ℝ) : wholePhysical →L[ℝ] ℝ :=
  (innerSL ℝ (velocityPath seed M sample)).comp ((heat nu M).comp (kernel seed M sample))

private theorem row_cont {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℝ → E) (K : ℝ → E →L[ℝ] E) (A : E →L[ℝ] E)
    (hv : Continuous v) (hK : Continuous K) :
    Continuous (fun s => (innerSL ℝ (v s)).comp (A.comp (K s))) :=
  ((innerSL ℝ).continuous.comp hv).clm_comp (continuous_const.clm_comp hK)

theorem row_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (row seed M) :=
  row_cont (E := wholePhysical) (velocityPath seed M) (kernel seed M) (heat nu M)
    (NativeWindowHistoryOseen.velocityPath_continuous seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M)

private def smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (order : ℕ) : ℝ → E := kernelJet order ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f

private theorem smooth_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (continuous : Continuous f) (order : ℕ) (time : ℝ) :
    HasDerivAt (smooth f order) (smooth f (order+1) time) time := by
  have source:=(kernelJet_compact order).hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((kernelJet_smooth order).of_le (by simp)) (continuous.locallyIntegrable (μ := (volume : Measure ℝ))) time
  simpa only [smooth,kernelJet,iteratedDeriv_succ] using source

private theorem smooth_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (time : ℝ) : smooth f 0 time=∫lag,f (time-lag) ∂averageMeasure := by
  rw [NativeForwardWindowPairingReadout.density_integral]
  rfl

def average (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → wholePhysical →L[ℝ] ℝ :=
  smooth (row seed M) order

theorem average_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (average seed M order) (average seed M (order+1) time) time := by
  exact smooth_derivative (row seed M) (row_continuous seed M) order time

theorem average_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    average seed M 0 time=∫lag,row seed M (time-lag) ∂averageMeasure := smooth_zero (row seed M) time

def input (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : wholePhysical :=
  includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M order time)

theorem input_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (input seed M order) (input seed M (order+1) time) time :=
  (includeCLM (modes M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time
    (NativeWindowHistoryCommonForceTime.jet_hasDerivAt seed M order time)

theorem input_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    input seed M 0 time=commonForce seed M time :=
  NativeWindowHistoryCommonForceTime.value_original seed M time

def value (seed : GeneratedWholeRestartCurrent nu) (M order forceOrder : ℕ) (time : ℝ) : ℝ :=
  average seed M order time (input seed M forceOrder time)

theorem value_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order forceOrder : ℕ) (time : ℝ) :
    HasDerivAt (value seed M order forceOrder)
      (value seed M (order+1) forceOrder time+value seed M order (forceOrder+1) time) time :=
  (average_hasDerivAt seed M order time).clm_apply (input_hasDerivAt seed M forceOrder time)

private theorem smooth_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E →L[ℝ] ℝ) (continuous : Continuous f) (time : ℝ) (v : E) :
    smooth f 0 time v=∫lag,f (time-lag) v ∂averageMeasure := by
  have paid:Integrable (fun lag => f (time-lag)) averageMeasure :=
    (NativeWindowTraceTerminalGraph.continuous_memLp time f continuous 1).integrable le_rfl
  exact (congrArg (fun L : E →L[ℝ] ℝ => L v) (smooth_zero f time)).trans
    ((ContinuousLinearMap.apply ℝ ℝ v).integral_comp_comm paid).symm

theorem value_zero (seed : GeneratedWholeRestartCurrent nu) (M forceOrder : ℕ) (time : ℝ) :
    value seed M 0 forceOrder time=∫lag,row seed M (time-lag) (input seed M forceOrder time) ∂averageMeasure :=
  smooth_apply (E := wholePhysical) (row seed M) (row_continuous seed M) time (input seed M forceOrder time)

private theorem smooth_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E →L[ℝ] ℝ) (continuous : Continuous f) (order : ℕ) (time : ℝ) (v : E) :
    smooth f order time v=∫sample in time+1..time+2,
      NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample * f sample v := by
  have original:smooth f order time=∫sample in time+1..time+2,
      NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample • f sample :=
    NativeWindowStressHeatTime.kernel_integral f order time
  have paid:=((NativeUnheatedStressPairEvolution.kernelWeight_continuous order time 0).smul continuous).intervalIntegrable (μ := (volume : Measure ℝ)) (time+1) (time+2)
  have source:=(ContinuousLinearMap.apply ℝ ℝ v).intervalIntegral_comp_comm paid
  exact (congrArg (fun L : E →L[ℝ] ℝ => L v) original).trans (source.symm.trans
    (intervalIntegral.integral_congr fun sample _ => rfl))

theorem value_interval (seed : GeneratedWholeRestartCurrent nu) (M order forceOrder : ℕ) (time : ℝ) :
    value seed M order forceOrder time=∫sample in time+1..time+2,
      NativeUnheatedStressPairEvolution.kernelWeight order time 0 sample * row seed M sample (input seed M forceOrder time) :=
  smooth_interval (E := wholePhysical) (row seed M) (row_continuous seed M) order time (input seed M forceOrder time)

theorem heat_ae (nu : Viscosity) (M : ℕ) (v : H) :
    NativeWindowHistoryJacobianControl.heat nu M v=ᵐ[averageMeasure] fun lag => heat nu M (v lag) := by
  filter_upwards [Lp.coeFn_add v (nu.coeff • laplacianAction nu M v),
    Lp.coeFn_smul nu.coeff (laplacianAction nu M v),(laplacianFiber nu M).coeFn_compLpL v]
    with lag add scale lap
  change NativeWindowHistoryJacobianControl.heat nu M v lag=_ at add
  change laplacianAction nu M v lag=laplacianFiber nu M (v lag) at lap
  rw [add,Pi.add_apply,scale,Pi.smul_apply,lap]
  rfl

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    value seed M 0 0 time=NativeWindowHistoryJacobianControl.form nu M
      (finiteHistory seed time M) (completion seed M time) := by
  rw [value_zero,input_zero,NativeWindowHistoryJacobianControl.form,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryOseen.history_original seed M time,
    NativeWindowHistoryInverseWindow.completion_original seed M time,heat_ae nu M (completion seed M time)]
    with lag original completed heated
  rw [original,heated,completed]
  rfl

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem row_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    row seed M (step.2.clockAdvance+time)=row step.1 M time := by
  have original (current : GeneratedWholeRestartCurrent nu) (sample : ℝ) :
      velocityPath current M sample=NativeWindowTraceWholeHistory.projection M (NativeWindowTraceWholeHistory.original current sample) := by
    simp only [NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,
      NativeWindowHistoryOseen.restrict_original_total]
    rfl
  have velocity:velocityPath seed M (step.2.clockAdvance+time)=velocityPath step.1 M time :=
    (original seed _).trans ((congrArg (NativeWindowTraceWholeHistory.projection M)
      (NativeWindowTraceWholeHistory.original_next seed step generated time time0)).trans (original step.1 time).symm)
  exact congrArg₂ (fun (v : wholePhysical) (K : wholePhysical →L[ℝ] wholePhysical) =>
    (innerSL ℝ v).comp ((heat nu M).comp K)) velocity
      (NativeWindowHistoryFrozenInverse.kernel_next seed M step generated time time0)

theorem average_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    average seed M order (step.2.clockAdvance+time)=average step.1 M order time := by
  change (∫lag,kernelJet order lag • row seed M (step.2.clockAdvance+time-lag))=
    ∫lag,kernelJet order lag • row step.1 M (time-lag)
  apply integral_congr_ae
  filter_upwards with lag
  by_cases zero:kernelJet order lag=0
  · simp only [zero,zero_smul]
  · have nonnegative:0≤time-lag := by linarith [NativeForwardWindowJets.kernelJet_nonpositive order lag zero]
    rw [add_sub_assoc,row_next seed M step generated (time-lag) nonnegative]

theorem value_next (seed : GeneratedWholeRestartCurrent nu) (M order forceOrder : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    value seed M order forceOrder (step.2.clockAdvance+time)=value step.1 M order forceOrder time :=
  congrArg₂ (fun (L : wholePhysical →L[ℝ] ℝ) (v : wholePhysical) => L v)
    (average_next seed M order step generated time time0)
    (congrArg (includeCLM (modes M) (modes_closed M))
      (NativeWindowHistoryCommonForceTime.jet_next seed M forceOrder step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCrossWindow

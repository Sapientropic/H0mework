import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonForceBounds
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Transpose
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCommonResponse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action)
open NativeWindowHistoryCommonForceTime (jet)
open NativeWindowHistoryFrozenInverse (kernel physical)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def curve (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (frame sampleTime : ℝ) : wholePhysical :=
  kernel seed M sampleTime (includeCLM (modes M) (modes_closed M) (jet seed M order frame))

private theorem applied_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (continuous : Continuous A) (v : E) : Continuous (fun t => A t v) :=
  continuous.clm_apply continuous_const

theorem curve_continuous (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    Continuous (curve seed M order time) := by
  simpa only [curve] using! applied_continuous (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M)
    (includeCLM (modes M) (modes_closed M) (jet seed M order time))

def profile (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : Lp wholePhysical ∞ averageMeasure :=
  NativeWindowHistoryOseen.profile (curve seed M order time) (curve_continuous seed M order time) time

def response (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : H :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time (curve seed M order time) (curve_continuous seed M order time) 2).toLp
    (fun lag => curve seed M order time (time-lag))

theorem profile_ae (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    profile seed M order time=ᵐ[averageMeasure] fun lag => curve seed M order time (time-lag) :=
  NativeWindowHistoryOseen.profile_ae _ _ _

theorem response_ae (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    response seed M order time=ᵐ[averageMeasure] fun lag => curve seed M order time (time-lag) :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time (curve seed M order time) (curve_continuous seed M order time) 2).coeFn_toLp

def sample (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time lag : ℝ) : physicalSpace (modes M) :=
  physical seed M (time-lag) (jet seed M order time)

theorem response_sample (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    response seed M order time=ᵐ[averageMeasure] fun lag => includeCLM (modes M) (modes_closed M) (sample seed M order time lag) := by
  filter_upwards [response_ae seed M order time] with lag original
  rw [original,curve,NativeWindowHistoryHeatWindow.included]
  rfl

theorem source_sample_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (lag : ℝ) :
    NativeWindowHistoryHeatDual.energy nu M (sample seed M order time lag) ≤ NativeWindowHistoryCommonForceBounds.budget seed horizon order :=
  (NativeWindowHistoryHeatDual.source_bound seed M (time-lag) (jet seed M order time)).trans
    (NativeWindowHistoryCommonForceBounds.source_bound seed horizon M order time inside)

theorem source_sample_gradient (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (lag : ℝ) :
    curlPair (modes M) (sample seed M order time lag).1 (sample seed M order time lag).1 ≤
      NativeWindowHistoryCommonForceBounds.budget seed horizon order/nu.coeff := by
  apply (le_div_iff₀ nu.coeff_pos).mpr
  have paid := source_sample_bound seed horizon M order time inside lag
  unfold NativeWindowHistoryHeatDual.energy at paid
  nlinarith only [paid,sq_nonneg ‖coefficients (modes M) (sample seed M order time lag)‖]

theorem response_projected (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    NativeWindowTraceWholeHistory.projected M (response seed M order time)=response seed M order time := by
  apply Lp.ext
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (response seed M order time),
    response_sample seed M order time] with lag projected original
  change ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure (response seed M order time)) lag=_
  rw [projected,original]
  simp only [NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,restrict_include]

theorem equation (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    response seed M order time-action seed M time (response seed M order time)=
      NativeWindowHistoryMeanProjection.embed (includeCLM (modes M) (modes_closed M) (jet seed M order time)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (response seed M order time) (action seed M time (response seed M order time)),
    NativeWindowHistoryOseen.action_ae seed M time (response seed M order time),response_sample seed M order time,
    NativeWindowTraceWholeHistory.constant_ae (includeCLM (modes M) (modes_closed M) (jet seed M order time))]
    with lag difference acted original constant
  have constantRead : NativeWindowHistoryMeanProjection.embed (includeCLM (modes M) (modes_closed M) (jet seed M order time)) lag=
      includeCLM (modes M) (modes_closed M) (jet seed M order time) := constant
  rw [difference,Pi.sub_apply,acted,original,constantRead]
  have source := congrArg (includeCLM (modes M) (modes_closed M)) (NativeWindowHistoryFrozenInverse.physical_write seed M (time-lag) (jet seed M order time))
  simpa only [map_sub,NativeWindowHistoryOseen.forwardFiber,NativeWindowHistoryOseen.lift_included] using! source

def transpose (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (NativeWindowHistorySchurAdvectorFiber.family nu M).flip.holderL averageMeasure ∞ 2 2 (profile seed M order time)

theorem transpose_ae (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (v : H) :
    transpose seed M order time v=ᵐ[averageMeasure] fun lag =>
      NativeWindowHistorySchurAdvectorFiber.family nu M (v lag) (includeCLM (modes M) (modes_closed M) (sample seed M order time lag)) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (NativeWindowHistorySchurAdvectorFiber.family nu M).flip (profile seed M order time) v,
    profile_ae seed M order time] with lag acted original
  change transpose seed M order time v lag=NativeWindowHistorySchurAdvectorFiber.family nu M (v lag) (profile seed M order time lag) at acted
  rw [acted,original,curve,NativeWindowHistoryHeatWindow.included]
  rfl

def nonlinear (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : H :=
  transpose seed M order time (NativeWindowTraceWholeHistory.finiteHistory seed time M)

theorem nonlinear_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    action seed M time (response seed M order time)=
      (-nu.coeff) • laplacianAction nu M (response seed M order time)+nonlinear seed M order time := by
  have point : action seed M time (response seed M order time)=
      (NativeWindowHistoryMeanBlocks.diffusion nu M).compLpL 2 averageMeasure (response seed M order time)+nonlinear seed M order time := by
    apply Lp.ext
    filter_upwards [NativeWindowHistoryOseen.action_ae seed M time (response seed M order time),
      Lp.coeFn_add ((NativeWindowHistoryMeanBlocks.diffusion nu M).compLpL 2 averageMeasure (response seed M order time)) (nonlinear seed M order time),
      (NativeWindowHistoryMeanBlocks.diffusion nu M).coeFn_compLpL (response seed M order time),
      transpose_ae seed M order time (NativeWindowTraceWholeHistory.finiteHistory seed time M),response_sample seed M order time,
      NativeWindowHistoryOseen.history_original seed M time] with lag acted added diffused transported original source
    rw [acted,added,Pi.add_apply,diffused,show nonlinear seed M order time lag=_ from transported,original,source]
    exact (NativeWindowHistorySchurAdvectorFiber.family_source seed M (time-lag) _).symm
  exact point.trans (congrArg (fun v : H => v+nonlinear seed M order time)
    (NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M (response seed M order time)))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem curve_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (frame sampleTime : ℝ)
    (frame0 : 0 ≤ frame) (sample0 : 0 ≤ sampleTime) :
    curve seed M order (step.2.clockAdvance+frame) (step.2.clockAdvance+sampleTime)=curve step.1 M order frame sampleTime := by
  unfold curve
  rw [NativeWindowHistoryCommonForceTime.jet_next seed M order step generated frame frame0,
    NativeWindowHistoryFrozenInverse.kernel_next seed M step generated sampleTime sample0]

private theorem field_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time lag : ℝ)
    (time0 : 0 ≤ time) (inside : lag∈Icc (-2 : ℝ) (-1)) :
    curve seed M order (step.2.clockAdvance+time) (step.2.clockAdvance+time-lag)=curve step.1 M order time (time-lag) := by
  simpa only [add_sub_assoc] using curve_next seed M order step generated time (time-lag) time0 (by linarith [inside.2])

theorem response_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    response seed M order (step.2.clockAdvance+time)=response step.1 M order time := by
  apply Lp.ext
  filter_upwards [response_ae seed M order (step.2.clockAdvance+time),response_ae step.1 M order time,
    NativeWindowTraceEndpointWindow.average_interval] with lag first last inside
  exact first.trans ((field_next seed M order step generated time lag time0 inside).trans last.symm)

theorem profile_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    profile seed M order (step.2.clockAdvance+time)=profile step.1 M order time := by
  apply Lp.ext
  filter_upwards [profile_ae seed M order (step.2.clockAdvance+time),profile_ae step.1 M order time,
    NativeWindowTraceEndpointWindow.average_interval] with lag first last inside
  exact first.trans ((field_next seed M order step generated time lag time0 inside).trans last.symm)

theorem nonlinear_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    nonlinear seed M order (step.2.clockAdvance+time)=nonlinear step.1 M order time := by
  have operators := congrArg ((NativeWindowHistorySchurAdvectorFiber.family nu M).flip.holderL averageMeasure ∞ 2 2)
    (profile_next seed M order step generated time time0)
  exact congrArg₂ (fun (A : H →L[ℝ] H) (h : H) => A h) operators
    (NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0 M)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCommonResponse

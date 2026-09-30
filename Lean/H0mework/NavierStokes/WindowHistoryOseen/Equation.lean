import H0mework.NavierStokes.WindowHistoryOseen.Source

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure density)
noncomputable section
variable {nu : Viscosity}

theorem fiber_before (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (before : time ≤ 0) :
    (forwardFiber seed M time,velocityPath seed M time)=(forwardFiber seed M 0,velocityPath seed M 0) := by
  have same : NativeWindowTraceAdjoint.value seed M time=NativeWindowTraceAdjoint.value seed M 0 := by
    simp only [NativeWindowTraceAdjoint.value,NativeWindowHierarchyPairWindow.state_before seed time before]
  have op : NativeWindowTraceAdjoint.forward seed M time=NativeWindowTraceAdjoint.forward seed M 0 := by
    simp only [NativeWindowTraceAdjoint.forward,NativeWindowTraceAdjoint.advector,same]
  simp only [forwardFiber,velocityPath,same,op]

def forcingValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  if 0 ≤ time then includeCLM (modes M) (modes_closed M) (NativeWindowStageNineSource.forcing seed M time)
  else -forwardFiber seed M 0 (velocityPath seed M 0)

theorem forcingValue_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcingValue seed M time=includeCLM (modes M) (modes_closed M) (NativeWindowStageNineSource.forcing seed M time) :=
  if_pos nonnegative

theorem source_fiber (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ∀ᵐ time : ℝ,velocityRate seed M time=
      forwardFiber seed M time (velocityPath seed M time)+forcingValue seed M time := by
  filter_upwards [velocityRate_original seed M,NativeWindowTraceAdjoint.source_action_ae seed M] with time read source
  by_cases positive : 0 ≤ time
  · rw [read,source positive,map_add,forcingValue_original seed M time positive]
    change _=lift M (NativeWindowTraceAdjoint.forward seed M time)
      (includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M time))+_
    rw [lift_included]
  · have before := fiber_before seed M time (le_of_not_ge positive)
    simp only [Prod.mk.injEq] at before
    rw [velocityRate,if_neg positive,forcingValue,if_neg positive,before.1,before.2,add_neg_cancel]

theorem forcing_difference_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (rateHistory seed M time-action seed M time (finiteHistory seed time M) : H) =ᵐ[averageMeasure]
      fun shift => forcingValue seed M (time-shift) := by
  have source := (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le
    ((Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae (source_fiber seed M))
  filter_upwards [Lp.coeFn_sub (rateHistory seed M time) (action seed M time (finiteHistory seed time M)),
    rateHistory_ae seed M time,action_ae seed M time (finiteHistory seed time M),history_original seed M time,source]
    with shift difference rate original actual equation
  rw [difference,Pi.sub_apply,rate,original,actual,equation,add_sub_cancel_left]

theorem forcing_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    MemLp (fun shift => forcingValue seed M (time-shift)) 2 averageMeasure :=
  (Lp.memLp (rateHistory seed M time-action seed M time (finiteHistory seed time M))).ae_eq
    (forcing_difference_ae seed M time)

def forcingHistory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  (forcing_memLp seed M time).toLp (fun shift => forcingValue seed M (time-shift))

theorem forcingHistory_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    forcingHistory seed M time =ᵐ[averageMeasure] fun shift => forcingValue seed M (time-shift) :=
  (forcing_memLp seed M time).coeFn_toLp

theorem forcingHistory_difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    forcingHistory seed M time=rateHistory seed M time-action seed M time (finiteHistory seed time M) :=
  Lp.ext ((forcingHistory_ae seed M time).trans (forcing_difference_ae seed M time).symm)

theorem source_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rateHistory seed M time=action seed M time (finiteHistory seed time M)+forcingHistory seed M time := by
  rw [forcingHistory_difference]
  abel

theorem source_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => finiteHistory seed t M)
      (action seed M time (finiteHistory seed time M)+forcingHistory seed M time) time := by
  rw [← source_equation]
  exact history_hasDerivAt seed M time

theorem history_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (fun t => finiteHistory seed t M) :=
  continuous_iff_continuousAt.mpr (fun time => (history_hasDerivAt seed M time).continuousAt)

theorem actionHistory_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun time => action seed M time (finiteHistory seed time M)) volume a b := by
  have continuous := Continuous.clm_apply (𝕜 := ℝ) (E := H) (F := H)
    (f := action seed M) (g := fun t => finiteHistory seed t M)
    (by exact action_continuous seed M) (history_continuous seed M)
  exact continuous.intervalIntegrable a b

theorem forcingHistory_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (forcingHistory seed M) volume a b := by
  convert! (rateHistory_integrable seed M a b).sub (actionHistory_integrable seed M a b) using 1
  funext time
  exact forcingHistory_difference seed M time

theorem source_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    finiteHistory seed b M-finiteHistory seed a M=
      ∫ time in a..b,action seed M time (finiteHistory seed time M)+forcingHistory seed M time := by
  rw [history_write]
  apply intervalIntegral.integral_congr
  intro time _
  exact source_equation seed M time

theorem source_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun time => finiteHistory seed time M) a b :=
  NativeUnheatedIntegralBilinear.written_ac _ _ (rateHistory_integrable seed M a b)
    (fun x _ y _ => history_write seed M x y)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem velocityRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    velocityRate seed M (step.2.clockAdvance+time)=velocityRate step.1 M time := by
  simp only [velocityRate,if_pos nonnegative,if_pos (add_nonneg step.2.clockAdvance_pos.le nonnegative),
    NativeUnifiedCompleteSource.source_generated_next seed step generated time nonnegative]

theorem rateHistory_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    rateHistory seed M (step.2.clockAdvance+time)=rateHistory step.1 M time := by
  apply Lp.ext
  filter_upwards [rateHistory_ae seed M (step.2.clockAdvance+time),rateHistory_ae step.1 M time,
    NativeWindowTraceEndpointWindow.average_interval] with shift first second support
  rw [first,second,add_sub_assoc,velocityRate_next seed M step generated (time-shift) (by linarith [support.2])]

theorem forcingHistory_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcingHistory seed M (step.2.clockAdvance+time)=forcingHistory step.1 M time := by
  have operators := whole_next seed M step generated time nonnegative
  simp only [Prod.mk.injEq] at operators
  have states := NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M
  calc
    _ = rateHistory seed M (step.2.clockAdvance+time)-
        action seed M (step.2.clockAdvance+time) (finiteHistory seed (step.2.clockAdvance+time) M) :=
      forcingHistory_difference seed M _
    _ = rateHistory step.1 M time-action step.1 M time (finiteHistory step.1 time M) :=
      congrArg₂ (fun (x y : H) => x-y) (rateHistory_next seed M step generated time nonnegative)
        (congrArg₂ (fun (op : H →L[ℝ] H) (v : H) => op v) operators.1 states)
    _ = _ := (forcingHistory_difference step.1 M time).symm

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseen

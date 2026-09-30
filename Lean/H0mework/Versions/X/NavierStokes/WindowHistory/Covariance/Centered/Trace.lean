import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.Mean

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowAbsoluteTimeFourier (Fiber Space physical field)
noncomputable section
local instance tracePhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance tracePhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def pairReal : Lp ℝ 2 (volume : Measure Torus) →L[ℝ]
    Lp ℝ 2 (volume : Measure Torus) →L[ℝ] Lp ℝ 1 (volume : Measure Torus) :=
  (innerSL ℝ (E := ℝ)).holderL volume 2 2 1

theorem pairReal_ae (u v : Lp ℝ 2 (volume : Measure Torus)) :
    pairReal u v=ᵐ[volume] fun x => u x*v x := by
  filter_upwards [(innerSL ℝ (E := ℝ)).coeFn_holder (r := 1) u v] with x actual
  change ((innerSL ℝ (E := ℝ)).holder 1 u v) x=u x*v x
  rw [actual]
  change inner ℝ (u x) (v x)=u x*v x
  exact Real.inner_apply _ _

def finiteTrace (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Lp ℝ 1 (volume : Measure Torus) :=
  ∑i : Coordinate,
    (NativeWindowAbsoluteTimePhysicalStress.pair
      (physical (modes M) i (NativeWindowAbsoluteTimeSource.history seed time))
      (physical (modes M) i (NativeWindowAbsoluteTimeSource.history seed time))-
      pairReal (finiteMeanField seed M time i) (finiteMeanField seed M time i))

def fullTrace (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Lp ℝ 1 (volume : Measure Torus) :=
  ∑i : Coordinate,
    (NativeWindowAbsoluteTimePhysicalStress.pair
      (NativeWindowAbsoluteTimePhysicalCompletion.synthesis i
        (NativeWindowAbsoluteTimeSource.history seed time))
      (NativeWindowAbsoluteTimePhysicalCompletion.synthesis i
        (NativeWindowAbsoluteTimeSource.history seed time))-
      pairReal (fullMeanField seed time i) (fullMeanField seed time i))

theorem finiteTrace_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun M => finiteTrace seed M time) atTop (𝓝 (fullTrace seed time)) := by
  unfold finiteTrace fullTrace
  apply tendsto_finsetSum
  intro i _
  have rawContinuous : Continuous (fun v : Space =>
      NativeWindowAbsoluteTimePhysicalStress.pair v v) :=
    NativeWindowAbsoluteTimePhysicalStress.pair.continuous.clm_apply continuous_id
  have meanContinuous : Continuous (fun v : Lp ℝ 2 (volume : Measure Torus) => pairReal v v) :=
    pairReal.continuous.clm_apply continuous_id
  exact (rawContinuous.tendsto _ |>.comp
    (NativeWindowAbsoluteTimePhysicalCompletion.source_tendsto seed time i)).sub
      (meanContinuous.tendsto _ |>.comp (finiteMeanField_tendsto seed time i))

theorem meanValue_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (i : Coordinate) :
    NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
      (NativeWindowHistoryMeanAction.meanValue seed M time)=
        NativeWindowFiniteGramFourier.read (modes M) i
          (NativeForwardWindowSource.source seed time) := by
  apply ContinuousMap.ext
  intro x
  rw [NativeWindowStressOseenTest.evaluate_apply]
  simp [NativeWindowFiniteGramFourier.read,NativeWindowFiniteGramFourier.complexRead,
    NativeWindowStressHeatBalance.basis,NativeWindowHistoryMeanAction.meanValue,
    NativeForwardWindowPairingReadout.velocityRead]
  have row (k : IntegerWavevector) (inside : k∈modes M) :
      (NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.history seed time))).1 k i=
          NativeEndpointVelocityCarrier.wholeVelocity
            (NativeForwardWindowSource.source seed time).fst k i := by
    change (NativeWholeH1Mixed.restrict M
      (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.history seed time))).1 k i=_
    rw [NativeWholeH1Mixed.restrict_row,if_pos inside,
      NativeWindowHistoryMeanProjection.source_mean]
  have first := Finset.sum_congr rfl (fun k inside => congrArg (fun z : ℂ =>
    z.re*((UnitAddTorus.mFourier k) x).re) (row k inside))
  have last := Finset.sum_congr rfl (fun k inside => congrArg (fun z : ℂ =>
    z.im*((UnitAddTorus.mFourier k) x).im) (row k inside))
  rw [first,last]
  rfl

theorem pairReal_toLp (g : C(Torus,ℝ)) :
    pairReal ((ContinuousMap.toLp 2 volume ℝ) g) ((ContinuousMap.toLp 2 volume ℝ) g)=
      (ContinuousMap.toLp 1 volume ℝ) (g*g) := by
  apply Lp.ext
  filter_upwards [pairReal_ae ((ContinuousMap.toLp 2 volume ℝ) g) ((ContinuousMap.toLp 2 volume ℝ) g),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (volume : Measure Torus) g,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus) (g*g)]
    with x actual read target
  rw [actual,read,target]
  rfl

theorem finite_trace_field (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) :
    NativeWindowHistoryCreationCovariance.trace seed M time=
      (∑i : Coordinate,NativeWindowFiniteGramFourier.stress seed time (modes M) i i)-
      (∑i : Coordinate,
        (NativeWindowFiniteGramFourier.read (modes M) i
          (NativeForwardWindowSource.source seed time))^2) := by
  apply ContinuousMap.ext
  intro x
  have raw:=NativeWindowHistoryCovarianceCurrent.gram seed M time x
  have split:=NativeWindowHistoryCovarianceCurrent.covariance_split seed M time nonnegative x
  simp only [ContinuousMap.sub_apply,ContinuousMap.sum_apply,ContinuousMap.pow_apply] at raw split ⊢
  have same (i : Coordinate) : NativeWindowStressOseenTest.evaluate (modes M) (modes M) i
      (NativeWindowHistoryMeanAction.meanValue seed M time) x=
        NativeWindowFiniteGramFourier.read (modes M) i (NativeForwardWindowSource.source seed time) x :=
    congrArg (fun f : C(Torus,ℝ) => f x) (meanValue_read seed M time i)
  simp_rw [same] at split
  linarith only [raw,split]

theorem finiteTrace_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (nonnegative : 0≤time) :
    finiteTrace seed M time=
      (ContinuousMap.toLp 1 volume ℝ)
        (NativeWindowHistoryCreationCovariance.trace seed M time) := by
  unfold finiteTrace
  simp_rw [NativeWindowAbsoluteTimePhysicalStress.finite_pair,finiteMeanField_read,pairReal_toLp]
  simp only [← pow_two]
  let read : C(Torus,ℝ) →L[ℝ] Lp ℝ 1 (volume : Measure Torus) := ContinuousMap.toLp 1 volume ℝ
  change (∑i : Coordinate,
    (read (NativeWindowFiniteGramFourier.stress seed time (modes M) i i)-
    read ((NativeWindowFiniteGramFourier.read (modes M) i
      (NativeForwardWindowSource.source seed time))^2)))=_
  calc
    _=read ((∑i : Coordinate,NativeWindowFiniteGramFourier.stress seed time (modes M) i i)-
        (∑i : Coordinate,(NativeWindowFiniteGramFourier.read (modes M) i
          (NativeForwardWindowSource.source seed time))^2)) := by
      rw [map_sub,map_sum,map_sum,Finset.sum_sub_distrib]
    _=_ := congrArg read (finite_trace_field seed M time nonnegative).symm

private def integrateAgainst (g : C(Torus,ℝ)) : Lp ℝ 1 (volume : Measure Torus) →L[ℝ] ℝ :=
  (L1.integralCLM' ℝ).comp ((innerSL ℝ (E := ℝ)).holderL volume ∞ 1 1
    ((ContinuousMap.toLp ∞ volume ℝ) g))

private theorem integrateAgainst_apply (g : C(Torus,ℝ))
    (f : Lp ℝ 1 (volume : Measure Torus)) :
    integrateAgainst g f=∫x : Torus,g x*f x := by
  rw [integrateAgainst,ContinuousLinearMap.comp_apply,ContinuousLinearMap.holderL_apply_apply,
    ← L1.integral_eq',L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [(innerSL ℝ (E := ℝ)).coeFn_holder (r := 1)
    ((ContinuousMap.toLp ∞ volume ℝ) g) f,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) (volume : Measure Torus) g] with x actual original
  rw [actual,original]
  change f x*g x=g x*f x
  ring

theorem trace_square_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (nonnegative : 0≤time) (g : C(Torus,ℝ)) :
    Tendsto (fun M => ∫x : Torus,
      NativeWindowHistoryCreationCovariance.trace seed M time x*(g x)^2)
      atTop (𝓝 (∫x : Torus,fullTrace seed time x*(g x)^2)) := by
  have source:=(integrateAgainst (g*g)).continuous.tendsto (fullTrace seed time) |>.comp
    (finiteTrace_tendsto seed time)
  have finite (M : ℕ) : integrateAgainst (g*g) (finiteTrace seed M time)=
      ∫x : Torus,NativeWindowHistoryCreationCovariance.trace seed M time x*(g x)^2 := by
    rw [finiteTrace_read seed M time nonnegative,integrateAgainst_apply]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus)
      (NativeWindowHistoryCreationCovariance.trace seed M time)] with x actual
    rw [actual]
    simp only [ContinuousMap.mul_apply]
    ring
  have complete : integrateAgainst (g*g) (fullTrace seed time)=
      ∫x : Torus,fullTrace seed time x*(g x)^2 := by
    rw [integrateAgainst_apply]
    apply integral_congr_ae
    filter_upwards with x
    simp only [ContinuousMap.mul_apply]
    ring
  simpa only [Function.comp_def,finite,complete] using source

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem finite_trace_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowHistoryCreationCovariance.trace seed M (step.2.clockAdvance+time)=
      NativeWindowHistoryCreationCovariance.trace step.1 M time := by
  have later : 0 ≤ step.2.clockAdvance+time :=
    add_nonneg step.2.clockAdvance_pos.le nonnegative
  rw [finite_trace_field seed M (step.2.clockAdvance+time) later,
    finite_trace_field step.1 M time nonnegative]
  simp only [NativeWindowFiniteGramFourier.stress_next seed step generated time nonnegative (modes M),
    NativeForwardWindowSource.source_next seed step generated time nonnegative]

theorem fullTrace_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    fullTrace seed (step.2.clockAdvance+time)=fullTrace step.1 time := by
  have same : (fun M => finiteTrace seed M (step.2.clockAdvance+time))=
      (fun M => finiteTrace step.1 M time) := by
    funext M
    rw [finiteTrace_read seed M (step.2.clockAdvance+time)
      (add_nonneg step.2.clockAdvance_pos.le nonnegative),
      finiteTrace_read step.1 M time nonnegative,
      finite_trace_next seed M step generated time nonnegative]
  have source:=finiteTrace_tendsto seed (step.2.clockAdvance+time)
  rw [same] at source
  exact tendsto_nhds_unique source (finiteTrace_tendsto step.1 time)


end
end SaturationMonoid.NavierStokes.NativeCenteredCovariance

import H0mework.NavierStokes.WindowSchurAbsolute.Isometry
import H0mework.NavierStokes.WindowSchurAbsolute.Source
import H0mework.NavierStokes.WindowSchurMean.Projection
import H0mework.NavierStokes.WindowHistoryRecovery.Covariance

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeBridge
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowKernelHalfDensity (rootKernel)
open NativeWindowAbsoluteTimeIsometry (map map_ae clock clock_ae)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}
abbrev Lag := NativeWindowTraceWholeHistory.H
abbrev H := NativeWindowAbsoluteTimeSource.H

theorem source_map (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    map wholePhysical time (NativeWindowTraceWholeHistory.history seed time)=NativeWindowAbsoluteTimeSource.history seed time := by
  apply Lp.ext
  have weighted:=NativeWindowAbsoluteTimeIsometry.weighted_ae wholePhysical
    (NativeWindowTraceWholeHistory.history_ae seed time)
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae weighted
  filter_upwards [map_ae wholePhysical time (NativeWindowTraceWholeHistory.history seed time),
    NativeWindowAbsoluteTimeSource.history_ae seed time,shifted] with s first last original
  rw [first,last]
  simpa only [NativeWindowTraceWholeHistory.sample,sub_sub_cancel] using original

def mean (time : ℝ) : H →L[ℝ] wholePhysical :=
  NativeWindowHistoryMeanProjection.mean.comp (NativeWindowAbsoluteTimeIsometry.pull wholePhysical time)

def projection (time : ℝ) : H →L[ℝ] H :=
  NativeWindowAbsoluteTimeIsometry.operator wholePhysical time NativeWindowHistoryMeanProjection.projection

def residual (time : ℝ) : H →L[ℝ] H := ContinuousLinearMap.id ℝ H-projection time

theorem mean_map (time : ℝ) (v : Lag) : mean time (map wholePhysical time v)=NativeWindowHistoryMeanProjection.mean v := by
  simp only [mean,ContinuousLinearMap.comp_apply,NativeWindowAbsoluteTimeIsometry.pull_map]

theorem projection_map (time : ℝ) (v : Lag) :
    projection time (map wholePhysical time v)=map wholePhysical time (NativeWindowHistoryMeanProjection.projection v) :=
  NativeWindowAbsoluteTimeIsometry.operator_map wholePhysical time _ v

theorem residual_map (time : ℝ) (v : Lag) :
    residual time (map wholePhysical time v)=map wholePhysical time (NativeWindowHistoryMeanProjection.residual v) := by
  change map wholePhysical time v-projection time (map wholePhysical time v)=_
  rw [projection_map]
  exact ((map wholePhysical time).toContinuousLinearMap.map_sub v (NativeWindowHistoryMeanProjection.projection v)).symm

theorem orthogonal (time : ℝ) (u v : Lag) :
    inner ℝ (projection time (map wholePhysical time u)) (residual time (map wholePhysical time v))=0 := by
  rw [projection_map,residual_map,NativeWindowAbsoluteTimeIsometry.pairing]
  exact NativeWindowHistoryMeanProjection.orthogonal u v

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (mean time (NativeWindowAbsoluteTimeSource.history seed time)).1=(NativeForwardWindowSource.source seed time).fst := by
  rw [← source_map,mean_map]
  exact NativeWindowHistoryMeanProjection.source_mean seed time

def stress (v : H) : NativeCompleteStressCarrier.Space :=
  NativeWindowHistoryCovarianceRecovery.fiber.lpPairing (volume : Measure ℝ) 2 2 v v

theorem stress_map (time : ℝ) (v : Lag) :
    stress (map wholePhysical time v)=NativeWindowHistoryCovarianceRecovery.stress v :=
  NativeWindowAbsoluteTimeIsometry.bilinear_pairing wholePhysical NativeWindowHistoryCovarianceRecovery.fiber time v v

def read (time : ℝ) (v : H) : NativeCompleteStressAction.FullSpace :=
  WithLp.toLp 2 ((mean time v).1,stress v)

theorem read_map (time : ℝ) (v : Lag) :
    read time (map wholePhysical time v)=NativeWindowHistoryCovarianceRecovery.read v := by
  simp only [read,mean_map,stress_map]
  rfl

theorem source_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read time (NativeWindowAbsoluteTimeSource.history seed time)=NativeForwardWindowSource.source seed time := by
  rw [← source_map,read_map,NativeWindowHistoryCovarianceRecovery.source_read]

theorem source_residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    stress (NativeWindowAbsoluteTimeSource.history seed time)-
      NativeStressTimeAlgebra.quadratic (mean time (NativeWindowAbsoluteTimeSource.history seed time)).1=
    (NativeForwardWindowSource.source seed time).snd-
      NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst := by
  rw [← source_map,stress_map,mean_map]
  exact NativeWindowHistoryCovarianceRecovery.source_residual seed time

def absoluteAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  NativeWindowAbsoluteTimeIsometry.operator wholePhysical time (NativeWindowHistoryOseen.action seed M time)

theorem action_on_image (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : Lag) :
    absoluteAction seed M time (map wholePhysical time v)=map wholePhysical time (NativeWindowHistoryOseen.action seed M time v) :=
  NativeWindowAbsoluteTimeIsometry.operator_map wholePhysical time _ v

theorem actual_action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : Lag) :
    absoluteAction seed M time (map wholePhysical time v)=ᵐ[volume]
      fun s => NativeWindowHistoryOseen.forwardFiber seed M s (map wholePhysical time v s) := by
  rw [action_on_image]
  have weighted:=NativeWindowAbsoluteTimeIsometry.weighted_ae wholePhysical
    (NativeWindowHistoryOseen.action_ae seed M time v)
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae weighted
  filter_upwards [map_ae wholePhysical time (NativeWindowHistoryOseen.action seed M time v),map_ae wholePhysical time v,shifted]
    with s first last actual
  rw [first,last,map_smul]
  simpa only [NativeWindowHistoryOseen.forwardField,sub_sub_cancel] using actual

def finiteHistory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  (NativeWindowTraceWholeHistory.projection M).compLpL 2 volume (NativeWindowAbsoluteTimeSource.history seed time)

def finiteRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  (NativeWindowTraceWholeHistory.projection M).compLpL 2 volume (NativeWindowAbsoluteTimeSource.rate seed time)

theorem finite_map (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    map wholePhysical time (NativeWindowTraceWholeHistory.finiteHistory seed time M)=finiteHistory seed M time := by
  rw [NativeWindowTraceWholeHistory.finiteHistory,NativeWindowAbsoluteTimeIsometry.naturality,source_map]
  rfl

theorem finite_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (finiteHistory seed M) (finiteRate seed M time) time := by
  let L : H →L[ℝ] H:=(NativeWindowTraceWholeHistory.projection M).compLpL 2 (volume : Measure ℝ)
  exact L.hasFDerivAt.comp_hasDerivAt (E := H) (F := H) time
    (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)

theorem projected_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowTraceWholeHistory.projection M (NativeWindowTraceWholeHistory.original seed time)=
      NativeWindowHistoryOseen.velocityPath seed M time := by
  simp only [NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,NativeWindowHistoryOseen.restrict_original_total]
  rfl

theorem raw_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    MemLp (NativeWindowHistoryOseen.velocityPath seed M) ∞ (volume : Measure ℝ) := by
  apply memLp_top_of_bound (NativeWindowHistoryOseen.velocityPath_continuous seed M).aestronglyMeasurable
    (NativeUnifiedCompleteSource.budget seed)
  exact Eventually.of_forall fun s => by
    rw [← projected_original]
    exact (NativeWindowHistoryWholeRecovery.projection_norm M _).trans (NativeWindowTraceWholeHistory.original_bound seed s)

theorem rawRate_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    MemLp (NativeWindowHistoryOseen.velocityRate seed M) ∞ (volume : Measure ℝ) :=
  memLp_top_of_bound (NativeWindowHistoryOseen.velocityRate_measurable seed M)
    (NativeWindowHistoryOseen.rateBudget seed M) (Eventually.of_forall (NativeWindowHistoryOseen.velocityRate_bound seed M))

def sampleDerivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  NativeWindowAbsoluteTimeCarrier.field rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
    (NativeWindowHistoryOseen.velocityRate seed M) (rawRate_memLp seed M) time-
  NativeWindowAbsoluteTimeCarrier.field (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    (NativeWindowHistoryOseen.velocityPath seed M) (raw_memLp seed M) time

theorem finiteRate_field (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    finiteRate seed M time=NativeWindowAbsoluteTimeCarrier.field (deriv rootKernel)
      (NativeWindowKernelHalfDensity.derivative_memLp 2) (NativeWindowHistoryOseen.velocityPath seed M) (raw_memLp seed M) time := by
  apply Lp.ext
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (NativeWindowAbsoluteTimeSource.rate seed time),
    NativeWindowAbsoluteTimeSource.rate_ae seed time,NativeWindowAbsoluteTimeCarrier.field_ae (deriv rootKernel)
      (NativeWindowKernelHalfDensity.derivative_memLp 2) (NativeWindowHistoryOseen.velocityPath seed M) (raw_memLp seed M) time]
    with s first last target
  change finiteRate seed M time s=_ at first
  rw [first,last,target,map_smul,projected_original]

theorem sampleDerivative_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    sampleDerivative seed M time=map wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time)-finiteRate seed M time := by
  rw [sampleDerivative,finiteRate_field]
  congr 1
  apply Lp.ext
  have weighted:=NativeWindowAbsoluteTimeIsometry.weighted_ae wholePhysical
    (NativeWindowHistoryOseen.rateHistory_ae seed M time)
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae weighted
  filter_upwards [map_ae wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time),
    NativeWindowAbsoluteTimeCarrier.field_ae rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
      (NativeWindowHistoryOseen.velocityRate seed M) (rawRate_memLp seed M) time,shifted] with s first last actual
  rw [first,last]
  simpa only [sub_sub_cancel] using actual.symm

theorem actual_sample_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ s : ℝ,HasDerivAt (fun r => rootKernel (time-r) • NativeWindowHistoryOseen.velocityPath seed M r)
      (sampleDerivative seed M time s) s := by
  have kernel:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    NativeWindowKernelHalfDensity.source_derivative
  filter_upwards [kernel,NativeWindowHistoryOseen.velocityPath_derivative seed M,
    Lp.coeFn_sub
      (NativeWindowAbsoluteTimeCarrier.field rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
        (NativeWindowHistoryOseen.velocityRate seed M) (rawRate_memLp seed M) time)
      (NativeWindowAbsoluteTimeCarrier.field (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
        (NativeWindowHistoryOseen.velocityPath seed M) (raw_memLp seed M) time),
    NativeWindowAbsoluteTimeCarrier.field_ae rootKernel (NativeWindowKernelHalfDensity.root_memLp 2)
      (NativeWindowHistoryOseen.velocityRate seed M) (rawRate_memLp seed M) time,
    NativeWindowAbsoluteTimeCarrier.field_ae (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
      (NativeWindowHistoryOseen.velocityPath seed M) (raw_memLp seed M) time] with s actual source difference first last
  have scalar : HasDerivAt (fun r => rootKernel (time-r)) (-deriv rootKernel (time-s)) s := by
    simpa only [Function.comp_def,zero_sub,mul_neg,mul_one] using!
      actual.comp s ((hasDerivAt_const s time).sub (hasDerivAt_id s))
  have product:=scalar.smul source
  change sampleDerivative seed M time s=_ at difference
  rw [difference,Pi.sub_apply,first,last]
  simpa only [Pi.smul_apply,neg_smul,sub_eq_add_neg] using! product

theorem source_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    finiteRate seed M time=absoluteAction seed M time (finiteHistory seed M time)+
      map wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time)-sampleDerivative seed M time := by
  have acted : absoluteAction seed M time (finiteHistory seed M time)=map wholePhysical time
      (NativeWindowHistoryOseen.action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)) := by
    rw [← finite_map]
    exact action_on_image seed M time _
  have original:=congrArg (map wholePhysical time).toContinuousLinearMap (NativeWindowHistoryOseen.source_equation seed M time)
  have addition := (map wholePhysical time).toContinuousLinearMap.map_add
    (NativeWindowHistoryOseen.action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M))
    (NativeWindowHistoryOseen.forcingHistory seed M time)
  have split := original.trans addition
  change map wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time)=_ at split
  have joint := split.trans (congrArg (fun v : H => v+map wholePhysical time
    (NativeWindowHistoryOseen.forcingHistory seed M time)) acted.symm)
  have identity : finiteRate seed M time=map wholePhysical time (NativeWindowHistoryOseen.rateHistory seed M time)-sampleDerivative seed M time := by
    rw [sampleDerivative_original]
    abel
  exact identity.trans (congrArg (fun v : H => v-sampleDerivative seed M time) joint)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem source_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowAbsoluteTimeSource.history seed (step.2.clockAdvance+time)=
      clock wholePhysical step.2.clockAdvance (NativeWindowAbsoluteTimeSource.history step.1 time) := by
  rw [← source_map,NativeWindowTraceWholeHistory.history_next seed step generated time nonnegative,
    NativeWindowAbsoluteTimeIsometry.map_clock,source_map]

theorem rate_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowAbsoluteTimeSource.rate seed (step.2.clockAdvance+time)=
      clock wholePhysical step.2.clockAdvance (NativeWindowAbsoluteTimeSource.rate step.1 time) := by
  apply Lp.ext
  have preserves : MeasurePreserving (fun s : ℝ => s-step.2.clockAdvance) volume volume := by
    simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-step.2.clockAdvance)
  have shifted:=preserves.quasiMeasurePreserving.ae (NativeWindowAbsoluteTimeSource.rate_ae step.1 time)
  filter_upwards [NativeWindowAbsoluteTimeSource.rate_ae seed (step.2.clockAdvance+time),
    clock_ae wholePhysical step.2.clockAdvance (NativeWindowAbsoluteTimeSource.rate step.1 time),shifted]
    with s first last actual
  rw [first,last,actual]
  have lag : step.2.clockAdvance+time-s=time-(s-step.2.clockAdvance) := by ring
  rw [← lag]
  by_cases zero : deriv rootKernel (step.2.clockAdvance+time-s)=0
  · simp only [zero,zero_smul]
  · have inside : step.2.clockAdvance+time-s∈Icc (-2:ℝ) (-1) := by
      by_contra outside
      exact zero (NativeWindowAbsoluteTimeSource.rate_zero_outside _ outside)
    have sampleNonnegative : (0 : ℝ) ≤ s - step.2.clockAdvance := by linarith [inside.2]
    have source:=NativeWindowTraceWholeHistory.original_next seed step generated (s-step.2.clockAdvance) sampleNonnegative
    have same : NativeWindowTraceWholeHistory.original seed s=NativeWindowTraceWholeHistory.original step.1 (s-step.2.clockAdvance) := by
      simpa only [add_sub_cancel] using source
    rw [same]

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeBridge

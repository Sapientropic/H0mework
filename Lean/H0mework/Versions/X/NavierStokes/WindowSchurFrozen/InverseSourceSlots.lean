import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.SourceGraph
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Bridge

set_option autoImplicit false
open scoped Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySourceResolventSlots
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H velocityPath)
open NativeWindowHistoryMeanProjection (mean)
open NativeForwardWindowPairingReadout (averageMeasure density density_measurable)
open NativeWindowKernelHalfDensity (rootKernel)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeWindowHistorySourceResolventGraph (value window responseRead)
noncomputable section
variable {nu : Viscosity}

def kernelRatio (lag : ℝ) : ℝ := deriv rootKernel lag/rootKernel lag

theorem root_zero_rate (lag : ℝ) (zero : rootKernel lag=0) : deriv rootKernel lag=0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Eventually.of_forall fun x => by rw [zero]; exact NativeWindowKernelHalfDensity.nonnegative x

theorem root_ratio (lag : ℝ) : rootKernel lag*kernelRatio lag=deriv rootKernel lag := by
  by_cases zero : rootKernel lag=0
  · rw [zero,zero_mul,root_zero_rate lag zero]
  · unfold kernelRatio
    field_simp

theorem gram_ratio (lag : ℝ) : NativeForwardWindowSource.kernel lag*kernelRatio lag=
    rootKernel lag*deriv rootKernel lag := by
  rw [← NativeWindowKernelHalfDensity.square,show rootKernel lag^2*kernelRatio lag=
    rootKernel lag*(rootKernel lag*kernelRatio lag) by ring,root_ratio]

private theorem ratio_measurable : AEStronglyMeasurable kernelRatio (volume : Measure ℝ) := by
  simpa only [kernelRatio,div_eq_mul_inv] using!
    (aestronglyMeasurable_deriv (𝕜 := ℝ) (F := ℝ) rootKernel volume).mul
      NativeWindowKernelHalfDensity.continuous.measurable.inv.aestronglyMeasurable

def weightedPoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : wholePhysical :=
  kernelRatio lag • velocityPath seed M (time-lag)

theorem weighted_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    MemLp (weightedPoint seed M time) 2 averageMeasure := by
  have raw : MemLp (fun lag => velocityPath seed M (time-lag)) ∞ (volume : Measure ℝ) :=
    (NativeWindowAbsoluteTimeBridge.raw_memLp seed M).comp_measurePreserving
      (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)
  have product : MemLp (fun lag => deriv rootKernel lag • velocityPath seed M (time-lag)) 2 (volume : Measure ℝ) := by
    simpa only [Pi.smul_apply] using! raw.smul (NativeWindowKernelHalfDensity.derivative_memLp 2)
  have measured : AEStronglyMeasurable (weightedPoint seed M time) averageMeasure :=
    (ratio_measurable.smul raw.aestronglyMeasurable).mono_ac
      (withDensity_absolutelyContinuous volume (fun lag => (density lag : ℝ≥0∞)))
  apply (memLp_two_iff_integrable_sq_norm measured).mpr
  apply (integrable_withDensity_iff_integrable_smul density_measurable).mpr
  apply (product.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).congr
  filter_upwards with lag
  change ‖deriv rootKernel lag • velocityPath seed M (time-lag)‖^2=
    NativeForwardWindowSource.kernel lag*‖weightedPoint seed M time lag‖^2
  rw [← NativeWindowAbsoluteTimeIsometry.norm_square_row wholePhysical,weightedPoint,smul_smul,root_ratio]

def weightedHistory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  (weighted_memLp seed M time).toLp (weightedPoint seed M time)

theorem weighted_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    weightedHistory seed M time=ᵐ[averageMeasure] weightedPoint seed M time :=
  (weighted_memLp seed M time).coeFn_toLp

theorem weighted_map (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowAbsoluteTimeIsometry.map wholePhysical time (weightedHistory seed M time)=
      NativeWindowAbsoluteTimeBridge.finiteRate seed M time := by
  rw [NativeWindowAbsoluteTimeBridge.finiteRate_field]
  apply Lp.ext
  have read:=NativeWindowAbsoluteTimeIsometry.weighted_ae wholePhysical (weighted_ae seed M time)
  have shifted:=(Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae read
  filter_upwards [NativeWindowAbsoluteTimeIsometry.map_ae wholePhysical time (weightedHistory seed M time),shifted,
    NativeWindowAbsoluteTimeCarrier.field_ae (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
      (velocityPath seed M) (NativeWindowAbsoluteTimeBridge.raw_memLp seed M) time] with sample mapped actual target
  rw [mapped,actual,weightedPoint,smul_smul,root_ratio,sub_sub_cancel,target]

/-- This is the independent absolute-time rate, not the old lag-history momentum rate. -/
theorem pull_rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowAbsoluteTimeIsometry.pull wholePhysical time (NativeWindowAbsoluteTimeBridge.finiteRate seed M time)=
      weightedHistory seed M time := by
  rw [← weighted_map,NativeWindowAbsoluteTimeIsometry.pull_map]

theorem weighted_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowTraceWholeHistory.projected M (weightedHistory seed M time)=weightedHistory seed M time := by
  apply Lp.ext
  filter_upwards [(NativeWindowTraceWholeHistory.projection M).coeFn_compLpL (weightedHistory seed M time),
    weighted_ae seed M time] with lag projected raw
  change NativeWindowTraceWholeHistory.projected M (weightedHistory seed M time) lag=
    NativeWindowTraceWholeHistory.projection M (weightedHistory seed M time lag) at projected
  rw [projected,raw,weightedPoint,map_smul]
  simp only [velocityPath,NativeWindowTraceWholeHistory.projection,ContinuousLinearMap.comp_apply,NativePhysicalPairing.restrict_include]

theorem mean_kernel_rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (kernelAction seed M time (weightedHistory seed M time))=(1/2:ℝ) • window seed M 1 time := by
  rw [NativeWindowHistoryMeanProjection.mean_original]
  have original : (fun lag => kernelAction seed M time (weightedHistory seed M time) lag)=ᵐ[averageMeasure]
      fun lag => kernelRatio lag • value seed M (time-lag) := by
    filter_upwards [kernelAction_ae seed M time (weightedHistory seed M time),weighted_ae seed M time] with lag acted raw
    rw [acted,raw,weightedPoint,map_smul]
    rfl
  rw [integral_congr_ae original,NativeForwardWindowPairingReadout.density_integral]
  have read : (fun lag => NativeForwardWindowSource.kernel lag • (kernelRatio lag • value seed M (time-lag)))=ᵐ[volume]
      fun lag => (1/2:ℝ) • (NativeForwardWindowJets.kernelJet 1 lag • value seed M (time-lag)) := by
    filter_upwards [NativeWindowKernelHalfDensity.source_gram_rate] with lag actual
    have scalar : NativeForwardWindowSource.kernel lag*kernelRatio lag=(1/2:ℝ)*NativeForwardWindowJets.kernelJet 1 lag := by
      rw [gram_ratio]
      simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_one]
      linarith only [actual]
    rw [smul_smul,scalar,smul_smul]
  rw [integral_congr_ae read,integral_smul]
  rfl

private theorem lp_contract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (contract : ∀ u,‖P u‖ ≤ ‖u‖) (v : Lp E 2 (volume : Measure ℝ)) :
    ‖P.compLpL 2 volume v‖ ≤ ‖v‖ := by
  have point : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun u => by simpa only [one_mul] using contract u)
  have lifted:‖P.compLpL 2 (volume : Measure ℝ)‖ ≤ 1:=P.norm_compLpL_le.trans point
  exact ((P.compLpL 2 volume).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_right lifted (norm_nonneg v)).trans_eq (one_mul _))

theorem weighted_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖weightedHistory seed M time‖ ≤ NativeWindowAbsoluteTimeSource.rateBudget seed := by
  have paid:=lp_contract (E := wholePhysical) (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowHistoryWholeRecovery.projection_norm M) (NativeWindowAbsoluteTimeSource.rate seed time)
  rw [← NativeWindowAbsoluteTimeIsometry.norm_map wholePhysical time (weightedHistory seed M time),weighted_map]
  exact paid.trans (NativeWindowAbsoluteTimeSource.source_rate_bound seed time)

private theorem factor_solved (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) (z : wholePhysical)
    (kept : NativeWindowTraceWholeHistory.projected M v=v) (read : mean (kernelAction seed M time v)=z) :
    responseRead seed M time v=NativeWindowMeanEffectiveGraph.load seed M time z-mean v := by
  have actual:=NativeWindowHistorySourceResolventGraph.response_factor seed M time v
  rw [kept,read] at actual
  exact eq_sub_of_add_eq' actual

theorem response_rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    responseRead seed M time (NativeWindowAbsoluteTimeIsometry.pull wholePhysical time
      (NativeWindowAbsoluteTimeBridge.finiteRate seed M time))=
        (1/2:ℝ) • NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time)-
          mean (NativeWindowAbsoluteTimeIsometry.pull wholePhysical time (NativeWindowAbsoluteTimeBridge.finiteRate seed M time)) := by
  have linear : NativeWindowMeanEffectiveGraph.load seed M time ((1/2:ℝ) • window seed M 1 time)=
      (1/2:ℝ) • NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time) := by
    simp only [NativeWindowMeanEffectiveGraph.load,map_smul,smul_sub]
  calc
    _=responseRead seed M time (weightedHistory seed M time) := congrArg (responseRead seed M time) (pull_rate seed M time)
    _=NativeWindowMeanEffectiveGraph.load seed M time ((1/2:ℝ) • window seed M 1 time)-mean (weightedHistory seed M time) :=
      factor_solved seed M time _ _ (weighted_projected seed M time) (mean_kernel_rate seed M time)
    _=_ := congrArg₂ (fun x y : wholePhysical => x-y) linear (congrArg mean (pull_rate seed M time)).symm

private theorem difference_square {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u-v‖^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
  have triangle:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
  nlinarith only [triangle,sq_nonneg (‖u‖-‖v‖)]

private theorem mean_bound (v : H) (B : ℝ) (paid : ‖v‖ ≤ B) : ‖mean v‖^2 ≤ B^2 := by
  have split:=NativeWindowHistoryMeanProjection.energy_split v
  change ‖v‖^2=‖NativeWindowHistoryMeanProjection.embed (mean v)‖^2+
    ‖NativeWindowHistoryMeanProjection.residual v‖^2 at split
  rw [NativeWindowHistoryMeanProjection.embed_norm] at split
  have square:=pow_le_pow_left₀ (norm_nonneg v) paid 2
  nlinarith only [split,square,sq_nonneg ‖NativeWindowHistoryMeanProjection.residual v‖]

private theorem half_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (C D : ℝ) (first : ‖u‖^2 ≤ C) (last : ‖v‖^2 ≤ D) :
    ‖(1/2:ℝ) • u-v‖^2 ≤ 2*((1/4:ℝ)*C+D) := by
  have bound:=difference_square ((1/2:ℝ) • u) v
  rw [norm_smul,mul_pow] at bound
  norm_num only [Real.norm_eq_abs,abs_div,abs_one,abs_of_pos (by norm_num : (0:ℝ)<2)] at bound
  nlinarith only [bound,first,last]

theorem source_response_rate_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) :
    ‖responseRead seed M time (NativeWindowAbsoluteTimeIsometry.pull wholePhysical time
      (NativeWindowAbsoluteTimeBridge.finiteRate seed M time))‖^2 ≤
        2*((1/4:ℝ)*NativeWindowHistorySourceResolventGraph.loadedBudget seed horizon 1+
          NativeWindowAbsoluteTimeSource.rateBudget seed^2) := by
  have mass:=mean_bound (weightedHistory seed M time) _ (weighted_bound seed M time)
  have original:=congrArg (fun v : wholePhysical => ‖v‖^2) (response_rate seed M time)
  have target:=half_difference (E := wholePhysical) (NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time))
    (mean (weightedHistory seed M time)) _ _
    (NativeWindowHistorySourceResolventGraph.source_loaded_window_bound seed horizon M 1 time inside) mass
  have same:=congrArg (fun v : H => ‖(1/2:ℝ) • NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time)-mean v‖^2)
    (pull_rate seed M time)
  exact original.trans_le (same.trans_le target)

/-- The remaining input retains the independent sample derivative and complete original forcing. -/
def retainedInput (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  NativeWindowAbsoluteTimeIsometry.pull wholePhysical time
    (NativeWindowAbsoluteTimeIsometry.map wholePhysical time (NativeWindowHistoryOseen.forcingHistory seed M time)-
      NativeWindowAbsoluteTimeBridge.sampleDerivative seed M time)

def retainedLoad (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  (mean+responseRead seed M time) (retainedInput seed M time)

theorem retainedInput_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    retainedInput seed M time=NativeWindowHistoryOseen.forcingHistory seed M time-
      NativeWindowHistoryOseen.rateHistory seed M time+weightedHistory seed M time := by
  simp only [retainedInput,NativeWindowAbsoluteTimeBridge.sampleDerivative_original,map_sub,
    NativeWindowAbsoluteTimeIsometry.pull_map,pull_rate]
  abel

private theorem compressed_source (m B : H →L[ℝ] wholePhysical) (h f q : H) :
    m h-m q+(m f+B (h+f-q))=(m+B) (h+f-q) := by
  simp only [add_apply,map_sub,map_add]
  abel

theorem commonForce_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistorySchurCompletion.commonForce seed M time=
      NativeWindowMeanEffectiveGraph.load seed M time (window seed M 0 time)-
        (1/2:ℝ) • NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time)+retainedLoad seed M time := by
  let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
  let r:=weightedHistory seed M time
  let S: H →L[ℝ] wholePhysical:=mean+responseRead seed M time
  have original : NativeWindowHistorySchurCompletion.commonForce seed M time=
      S (h+NativeWindowHistoryOseen.forcingHistory seed M time-NativeWindowHistoryOseen.rateHistory seed M time) := by
    simpa only [NativeWindowHistorySchurCompletion.commonForce,NativeWindowHistorySchurAction.remainder,
      NativeWindowHistorySchurAction.temporalInput,NativeWindowHistorySourceResolventGraph.responseRead,
      ContinuousLinearMap.comp_apply,S,h] using! compressed_source mean (responseRead seed M time) h
        (NativeWindowHistoryOseen.forcingHistory seed M time) (NativeWindowHistoryOseen.rateHistory seed M time)
  have row : h+NativeWindowHistoryOseen.forcingHistory seed M time-NativeWindowHistoryOseen.rateHistory seed M time=
      h-r+retainedInput seed M time := by rw [retainedInput_original]; dsimp only [r]; abel
  have first : S h=NativeWindowMeanEffectiveGraph.load seed M time (window seed M 0 time) := by
    change mean h+responseRead seed M time h=_
    rw [NativeWindowHistorySourceResolventGraph.response_history]
    abel
  have last : S r=(1/2:ℝ) • NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time) := by
    have source:=response_rate seed M time
    simp only [pull_rate] at source
    change mean r+responseRead seed M time r=_
    rw [source]
    abel
  exact original.trans ((congrArg S row).trans ((S.map_add _ _).trans
    (congrArg (fun v : wholePhysical => v+retainedLoad seed M time)
      ((S.map_sub h r).trans (congrArg₂ (fun x y : wholePhysical => x-y) first last)))))

theorem source_regular_load_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) :
    ‖NativeWindowHistorySchurCompletion.commonForce seed M time-retainedLoad seed M time‖^2 ≤
      2*(NativeWindowHistorySourceResolventGraph.loadedBudget seed horizon 0+
        (1/4:ℝ)*NativeWindowHistorySourceResolventGraph.loadedBudget seed horizon 1) := by
  have equation:=commonForce_split seed M time
  have paid:=half_difference (E := wholePhysical) (NativeWindowMeanEffectiveGraph.load seed M time (window seed M 1 time))
    (NativeWindowMeanEffectiveGraph.load seed M time (window seed M 0 time)) _ _
    (NativeWindowHistorySourceResolventGraph.source_loaded_window_bound seed horizon M 1 time inside)
    (NativeWindowHistorySourceResolventGraph.source_loaded_window_bound seed horizon M 0 time inside)
  rw [equation,add_sub_cancel_right,norm_sub_rev]
  exact paid.trans_eq (by ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem weighted_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    weightedHistory seed M (step.2.clockAdvance+time)=weightedHistory step.1 M time := by
  apply Lp.ext
  filter_upwards [weighted_ae seed M (step.2.clockAdvance+time),weighted_ae step.1 M time,
    NativeWindowTraceEndpointWindow.average_interval] with lag first last support
  have physical : 0 ≤ time-lag := by linarith [support.2]
  have source:=NativeWindowTraceAdjoint.source_next seed M step generated (time-lag) physical
  simp only [Prod.mk.injEq] at source
  rw [first,last,weightedPoint,weightedPoint,add_sub_assoc,velocityPath,velocityPath,source.1]

theorem response_rate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    responseRead seed M (step.2.clockAdvance+time)
      (NativeWindowAbsoluteTimeIsometry.pull wholePhysical (step.2.clockAdvance+time)
        (NativeWindowAbsoluteTimeBridge.finiteRate seed M (step.2.clockAdvance+time)))=
      responseRead step.1 M time (NativeWindowAbsoluteTimeIsometry.pull wholePhysical time
        (NativeWindowAbsoluteTimeBridge.finiteRate step.1 M time)) := by
  simp only [pull_rate]
  exact congrArg₂ (fun (B : H →L[ℝ] wholePhysical) (v : H) => B v)
    (NativeWindowHistorySourceResolventGraph.responseRead_next seed M step generated time nonnegative)
    (weighted_next seed M step generated time nonnegative)

theorem retainedLoad_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    retainedLoad seed M (step.2.clockAdvance+time)=retainedLoad step.1 M time := by
  simp only [retainedLoad,retainedInput_original,
    NativeWindowHistorySourceResolventGraph.responseRead_next seed M step generated time nonnegative,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative,
    NativeWindowHistoryOseen.rateHistory_next seed M step generated time nonnegative,
    weighted_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySourceResolventSlots

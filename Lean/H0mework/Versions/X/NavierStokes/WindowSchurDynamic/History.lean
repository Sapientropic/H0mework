import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Test
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Derivative
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonForceTime
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Transpose

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicHistory
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H velocityPath velocityRate)
open NativeWindowHistoryFrozenInverse (kernel)
open NativeWindowHistorySchurAdvectorFiber (family)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem curve_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (curve : ℝ → Lp E 2 averageMeasure) (point : ℝ → ℝ → E)
    (rate : Lp E 2 averageMeasure) (pointRate : ℝ → E) (time B : ℝ)
    (read : ∀ t,curve t=ᵐ[averageMeasure] point t)
    (rateRead : rate=ᵐ[averageMeasure] pointRate)
    (derivative : ∀ᵐ lag ∂averageMeasure,HasDerivAt (fun t => point t lag) (pointRate lag) time)
    (domination : ∀ᶠ d in 𝓝[≠] (0 : ℝ),∀ᵐ lag ∂averageMeasure,
      ‖d⁻¹ • (point (time+d) lag-point time lag)-pointRate lag‖ ≤ B) :
    HasDerivAt curve rate time := by
  let error (d lag : ℝ) := d⁻¹ • (point (time+d) lag-point time lag)-pointRate lag
  have measuredPoint (t : ℝ) : AEStronglyMeasurable (point t) averageMeasure :=
    (Lp.memLp (curve t)).aestronglyMeasurable.congr (read t)
  have measuredRate : AEStronglyMeasurable pointRate averageMeasure :=
    (Lp.memLp rate).aestronglyMeasurable.congr rateRead
  have measured (d : ℝ) : AEStronglyMeasurable (fun lag => ‖error d lag‖^2) averageMeasure :=
    (((measuredPoint (time+d)).sub (measuredPoint time)).const_smul d⁻¹ |>.sub measuredRate).norm.pow 2
  have bounded : ∀ᶠ d in 𝓝[≠] (0 : ℝ),∀ᵐ lag ∂averageMeasure,‖‖error d lag‖^2‖ ≤ B^2 := by
    filter_upwards [domination] with d source
    filter_upwards [source] with lag paid
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) paid 2
  have convergence := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => B^2) (Eventually.of_forall measured) bounded (integrable_const _) (by
      filter_upwards [derivative] with lag actual
      have source := (tendsto_iff_norm_sub_tendsto_zero.mp actual.tendsto_slope_zero).pow 2
      simpa only [error,zero_pow (by decide : (2 : ℕ)≠0)] using! source)
  have identity (d : ℝ) : ‖d⁻¹ • (curve (time+d)-curve time)-rate‖^2=
      ∫ lag,‖error d lag‖^2 ∂averageMeasure := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (d⁻¹ • (curve (time+d)-curve time)) rate,
      Lp.coeFn_smul d⁻¹ (curve (time+d)-curve time),Lp.coeFn_sub (curve (time+d)) (curve time),
      read (time+d),read time,rateRead] with lag subtract scale difference first last actual
    rw [subtract,Pi.sub_apply,scale,Pi.smul_apply,difference,Pi.sub_apply,first,last,actual]
  have squares : Tendsto (fun d => ‖d⁻¹ • (curve (time+d)-curve time)-rate‖^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp only [identity]
    simpa only [integral_zero] using! convergence
  have normLimit := Real.continuous_sqrt.continuousAt.tendsto.comp squares
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,@abs_norm (Lp E 2 averageMeasure) _,Real.sqrt_zero] at normLimit
  exact (hasDerivAt_iff_tendsto_slope_zero (F := Lp E 2 averageMeasure)).mpr (tendsto_iff_norm_sub_tendsto_zero.mpr normLimit)

def slice (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : wholePhysical :=
  kernel seed M (time-lag) (commonForce seed M time)

theorem slice_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    completion seed M time=ᵐ[averageMeasure] slice seed M time :=
  NativeWindowHistoryInverseWindow.completion_original seed M time

private theorem linear_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] E) (L : E →L[ℝ] E) (u v x : E) :
    (L x+A u x)-(L x+A v x)=A (u-v) x := by
  rw [map_sub,sub_apply]
  abel

theorem forward_difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (s t : ℝ) (v : wholePhysical) :
    (NativeWindowHistoryOseen.forwardFiber seed M s-NativeWindowHistoryOseen.forwardFiber seed M t) v=
      family nu M (velocityPath seed M s-velocityPath seed M t) v := by
  simp only [sub_apply,NativeWindowHistoryDynamicTest.forward_split,NativeWindowHistoryDynamicTest.advection]
  exact linear_difference (family nu M) ((-nu.coeff) • NativeWindowHistoryAnnihilationControl.laplacianFiber nu M)
    (velocityPath seed M s) (velocityPath seed M t) v

theorem kernel_quotient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample d : ℝ) (v : wholePhysical) :
    d⁻¹ • (kernel seed M (sample+d) v-kernel seed M sample v)=
      kernel seed M (sample+d) (family nu M
        (d⁻¹ • (velocityPath seed M (sample+d)-velocityPath seed M sample)) (kernel seed M sample v)) := by
  rw [NativeWindowHistoryFrozenInverse.kernel_difference,forward_difference]
  simp only [map_smul,smul_apply]

private def operatorSize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] E) : ℝ := ‖A‖

private theorem operatorSize_nonnegative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] E) : 0 ≤ operatorSize A := norm_nonneg A

private theorem operatorSize_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] E) (u v : E) : ‖A u v‖ ≤ operatorSize A*‖u‖*‖v‖ :=
  ((A u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg v))

def transportSize (nu : Viscosity) (M : ℕ) : ℝ := operatorSize (E := wholePhysical) (family nu M)

theorem transportSize_nonnegative (nu : Viscosity) (M : ℕ) : 0 ≤ transportSize nu M :=
  operatorSize_nonnegative (E := wholePhysical) (family nu M)

theorem transportSize_bound (nu : Viscosity) (M : ℕ) (u v : wholePhysical) :
    ‖family nu M u v‖ ≤ transportSize nu M*‖u‖*‖v‖ :=
  operatorSize_bound (family nu M) u v

theorem kernel_quotient_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (sample d : ℝ) (v : wholePhysical) :
    ‖d⁻¹ • (kernel seed M (sample+d) v-kernel seed M sample v)‖ ≤
      transportSize nu M*NativeWindowHistoryOseen.rateBudget seed M*‖v‖ := by
  rw [kernel_quotient]
  apply (NativeWindowHistoryFrozenInverse.kernel_bound seed M (sample+d) _).trans
  have first := transportSize_bound nu M
    (d⁻¹ • (velocityPath seed M (sample+d)-velocityPath seed M sample)) (kernel seed M sample v)
  have operator := mul_le_mul_of_nonneg_left (NativeWindowHistoryOseen.velocityPath_quotient seed M sample d)
    (transportSize_nonnegative nu M)
  exact first.trans (mul_le_mul operator (NativeWindowHistoryFrozenInverse.kernel_bound seed M sample v)
    (norm_nonneg _) (mul_nonneg (transportSize_nonnegative nu M) (NativeWindowHistoryOseen.rateBudget_nonnegative seed M)))

private def multiply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp (E →L[ℝ] E) ∞ averageMeasure →L[ℝ] Lp E 2 averageMeasure →L[ℝ] Lp E 2 averageMeasure :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderL averageMeasure ∞ 2 2

def kernelProfile (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Lp (wholePhysical →L[ℝ] wholePhysical) ∞ averageMeasure :=
  NativeWindowHistoryOseen.profile (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) time

def kernelAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  multiply (E := wholePhysical) (kernelProfile seed M time)

theorem kernelAction_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    kernelAction seed M time v=ᵐ[averageMeasure] fun lag => kernel seed M (time-lag) (v lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical →L[ℝ] wholePhysical)
    (F := wholePhysical) (G := wholePhysical) (r := 2) (ContinuousLinearMap.id ℝ (wholePhysical →L[ℝ] wholePhysical))
    (kernelProfile seed M time) v,
    NativeWindowHistoryOseen.profile_ae (kernel seed M) (NativeWindowHistoryFrozenInverse.kernel_continuous seed M) time]
    with lag acted original
  change kernelAction seed M time v lag=kernelProfile seed M time lag (v lag) at acted
  rw [acted,show kernelProfile seed M time lag=kernel seed M (time-lag) from original]

def commonRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M 1 time)

def rateSlice (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) : wholePhysical :=
  kernel seed M (time-lag) (family nu M (velocityRate seed M (time-lag)) (slice seed M time lag)+commonRate seed M time)

def rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  kernelAction seed M time (NativeWindowHistorySchurTranspose.transposeAction seed M time
    (NativeWindowHistoryOseen.rateHistory seed M time)+NativeWindowHistoryMeanProjection.embed (commonRate seed M time))

theorem rate_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rate seed M time=ᵐ[averageMeasure] rateSlice seed M time := by
  filter_upwards [kernelAction_ae seed M time (NativeWindowHistorySchurTranspose.transposeAction seed M time
      (NativeWindowHistoryOseen.rateHistory seed M time)+NativeWindowHistoryMeanProjection.embed (commonRate seed M time)),
    Lp.coeFn_add (NativeWindowHistorySchurTranspose.transposeAction seed M time (NativeWindowHistoryOseen.rateHistory seed M time))
      (NativeWindowHistoryMeanProjection.embed (commonRate seed M time)),
    NativeWindowHistorySchurTranspose.transpose_ae seed M time (NativeWindowHistoryOseen.rateHistory seed M time),
    NativeWindowHistoryOseen.rateHistory_ae seed M time, slice_original seed M time,
    NativeWindowTraceWholeHistory.constant_ae (commonRate seed M time)]
    with lag acted added transported original completed constant
  change rate seed M time lag=_ at acted
  rw [acted,added,Pi.add_apply,transported,original,completed,show NativeWindowHistoryMeanProjection.embed
    (commonRate seed M time) lag=commonRate seed M time from constant]
  rfl

theorem slice_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) :
    ‖slice seed M time lag‖ ≤ ‖commonForce seed M time‖ :=
  NativeWindowHistoryFrozenInverse.kernel_bound seed M (time-lag) (commonForce seed M time)

def rateBound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  transportSize nu M*NativeWindowHistoryOseen.rateBudget seed M*‖commonForce seed M time‖+‖commonRate seed M time‖

theorem rateSlice_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) :
    ‖rateSlice seed M time lag‖ ≤ rateBound seed M time := by
  apply (NativeWindowHistoryFrozenInverse.kernel_bound seed M (time-lag) _).trans
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  exact (transportSize_bound nu M _ _).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryOseen.velocityRate_bound seed M (time-lag)) (transportSize_nonnegative nu M))
    (slice_bound seed M time lag) (norm_nonneg _)
    (mul_nonneg (transportSize_nonnegative nu M) (NativeWindowHistoryOseen.rateBudget_nonnegative seed M)))

private theorem moving_difference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : E →L[ℝ] E) (x y : E) (d : ℝ) :
    d⁻¹ • (K x-L y)=K (d⁻¹ • (x-y))+d⁻¹ • (K y-L y) := by
  simp only [map_smul,map_sub,smul_sub]
  abel

theorem slice_quotient_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time d lag : ℝ) :
    ‖d⁻¹ • (slice seed M (time+d) lag-slice seed M time lag)‖ ≤
      ‖d⁻¹ • (commonForce seed M (time+d)-commonForce seed M time)‖+
        transportSize nu M*NativeWindowHistoryOseen.rateBudget seed M*‖commonForce seed M time‖ := by
  have actual := moving_difference (kernel seed M (time+d-lag)) (kernel seed M (time-lag))
    (commonForce seed M (time+d)) (commonForce seed M time) d
  change d⁻¹ • (slice seed M (time+d) lag-slice seed M time lag)=_ at actual
  rw [actual]
  apply (norm_add_le _ _).trans
  apply add_le_add (NativeWindowHistoryFrozenInverse.kernel_bound seed M (time+d-lag) _)
  have last := kernel_quotient_bound seed M (time-lag) d (commonForce seed M time)
  simpa only [sub_add_eq_add_sub] using last

private theorem slope_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (time : ℝ) (actual : HasDerivAt f v time) :
    ∀ᶠ d in 𝓝[≠] (0 : ℝ),‖d⁻¹ • (f (time+d)-f time)‖ ≤ ‖v‖+1 := by
  have source := actual.tendsto_slope_zero.norm
  exact (source.eventually (gt_mem_nhds (lt_add_one ‖v‖))).mono fun _ paid => paid.le

theorem slice_domination (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∃ B : ℝ,∀ᶠ d in 𝓝[≠] (0 : ℝ),∀ lag : ℝ,
      ‖d⁻¹ • (slice seed M (time+d) lag-slice seed M time lag)-rateSlice seed M time lag‖ ≤ B := by
  have actual : HasDerivAt (commonForce seed M) (commonRate seed M time) time :=
    NativeWindowHistoryCommonForceTime.whole_hasDerivAt seed M time
  refine ⟨‖commonRate seed M time‖+1+
    transportSize nu M*NativeWindowHistoryOseen.rateBudget seed M*‖commonForce seed M time‖+rateBound seed M time,?_⟩
  filter_upwards [slope_bound (commonForce seed M) (commonRate seed M time) time actual] with d paid lag
  exact (norm_sub_le _ _).trans (add_le_add
    ((slice_quotient_bound seed M time d lag).trans (add_le_add paid le_rfl)) (rateSlice_bound seed M time lag))

theorem slice_physical (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) :
    slice seed M time lag=includeCLM (modes M) (modes_closed M)
      (NativeWindowHistoryDynamicKernel.kernel nu M (NativeWindowTraceAdjoint.value seed M (time-lag))
        (NativeWindowHistoryCommonForceTime.value seed M time)) := by
  rw [slice,← NativeWindowHistoryCommonForceTime.value_original,NativeWindowHistoryHeatWindow.included,
    NativeWindowHistoryDynamicKernel.kernel_source]
  rfl

theorem rateSlice_physical (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time lag : ℝ) :
    rateSlice seed M time lag=includeCLM (modes M) (modes_closed M)
      (NativeWindowHistoryDynamicKernel.kernel nu M (NativeWindowTraceAdjoint.value seed M (time-lag))
        (NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
          (restrictCLM (modes M) (modes_zero M) (modes_closed M) (velocityRate seed M (time-lag)))
          (NativeWindowHistoryDynamicKernel.kernel nu M (NativeWindowTraceAdjoint.value seed M (time-lag))
            (NativeWindowHistoryCommonForceTime.value seed M time))+
          NativeWindowHistoryCommonForceTime.jet seed M 1 time)) := by
  rw [rateSlice,NativeWindowHistorySchurAdvectorFiber.family_original,slice_physical,restrict_include]
  change kernel seed M (time-lag) (includeCLM (modes M) (modes_closed M) _+
    includeCLM (modes M) (modes_closed M) (NativeWindowHistoryCommonForceTime.jet seed M 1 time))=_
  rw [← map_add,NativeWindowHistoryHeatWindow.included,NativeWindowHistoryDynamicKernel.kernel_source]
  rfl

private theorem value_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (actual : HasDerivAt (velocityPath seed M) (velocityRate seed M time) time) :
    HasDerivAt (NativeWindowTraceAdjoint.value seed M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (velocityRate seed M time)) time := by
  have source := (restrictCLM (modes M) (modes_zero M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time actual
  simpa only [Function.comp_def,NativeWindowHistoryOseen.velocityPath,restrict_include] using! source

theorem slice_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,HasDerivAt (fun t => slice seed M t lag) (rateSlice seed M time lag) time := by
  filter_upwards [NativeWindowHistoryOseen.shifted_derivative seed M time] with lag actual
  have shifted : HasDerivAt (fun t => NativeWindowTraceAdjoint.value seed M (t-lag))
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (velocityRate seed M (time-lag))) time := by
    simpa only [Function.comp_def,one_smul] using!
      (value_derivative seed M (time-lag) actual).scomp time ((hasDerivAt_id time).sub_const lag)
  have forcing : HasDerivAt (NativeWindowHistoryCommonForceTime.value seed M)
      (NativeWindowHistoryCommonForceTime.jet seed M 1 time) time := by
    simpa only [NativeWindowHistoryCommonForceTime.jet_zero] using!
      NativeWindowHistoryCommonForceTime.jet_hasDerivAt seed M 0 time
  have finite := NativeWindowHistoryDynamicDerivative.solution_hasDerivAt nu M
    (fun t => NativeWindowTraceAdjoint.value seed M (t-lag)) (NativeWindowHistoryCommonForceTime.value seed M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) (velocityRate seed M (time-lag)))
    (NativeWindowHistoryCommonForceTime.jet seed M 1 time) time shifted forcing
  have source := (includeCLM (modes M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time finite
  rw [rateSlice_physical]
  exact source.congr_of_eventuallyEq (Eventually.of_forall fun t => slice_physical seed M t lag)

theorem completion_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (completion seed M) (rate seed M time) time := by
  obtain ⟨B,dominated⟩ := slice_domination seed M time
  exact curve_derivative (completion seed M) (slice seed M) (rate seed M time) (rateSlice seed M time) time B
    (slice_original seed M) (rate_original seed M time) (slice_hasDerivAt_ae seed M time)
    (dominated.mono fun _ bound => Eventually.of_forall bound)

theorem rate_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rate seed M time=kernelAction seed M time
      (NativeWindowHistorySchurTranspose.transposeAction seed M time
        (NativeWindowHistoryOseen.action seed M time (NativeWindowTraceWholeHistory.finiteHistory seed time M)+
          NativeWindowHistoryOseen.forcingHistory seed M time)+NativeWindowHistoryMeanProjection.embed (commonRate seed M time)) := by
  exact congrArg (fun v : H => kernelAction seed M time
    (NativeWindowHistorySchurTranspose.transposeAction seed M time v+
      NativeWindowHistoryMeanProjection.embed (commonRate seed M time)))
    (NativeWindowHistoryOseen.source_equation seed M time)

def residualRate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  NativeWindowHistoryOseen.rateHistory seed M time-rate seed M time

theorem residualRate_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    residualRate seed M time=NativeWindowHistoryOseen.action seed M time
      (NativeWindowTraceWholeHistory.finiteHistory seed time M)+NativeWindowHistoryOseen.forcingHistory seed M time-rate seed M time := by
  rw [residualRate,NativeWindowHistoryOseen.source_equation]

theorem residual_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (NativeWindowHistorySchurTemporalControl.temporalResponse seed M) (residualRate seed M time) time := by
  have source := HasDerivAt.sub (𝕜 := ℝ) (F := H)
    (NativeWindowHistoryOseen.history_hasDerivAt seed M time) (completion_hasDerivAt seed M time)
  apply source.congr_of_eventuallyEq
  filter_upwards with t
  simp only [Pi.sub_apply,NativeWindowHistorySchurCompletion.source_split]
  abel

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem kernelAction_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    kernelAction seed M (step.2.clockAdvance+time)=kernelAction step.1 M time := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [kernelAction_ae seed M (step.2.clockAdvance+time) v,kernelAction_ae step.1 M time v,
    NativeWindowTraceEndpointWindow.average_interval] with lag first last support
  rw [first,last,add_sub_assoc,NativeWindowHistoryFrozenInverse.kernel_next seed M step generated
    (time-lag) (by linarith [support.2])]

theorem commonRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    commonRate seed M (step.2.clockAdvance+time)=commonRate step.1 M time :=
  congrArg (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistoryCommonForceTime.jet_next seed M 1 step generated time time0)

theorem rate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    rate seed M (step.2.clockAdvance+time)=rate step.1 M time := by
  have transported := congrArg₂ (fun (A : H →L[ℝ] H) (v : H) => A v)
    (NativeWindowHistorySchurTranspose.transpose_next seed M step generated time time0)
    (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0)
  have input := congrArg₂ (fun (v : H) (d : wholePhysical) => v+NativeWindowHistoryMeanProjection.embed d)
    transported (commonRate_next seed M step generated time time0)
  exact congrArg₂ (fun (A : H →L[ℝ] H) (v : H) => A v)
    (kernelAction_next seed M step generated time time0) input

theorem residualRate_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    residualRate seed M (step.2.clockAdvance+time)=residualRate step.1 M time := by
  exact congrArg₂ (fun x y : H => x-y)
    (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0) (rate_next seed M step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryDynamicHistory

import H0mework.Versions.X.NavierStokes.WindowHistoryOseen.Rate
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Joint
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowTraceWholeHistory (history finiteHistory original projection)
open NativeForwardWindowPairingReadout (averageMeasure density)
noncomputable section
variable {nu : Viscosity}

theorem restrict_original_total (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M : ℕ) :
    restrictCLM (modes M) (modes_zero M) (modes_closed M) (original seed time)=NativeWindowTraceAdjoint.value seed M time := by
  by_cases positive : 0 ≤ time
  · exact NativeWindowTraceWholeHistory.restrict_original seed time positive M
  · rw [NativeWindowTraceWholeHistory.original_nonpositive seed time (le_of_not_ge positive),
      NativeWindowTraceWholeHistory.restrict_original seed 0 le_rfl M]
    simp only [NativeWindowTraceAdjoint.value,NativeWindowHierarchyPairWindow.state_before seed time (le_of_not_ge positive)]

theorem history_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    finiteHistory seed time M =ᵐ[averageMeasure] fun shift => velocityPath seed M (time-shift) := by
  filter_upwards [NativeWindowTraceWholeHistory.finiteHistory_ae seed time M] with shift actual
  rw [actual,projection,ContinuousLinearMap.comp_apply,restrict_original_total]
  rfl

theorem shiftedRate_measurable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    AEStronglyMeasurable (fun shift => velocityRate seed M (time-shift)) averageMeasure :=
  ((velocityRate_measurable seed M).comp_measurePreserving
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) time)).mono_ac
      (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞)))

theorem shiftedRate_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    MemLp (fun shift => velocityRate seed M (time-shift)) 2 averageMeasure :=
  MemLp.of_bound (shiftedRate_measurable seed M time) (rateBudget seed M)
    (Eventually.of_forall fun shift => velocityRate_bound seed M (time-shift))

def rateHistory (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  (shiftedRate_memLp seed M time).toLp (fun shift => velocityRate seed M (time-shift))

theorem rateHistory_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rateHistory seed M time =ᵐ[averageMeasure] fun shift => velocityRate seed M (time-shift) :=
  (shiftedRate_memLp seed M time).coeFn_toLp

theorem rateHistory_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖rateHistory seed M time‖ ≤ rateBudget seed M := by
  have paid := Lp.norm_le_of_ae_bound (rateBudget_nonnegative seed M) (by
    filter_upwards [rateHistory_ae seed M time] with shift actual
    rw [actual]
    exact velocityRate_bound seed M (time-shift))
  simpa [measureUnivNNReal] using paid

theorem shifted_derivative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ shift ∂averageMeasure,HasDerivAt (velocityPath seed M) (velocityRate seed M (time-shift)) (time-shift) :=
  (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le
    ((Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
      (velocityPath_derivative seed M))

theorem history_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (fun t => finiteHistory seed t M) (rateHistory seed M time) time := by
  let error (displacement shift : ℝ) := displacement⁻¹ •
    (velocityPath seed M (time+displacement-shift)-velocityPath seed M (time-shift))-velocityRate seed M (time-shift)
  have measured (displacement : ℝ) : AEStronglyMeasurable (fun shift => ‖error displacement shift‖^2) averageMeasure :=
    ((((velocityPath_continuous seed M).comp
        (continuous_const.sub continuous_id : Continuous (fun shift : ℝ => time+displacement-shift))).aestronglyMeasurable.sub
      ((velocityPath_continuous seed M).comp
        (continuous_const.sub continuous_id : Continuous (fun shift : ℝ => time-shift))).aestronglyMeasurable).const_smul displacement⁻¹
      |>.sub (shiftedRate_measurable seed M time)).norm.pow 2
  have dominated (displacement : ℝ) : ∀ᵐ shift ∂averageMeasure,
      ‖‖error displacement shift‖^2‖ ≤ 4*(rateBudget seed M)^2 := by
    filter_upwards with shift
    have quotient := velocityPath_quotient seed M (time-shift) displacement
    rw [sub_add_eq_add_sub] at quotient
    have bound : ‖error displacement shift‖ ≤ 2*rateBudget seed M :=
      (norm_sub_le _ _).trans (by linarith [velocityRate_bound seed M (time-shift)])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (error displacement shift),rateBudget_nonnegative seed M]
  have convergence := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => 4*(rateBudget seed M)^2) (Eventually.of_forall measured) (Eventually.of_forall dominated)
    (integrable_const _) (by
      filter_upwards [shifted_derivative seed M time] with shift actual
      have point := (tendsto_iff_norm_sub_tendsto_zero.mp actual.tendsto_slope_zero).pow 2
      simpa only [error,sub_add_eq_add_sub,zero_pow (by decide : (2 : ℕ) ≠ 0)] using! point)
  have identity (displacement : ℝ) :
      ‖displacement⁻¹ • (finiteHistory seed (time+displacement) M-finiteHistory seed time M)-rateHistory seed M time‖^2=
        ∫ shift,‖error displacement shift‖^2 ∂averageMeasure := by
    rw [NativeWindowTraceWholeHistory.norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (displacement⁻¹ • (finiteHistory seed (time+displacement) M-finiteHistory seed time M)) (rateHistory seed M time),
      Lp.coeFn_smul displacement⁻¹ (finiteHistory seed (time+displacement) M-finiteHistory seed time M),
      Lp.coeFn_sub (finiteHistory seed (time+displacement) M) (finiteHistory seed time M),
      history_original seed M (time+displacement),history_original seed M time,rateHistory_ae seed M time]
      with shift subtract scale difference first second derivative
    rw [subtract,Pi.sub_apply,scale,Pi.smul_apply,difference,Pi.sub_apply,first,second,derivative]
  have squares : Tendsto
      (fun displacement => ‖displacement⁻¹ • (finiteHistory seed (time+displacement) M-finiteHistory seed time M)-rateHistory seed M time‖^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp only [identity]
    simpa only [integral_zero] using! convergence
  have normLimit := Real.continuous_sqrt.continuousAt.tendsto.comp squares
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,@abs_norm H _,Real.sqrt_zero] at normLimit
  apply (hasDerivAt_iff_tendsto_slope_zero (F := H) (f := fun t => finiteHistory seed t M)
    (f' := rateHistory seed M time) (x := time)).mpr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr normLimit

theorem rateHistory_measurable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    AEStronglyMeasurable (rateHistory seed M) (volume : Measure ℝ) := by
  have same : rateHistory seed M=deriv (fun t => finiteHistory seed t M) := by
    funext time
    exact (HasDerivAt.deriv (𝕜 := ℝ) (F := H) (f := fun t => finiteHistory seed t M)
      (f' := rateHistory seed M time) (x := time) (by exact history_hasDerivAt seed M time)).symm
  rw [same]
  have : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩
  simpa only using! (aestronglyMeasurable_deriv (𝕜 := ℝ) (F := H) (fun t => finiteHistory seed t M) (volume : Measure ℝ))

theorem rateHistory_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (rateHistory seed M) volume a b := by
  apply (intervalIntegrable_iff (ε := H) (f := rateHistory seed M)).mpr
  have constants : IntervalIntegrable (fun _ : ℝ => rateBudget seed M) volume a b := intervalIntegrable_const
  exact constants.def'.mono' (rateHistory_measurable seed M).restrict (Eventually.of_forall (rateHistory_bound seed M))

theorem history_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (a b : ℝ) :
    finiteHistory seed b M-finiteHistory seed a M=∫ time in a..b,rateHistory seed M time :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => history_hasDerivAt seed M time)
    (rateHistory_integrable seed M a b)).symm

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseen

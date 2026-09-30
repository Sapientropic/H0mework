import H0mework.Versions.X.NavierStokes.WindowSchurMean.Recovery

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryWholeRecovery
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open NativeWholeResolvent (wholePhysical)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (finiteHistory history projection projected)
open NativeWindowHistoryMeanForceResolution (error resolved)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

theorem projection_norm (M : ℕ) (v : wholePhysical) : ‖projection M v‖≤‖v‖ := by
  change ‖(projection M v).1‖≤‖v.1‖
  rw [NativeWindowHistoryMeanTime.projection_read]
  exact NativeWindowHistoryMeanTime.read_bound M v.1

theorem projection_error_tendsto (v : wholePhysical) :
    Tendsto (fun M => ‖projection M v-v‖^2) atTop (𝓝 (0 : ℝ)) := by
  have source:=((wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto v.1).sub_const v.1).norm.pow 2
  change Tendsto (fun M => ‖(projection M v).1-v.1‖^2) atTop (𝓝 (0 : ℝ))
  simpa only [NativeWindowHistoryMeanTime.projection_read,NativeWindowHistoryMeanTime.read_original,
    sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)] using source

private theorem square_sub_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (bound : ∀ x,‖P x‖≤‖x‖) (v : E) : ‖P v-v‖^2≤4*‖v‖^2 := by
  have actual:‖P v-v‖≤2*‖v‖ := calc
    _ ≤ ‖P v‖+‖v‖ := norm_sub_le (P v) v
    _ ≤ ‖v‖+‖v‖ := add_le_add (bound v) le_rfl
    _ = _ := by ring
  exact (pow_le_pow_left₀ (norm_nonneg (P v-v)) actual 2).trans_eq (by ring)

theorem projected_tendsto (v : H) : Tendsto (fun M => projected M v) atTop (𝓝 v) := by
  let F:=fun M lag => ‖projection M (v lag)-v lag‖^2
  have measured (M : ℕ) : AEStronglyMeasurable (F M) averageMeasure :=
    (((projection M).continuous.comp_aestronglyMeasurable (Lp.memLp v).1).sub (Lp.memLp v).1).norm.pow 2
  have dominated (M : ℕ) : ∀ᵐ lag ∂averageMeasure,‖F M lag‖≤4*‖v lag‖^2 := by
    filter_upwards with lag
    simpa only [F,Real.norm_eq_abs,abs_sq] using
      square_sub_bound (E := wholePhysical) (projection M) (projection_norm M) (v lag)
  have paid:Integrable (fun lag => 4*‖v lag‖^2) averageMeasure :=
    ((Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ)≠0)).const_mul 4
  have limit:=tendsto_integral_of_dominated_convergence (μ := averageMeasure) (f := fun _ => (0 : ℝ))
    (fun lag => 4*‖v lag‖^2) measured paid dominated (Eventually.of_forall fun lag => projection_error_tendsto (v lag))
  have read (M : ℕ) : ‖projected M v-v‖^2=∫ lag,F M lag ∂averageMeasure := by
    rw [NativeWindowTraceWholeHistory.norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (projected M v) v,(projection M).coeFn_compLpL v] with lag difference project
    rw [difference,Pi.sub_apply,show projected M v lag=projection M (v lag) from project]
  have squared:Tendsto (fun M => ‖projected M v-v‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [read,integral_zero] using limit
  have normed:=Real.continuous_sqrt.continuousAt.tendsto.comp squared
  have root (M : ℕ) : Real.sqrt (‖projected M v-v‖^2)=‖projected M v-v‖ :=
    Real.sqrt_sq (norm_nonneg (projected M v-v))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,root,Real.sqrt_zero] using normed

def retained (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  resolved seed M time+temporalResponse seed M time

theorem retained_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    retained seed M time=finiteHistory seed time M-error seed M time := by
  unfold retained resolved
  have source:=NativeWindowHistorySchurCompletion.source_split seed M time
  calc
    _ = (NativeWindowHistorySchurCompletion.completion seed M time+temporalResponse seed M time)-error seed M time := by abel
    _ = _ := congrArg (fun v : H => v-error seed M time) source.symm

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    Tendsto (fun M => retained seed M time) atTop (𝓝 (history seed time)) := by
  have source:=(projected_tendsto (history seed time)).sub
    (NativeWindowHistoryMeanRecovery.source_error_tendsto seed time nonnegative)
  simpa only [retained_original,finiteHistory,projected,sub_zero] using source

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem retained_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    retained seed M (step.2.clockAdvance+time)=retained step.1 M time :=
  congrArg₂ (fun y w : H => y+w)
    (NativeWindowHistoryMeanForceResolution.resolved_next seed M step generated time nonnegative)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryWholeRecovery

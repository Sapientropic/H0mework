import H0mework.NavierStokes.WindowSchurMean.Projection
import H0mework.NavierStokes.WindowHistory.ForcingWork

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (H gradient finiteHistory)
open NativeWindowHistoryMeanProjection (embed mean projection residual)
noncomputable section
variable {nu : Viscosity}

private theorem fixed_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    inner ℝ v ((NativeWindowHistoryOseen.forwardFiber seed M 0).compLpL 2 averageMeasure v)=
      -nu.coeff*gradient M v := by
  rw [L2.inner_def,NativeWindowTraceWholeHistory.gradient,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(NativeWindowHistoryOseen.forwardFiber seed M 0).coeFn_compLpL v] with lag actual
  rw [actual,NativeWindowHistoryOseenGap.fiber_energy]

theorem gradient_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    gradient M v=gradient M (NativeWindowHistoryMeanProjection.projection v)+gradient M (NativeWindowHistoryMeanProjection.residual v) := by
  have same:=NativeWindowHistoryMeanProjection.comp_energy_split (NativeWindowHistoryOseen.forwardFiber seed M 0) v
  have first:=fixed_energy seed M v
  have meanEnergy:=fixed_energy seed M (NativeWindowHistoryMeanProjection.projection v)
  have residualEnergy:=fixed_energy seed M (NativeWindowHistoryMeanProjection.residual v)
  have paid:=first.symm.trans (same.trans (congrArg₂ (fun x y : ℝ => x+y) meanEnergy residualEnergy))
  nlinarith only [paid,nu.coeff_pos]

theorem gradient_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) : 0≤gradient M v := by
  have paid:=NativeWindowHistoryOseen.action_dissipative seed M 0 v
  rw [NativeWindowHistoryOseenGap.action_energy] at paid
  nlinarith only [paid,nu.coeff_pos]

theorem gradient_projection_le (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    gradient M (NativeWindowHistoryMeanProjection.projection v)≤gradient M v := by
  rw [gradient_split seed M v]
  exact le_add_of_nonneg_right (gradient_nonnegative seed M (NativeWindowHistoryMeanProjection.residual v))

theorem gradient_residual_le (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v : H) :
    gradient M (NativeWindowHistoryMeanProjection.residual v)≤gradient M v := by
  rw [gradient_split seed M v]
  exact le_add_of_nonneg_left (gradient_nonnegative seed M (NativeWindowHistoryMeanProjection.projection v))

theorem gradient_embed (M : ℕ) (v : physicalSpace (modes M)) :
    gradient M (embed (includeCLM (modes M) (modes_closed M) v))=curlPair (modes M) v.1 v.1 := by
  rw [NativeWindowTraceWholeHistory.gradient]
  have same : (fun lag => curlPair (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (embed (includeCLM (modes M) (modes_closed M) v) lag)).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) (embed (includeCLM (modes M) (modes_closed M) v) lag)).1)
      =ᵐ[averageMeasure] fun _ => curlPair (modes M) v.1 v.1 := by
    filter_upwards [NativeWindowTraceWholeHistory.constant_ae (includeCLM (modes M) (modes_closed M) v)] with lag actual
    rw [show embed (includeCLM (modes M) (modes_closed M) v) lag=includeCLM (modes M) (modes_closed M) v from actual,restrict_include]
  rw [integral_congr_ae same]
  simp

def meanValue (M : ℕ) (v : H) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean v)

theorem source_projection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    projection (finiteHistory seed time M)=embed (includeCLM (modes M) (modes_closed M)
      (meanValue M (finiteHistory seed time M))) := by
  have same:=NativeWindowHistoryMeanProjection.mean_comp (NativeWindowTraceWholeHistory.projection M) (finiteHistory seed time M)
  rw [show (NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure (finiteHistory seed time M)=finiteHistory seed time M from
    NativeWindowHistoryOseenGap.projected_finiteHistory seed time M] at same
  exact congrArg (fun v : wholePhysical => embed v) same

theorem source_mean_gradient (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    curlPair (modes M) (meanValue M (finiteHistory seed time M)).1 (meanValue M (finiteHistory seed time M)).1≤
      gradient M (finiteHistory seed time M) := by
  have paid:=gradient_projection_le seed M (finiteHistory seed time M)
  rw [source_projection,gradient_embed] at paid
  exact paid

theorem source_mean_budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    curlPair (modes M) (meanValue M (finiteHistory seed time M)).1 (meanValue M (finiteHistory seed time M)).1≤
      NativeWindowAugmentedPayment.graphBudget seed 0 horizon := by
  have source:=source_mean_gradient seed M time
  rw [NativeWindowHistoryForcingWork.gradient_original seed M time inside.1] at source
  exact source.trans ((le_abs_self _).trans
    (by simpa only [← Real.norm_eq_abs] using NativeWindowAugmentedPayment.graphJet_bound seed (modes M) 0 time horizon inside))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGradient

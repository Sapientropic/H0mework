import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Read
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Current

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceBudget
open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier (Torus)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def numerator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) : ℝ :=
  ∑i : Coordinate,(NativeWindowHistoryCovarianceMetric.momentum seed M time i x)^2

theorem numerator_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    0≤numerator seed M time x := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem numerator_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Continuous (numerator seed M time) :=
  continuous_finsetSum _ (fun i _ => (NativeWindowHistoryCovarianceMetric.momentum seed M time i).continuous.pow 2)

private theorem current_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Continuous (NativeWindowHistoryCovarianceCurrent.value seed M time) := by
  have same : NativeWindowHistoryCovarianceCurrent.value seed M time =
      fun x => NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0 x := by
    funext x
    change (NativeWindowAbsoluteTimePhysicalCurrent.current seed M time 0 x).re=_
    rw [NativeWindowAbsoluteTimePhysicalCurrent.current_read]
    rfl
  rw [same]
  exact (NativeWindowAbsoluteTimePhysicalCurrent.currentRead seed M time 0).continuous

set_option backward.isDefEq.respectTransparency false in
theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    (∫x : Torus,numerator seed M time x/NativeWindowHistoryCovarianceCurrent.value seed M time x)≤
      8*NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon := by
  have currentPositive (x : Torus) : 0<NativeWindowHistoryCovarianceCurrent.value seed M time x := by
    linarith [(NativeWindowHistoryCovarianceCurrent.lower seed M time inside.1 x).1]
  have tracePositive (x : Torus) : 0<1+NativeWindowHistoryCreationCovariance.trace seed M time x := by
    linarith [NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time x]
  have first : Integrable (fun x : Torus => numerator seed M time x /
      NativeWindowHistoryCovarianceCurrent.value seed M time x) :=
    ((numerator_continuous seed M time).div (current_continuous seed M time)
      (fun x => (currentPositive x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have last : Integrable (fun x : Torus => 8*(numerator seed M time x /
      (1+NativeWindowHistoryCreationCovariance.trace seed M time x))) :=
    (((numerator_continuous seed M time).div
      (continuous_const.add (NativeWindowHistoryCreationCovariance.trace seed M time).continuous)
      (fun x => (tracePositive x).ne')).const_mul 8).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have point (x : Torus) : numerator seed M time x/NativeWindowHistoryCovarianceCurrent.value seed M time x≤
      8*(numerator seed M time x/(1+NativeWindowHistoryCreationCovariance.trace seed M time x)) :=
    NativeWindowHistoryCovarianceCurrent.inverse_cost seed M time inside.1 x
      (numerator seed M time x) (numerator_nonnegative seed M time x)
  have paid:=integral_mono first last point
  rw [integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left
    (NativeWindowHistoryCovarianceMetric.source seed horizon M time inside) (by norm_num))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceBudget

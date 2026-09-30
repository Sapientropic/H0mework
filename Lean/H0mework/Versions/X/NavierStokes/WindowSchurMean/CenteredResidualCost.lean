import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.Variational

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
local instance costPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance costPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def centeredWCost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  let l := NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
    (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  centeredActionCost seed time
    (fun i => NativeWindowHistoryMeanWeightedResidualTest.waveTest M l i)

theorem source_centered_stress_work (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time∈Icc 0 horizon) (M : ℕ) :
    NativeWindowHistoryMeanPhysicalResidualCost.stressWork seed M time≤
      Real.sqrt (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon)*
        Real.sqrt (centeredWCost seed M time) := by
  rw [NativeWindowHistoryMeanWeightedResidualTest.stressWork_action]
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,centeredWCost] using
    (source_centered_action_bound seed horizon time inside (fun i =>
      NativeWindowHistoryMeanWeightedResidualTest.waveTest M
        (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
          (NativeWindowHistoryMeanProjection.mean
            (NativeWindowTraceWholeHistory.finiteHistory seed time M))) i)))

theorem source_centered_spatial_cost (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,
      (nu.coeff/4)*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
        (NativeWindowHistoryMeanProjection.mean
          (NativeWindowTraceWholeHistory.finiteHistory seed t M))‖^2≤
          Real.sqrt (NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon)*
            Real.sqrt (centeredWCost seed M t)+C := by
  obtain ⟨low,C,C0,paid⟩:=
    NativeWindowHistoryMeanPhysicalResidualCost.source_stress_spatial_cost seed horizon
  refine ⟨low,C,C0,fun M above t inside => ?_⟩
  exact (paid M above t inside).trans
    (add_le_add_left (source_centered_stress_work seed horizon t inside M) C)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem centeredWCost_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    centeredWCost seed M (step.2.clockAdvance+time)=centeredWCost step.1 M time := by
  simp only [centeredWCost,centeredActionCost,
    fullTrace_next seed step generated time nonnegative,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M]

end
end SaturationMonoid.NavierStokes.NativeCenteredCovariance

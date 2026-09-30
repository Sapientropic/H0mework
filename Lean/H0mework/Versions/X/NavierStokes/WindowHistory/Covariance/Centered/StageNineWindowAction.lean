import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowJointGraph
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryWrite
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.HistoryControl

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section
variable {nu : Viscosity}

def meanQEnergy (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  (∑index : FixedMatterSpatialWordIndex order,
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.projection h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection h)))+
  (∑index : FixedMatterSpatialWordIndex order,
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.residual h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual h)))

theorem meanQEnergy_original (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    meanQEnergy seed M order F radius time=
      NativeWindowHierarchyHistory.history seed M order F radius 0 time :=
  (history_full_metric_mean_q seed M order time F radius).symm

theorem meanQEnergy_actual_rate (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    HasDerivAt (meanQEnergy seed M order F radius)
      (NativeWindowHierarchyWrite.spatialRate seed M order F radius 0 time+
        NativeWindowHierarchyHistory.coefficientRate seed M order F radius 0 time) time := by
  have original:=NativeWindowHierarchyWrite.whole_history_write
    seed M order F radius 0 time
  exact original.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    meanQEnergy_original seed M order F radius t)

theorem meanQEnergy_prepared :
    ∃low : ℕ,∀order : ℕ,0≤NativeWindowStageNineInitialEnergy.budget order ∧
      ∀radius≥low,∀outerRadius M,
        meanQEnergy stackedShortCurrent M order
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius (-2)≤
          NativeWindowStageNineInitialEnergy.budget order := by
  obtain ⟨low,paid⟩:=NativeWindowHierarchyControl.source_history_initial
  refine ⟨low,fun order => ⟨(paid order).1,fun radius above outerRadius M => ?_⟩⟩
  rw [meanQEnergy_original]
  exact (paid order).2 radius above outerRadius M

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem meanQEnergy_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M order : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (nonnegative : 0≤time) :
    meanQEnergy seed M order F radius (step.2.clockAdvance+time)=
      meanQEnergy step.1 M order F radius time := by
  rw [meanQEnergy_original,NativeWindowHierarchyHistory.history_next
    seed step generated M order F radius 0 time nonnegative,
    meanQEnergy_original]

end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

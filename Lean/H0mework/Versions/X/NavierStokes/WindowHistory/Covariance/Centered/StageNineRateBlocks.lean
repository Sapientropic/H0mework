import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineSpatialSplit
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Causal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
noncomputable section
variable {nu : Viscosity}

theorem centered_word_rate_original (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ) :
    NativeWindowHistoryMeanProjection.residual
      (NativeWindowHistorySpatialWords.rate seed M word time)=
      NativeWindowHistoryMeanBlocks.bath seed M time
        (NativeWindowHistoryMeanProjection.residual
          (NativeWindowHistorySpatialWords.history seed M word time))+
      NativeWindowHistoryMeanAction.creation seed M time
        (NativeWindowHistoryAllOrderWord.value seed M word time)+
      NativeWindowHistoryMeanProjection.residual
        (NativeWindowHistoryAllOrderCausal.load seed M word time) := by
  have source :=
    (NativeWindowHistoryMeanProjection.residual.hasFDerivAt.comp_hasDerivAt time
      (NativeWindowHistorySpatialWords.source_hasDerivAt seed M word time))
  have original := NativeWindowHistoryAllOrderCausal.residual_derivative seed M word time
  exact (original.unique source).symm

theorem mean_word_rate_original (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ) :
    NativeWindowHistoryMeanProjection.mean
      (NativeWindowHistorySpatialWords.rate seed M word time)=
      NativeWindowHistoryMeanAction.meanOperator seed M time
        (NativeWindowHistoryAllOrderWord.value seed M word time)+
      NativeWindowHistoryMeanBlocks.annihilation seed M time
        (NativeWindowHistorySpatialWords.history seed M word time)+
      NativeWindowHistoryMeanProjection.mean
        (NativeWindowHistoryAllOrderCausal.load seed M word time) := by
  have source :=
    (NativeWindowHistoryMeanProjection.mean.hasFDerivAt.comp_hasDerivAt time
      (NativeWindowHistorySpatialWords.source_hasDerivAt seed M word time))
  have source' : HasDerivAt (NativeWindowHistoryAllOrderWord.value seed M word)
      (NativeWindowHistoryMeanProjection.mean
        (NativeWindowHistorySpatialWords.rate seed M word time)) time :=
    source.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
      NativeWindowHistoryAllOrderWord.value_original seed M word t)
  have original := NativeWindowHistoryAllOrderCausal.mean_derivative seed M word time
  exact (original.unique source').symm
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineCoupling

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

def spatialWordDiagonal (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  let h:=NativeWindowHistorySpatialWords.history seed M word time
  let u:=NativeWindowHistoryAllOrderWord.value seed M word time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let B:=fullMetricAction seed time M F radius
  twoLeg B (NativeWindowHistoryMeanProjection.embed u)
    (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator seed M time u))+
  twoLeg B q (NativeWindowHistoryMeanBlocks.bath seed M time q)

def spatialWordLoad (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  let h:=NativeWindowHistorySpatialWords.history seed M word time
  let u:=NativeWindowHistoryAllOrderWord.value seed M word time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let load:=NativeWindowHistoryAllOrderCausal.load seed M word time
  let B:=fullMetricAction seed time M F radius
  twoLeg B (NativeWindowHistoryMeanProjection.embed u)
    (NativeWindowHistoryMeanProjection.embed (NativeWindowHistoryMeanProjection.mean load))+
  twoLeg B q (NativeWindowHistoryMeanProjection.residual load)

theorem spatialRate_action_blocks (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    NativeWindowHierarchyWrite.spatialRate seed M order F radius 0 time=
      ∑index : FixedMatterSpatialWordIndex order,
        (spatialWordDiagonal seed M index.toList time F radius+
          wordCoupling seed M index.toList time F radius+
          spatialWordLoad seed M index.toList time F radius) := by
  rw [spatialRate_mean_centered,meanSpatialRate,centeredSpatialRate]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  have mean:=mean_word_spatial_blocks seed M index.toList time F radius
  have centered:=centered_word_spatial_blocks seed M index.toList time F radius
  have coupling:=wordCoupling_twoLeg seed M index.toList time F radius
  dsimp only [spatialWordDiagonal,spatialWordLoad,twoLeg] at *
  linarith only [mean,centered,coupling]
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineSpatialSample

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM include_inner restrict_include)
open NativeFiniteActionResolvent (pairing physicalSpace)
open NativeForwardWindowPairingReadout (averageMeasure density)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

private theorem quadratic_split_two_leg {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A P Q : E →L[ℝ] E)
    (split : ∀v : E,inner ℝ v (A v)=
      inner ℝ (P v) (A (P v))+inner ℝ (Q v) (A (Q v)))
    (h r : E) :
    inner ℝ r (A h)+inner ℝ h (A r)=
      inner ℝ (P r) (A (P h))+inner ℝ (P h) (A (P r))+
        inner ℝ (Q r) (A (Q h))+inner ℝ (Q h) (A (Q r)) := by
  have total:=split (h+r)
  have first:=split h
  have last:=split r
  simp only [map_add,inner_add_left,inner_add_right] at total
  linarith only [total,first,last]

theorem full_metric_two_leg_split (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ)
    (h r : NativeWindowTraceWholeHistory.H) :
    inner ℝ r (fullMetricAction seed time M F radius h)+
      inner ℝ h (fullMetricAction seed time M F radius r)=
      inner ℝ (NativeWindowHistoryMeanProjection.projection r)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.projection h))+
      inner ℝ (NativeWindowHistoryMeanProjection.projection h)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.projection r))+
      inner ℝ (NativeWindowHistoryMeanProjection.residual r)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.residual h))+
      inner ℝ (NativeWindowHistoryMeanProjection.residual h)
        (fullMetricAction seed time M F radius
          (NativeWindowHistoryMeanProjection.residual r)) :=
  quadratic_split_two_leg (fullMetricAction seed time M F radius)
    NativeWindowHistoryMeanProjection.projection
    NativeWindowHistoryMeanProjection.residual
    (fun v => full_metric_split seed M time F radius v) h r

def meanSpatialRate (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.projection r)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection h))+
    inner ℝ (NativeWindowHistoryMeanProjection.projection h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection r))

def centeredSpatialRate (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.residual r)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual h))+
    inner ℝ (NativeWindowHistoryMeanProjection.residual h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual r))

theorem spatialRate_mean_centered (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowHierarchyWrite.spatialRate seed M order F radius 0 time=
      meanSpatialRate seed M order time F radius+
        centeredSpatialRate seed M order time F radius := by
  rw [spatialRate_full_metric]
  let left (index : FixedMatterSpatialWordIndex order) :=
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.projection r)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection h))+
    inner ℝ (NativeWindowHistoryMeanProjection.projection h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection r))
  let right (index : FixedMatterSpatialWordIndex order) :=
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.residual r)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual h))+
    inner ℝ (NativeWindowHistoryMeanProjection.residual h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual r))
  have row (index : FixedMatterSpatialWordIndex order) :
      (let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
       let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
       inner ℝ r (fullMetricAction seed time M F radius h)+
         inner ℝ h (fullMetricAction seed time M F radius r))=
        left index+right index := by
    have paid:=full_metric_two_leg_split seed M time F radius
      (NativeWindowHistorySpatialWords.history seed M index.toList time)
      (NativeWindowHistorySpatialWords.rate seed M index.toList time)
    dsimp only [left,right]
    linarith only [paid]
  have summed :
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        let r:=NativeWindowHistorySpatialWords.rate seed M index.toList time
        inner ℝ r (fullMetricAction seed time M F radius h)+
          inner ℝ h (fullMetricAction seed time M F radius r))=
      ∑index : FixedMatterSpatialWordIndex order,(left index+right index) :=
    Finset.sum_congr rfl (fun index _ => row index)
  change _=(∑index : FixedMatterSpatialWordIndex order,left index)+
    (∑index : FixedMatterSpatialWordIndex order,right index)
  rw [← Finset.sum_add_distrib]
  exact summed
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

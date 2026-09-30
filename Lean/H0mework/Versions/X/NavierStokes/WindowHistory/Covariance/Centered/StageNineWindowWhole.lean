import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowMetric

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter (IntegerWavevector)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (pairing)
open NativePhysicalPairing (restrict_include include_inner)
open NativeForwardWindowPairingReadout (averageMeasure)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

private theorem sample_word_full_metric_integrable (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (directions : List Coordinate) (time : ℝ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    Integrable (fun shift => pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M directions (time-shift))
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
        (NativeWindowStageNineSource.coefficient seed M directions (time-shift))))
      averageMeasure := by
  let h:=NativeWindowHistorySpatialWords.history seed M directions time
  let A:=fullMetricAction seed time M F radius
  have original : Integrable (fun shift => inner ℝ (h shift) (A h shift)) averageMeasure :=
    L2.integrable_inner h (A h)
  apply original.congr
  filter_upwards [(fullMetricFiber seed time M F radius).coeFn_compLpL h,
    NativeWindowHistorySpatialWords.history_original seed M directions time]
      with shift applied source
  change inner ℝ (h shift)
    (((fullMetricFiber seed time M F radius).compLpL 2 averageMeasure h) shift)=_
  rw [applied,source]
  dsimp only [fullMetricFiber]
  rw [NativeWindowHistoryOseen.lift_included]
  rw [include_inner (modes M) (modes_zero M) (modes_closed M),restrict_include]
  rfl

theorem history_full_metric_total (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowHierarchyHistory.history seed M order F radius 0 time=
      ∑index : FixedMatterSpatialWordIndex order,
        inner ℝ (NativeWindowHistorySpatialWords.history seed M index.toList time)
          (fullMetricAction seed time M F radius
            (NativeWindowHistorySpatialWords.history seed M index.toList time)) := by
  let f (index : FixedMatterSpatialWordIndex order) (shift : ℝ) :=
    pairing (modes M)
      (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift))
      (NativeWindowAugmentedFixedOperator.test seed time (modes M) (modes M) F radius
        (NativeWindowStageNineSource.coefficient seed M index.toList (time-shift)))
  have integrated : (∫shift,∑index : FixedMatterSpatialWordIndex order,
      f index shift ∂averageMeasure)=
      ∑index : FixedMatterSpatialWordIndex order,
        ∫shift,f index shift ∂averageMeasure :=
    integral_finsetSum Finset.univ (fun index _ =>
      sample_word_full_metric_integrable seed M index.toList time F radius)
  calc
    _=∫shift,NativeWindowHierarchyHistory.sampleEnergy seed time M order F radius (time-shift)
        ∂averageMeasure := hierarchy_history_lag seed M order F radius time
    _=∫shift,∑index : FixedMatterSpatialWordIndex order,f index shift ∂averageMeasure := rfl
    _=∑index : FixedMatterSpatialWordIndex order,
      ∫shift,f index shift ∂averageMeasure := integrated
    _=_ := Finset.sum_congr rfl (fun index _ =>
      (history_word_full_metric seed M index.toList time F radius).symm)

theorem history_full_metric_mean_q (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    NativeWindowHierarchyHistory.history seed M order F radius 0 time=
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        inner ℝ (NativeWindowHistoryMeanProjection.projection h)
          (fullMetricAction seed time M F radius
            (NativeWindowHistoryMeanProjection.projection h)))+
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        inner ℝ (NativeWindowHistoryMeanProjection.residual h)
          (fullMetricAction seed time M F radius
            (NativeWindowHistoryMeanProjection.residual h))) := by
  rw [history_full_metric_total]
  let left (index : FixedMatterSpatialWordIndex order) :=
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.projection h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.projection h))
  let right (index : FixedMatterSpatialWordIndex order) :=
    let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
    inner ℝ (NativeWindowHistoryMeanProjection.residual h)
      (fullMetricAction seed time M F radius
        (NativeWindowHistoryMeanProjection.residual h))
  have row (index : FixedMatterSpatialWordIndex order) :
      inner ℝ (NativeWindowHistorySpatialWords.history seed M index.toList time)
        (fullMetricAction seed time M F radius
          (NativeWindowHistorySpatialWords.history seed M index.toList time))=
        left index+right index :=
    full_metric_split seed M time F radius _
  have summed :
      (∑index : FixedMatterSpatialWordIndex order,
        inner ℝ (NativeWindowHistorySpatialWords.history seed M index.toList time)
          (fullMetricAction seed time M F radius
            (NativeWindowHistorySpatialWords.history seed M index.toList time)))=
        ∑index : FixedMatterSpatialWordIndex order,(left index+right index) :=
    Finset.sum_congr rfl (fun index _ => row index)
  simpa only [Finset.sum_add_distrib] using summed
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

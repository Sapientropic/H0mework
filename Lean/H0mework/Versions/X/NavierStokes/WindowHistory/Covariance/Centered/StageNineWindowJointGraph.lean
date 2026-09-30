import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowWhole

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

theorem source_full_metric_mean_q_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∀radius≥low,∀outerRadius M order : ℕ,
      ∀time∈Icc 0 horizon,
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        ‖NativeWindowHistoryMeanProjection.projection h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.projection h)+
          ‖NativeWindowHistoryMeanProjection.residual h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.residual h))≤
        NativeWindowHierarchyHistory.history seed M order
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius 0 time := by
  obtain ⟨low,paid⟩:=source_full_metric_coercive seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M order time inside => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
    outerRadius
  let A:=fullMetricAction seed time M F radius
  let h (index : FixedMatterSpatialWordIndex order) :=
    NativeWindowHistorySpatialWords.history seed M index.toList time
  let p (index : FixedMatterSpatialWordIndex order) :=
    NativeWindowHistoryMeanProjection.projection (h index)
  let q (index : FixedMatterSpatialWordIndex order) :=
    NativeWindowHistoryMeanProjection.residual (h index)
  have row (index : FixedMatterSpatialWordIndex order) :
      ‖p index‖^2+(nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M (p index)+
        ‖q index‖^2+(nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M (q index)≤
      inner ℝ (p index) (A (p index))+inner ℝ (q index) (A (q index)) := by
    have first:=paid radius above outerRadius M time inside (p index)
    have second:=paid radius above outerRadius M time inside (q index)
    rw [history_word_mean_projected seed M index.toList time] at first
    rw [history_word_residual_projected seed M index.toList time] at second
    dsimp only [p,q,h,A,F] at first second ⊢
    linarith only [first,second]
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset
      (FixedMatterSpatialWordIndex order))) (fun index _ => row index)
  have split:=history_full_metric_mean_q seed M order time F radius
  dsimp only [p,q,h,A,F] at summed split ⊢
  simp only [Finset.sum_add_distrib] at summed
  simp only [Finset.sum_add_distrib]
  linarith only [summed,split]

theorem source_stage_nine_window_mean_q_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∀radius≥low,∀outerRadius M order : ℕ,
      ∀time∈Icc 0 horizon,
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        let w:=NativeWindowHistoryAllOrderWord.value seed M index.toList time
        ‖w‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.embed w)+
          ‖NativeWindowHistoryMeanProjection.residual h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.residual h))≤
        NativeWindowHierarchyHistory.history seed M order
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius 0 time := by
  obtain ⟨low,paid⟩:=source_full_metric_mean_q_graph seed horizon nonnegative
  refine ⟨low,fun radius above outerRadius M order time inside => ?_⟩
  have row (index : FixedMatterSpatialWordIndex order) :
      NativeWindowHistoryMeanProjection.projection
        (NativeWindowHistorySpatialWords.history seed M index.toList time)=
      NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryAllOrderWord.value seed M index.toList time) := by
    change NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanProjection.mean
        (NativeWindowHistorySpatialWords.history seed M index.toList time))=_
    rw [NativeWindowHistoryAllOrderWord.value_original]
  have identity :
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        let w:=NativeWindowHistoryAllOrderWord.value seed M index.toList time
        ‖w‖^2+(nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
          (NativeWindowHistoryMeanProjection.embed w)+
          ‖NativeWindowHistoryMeanProjection.residual h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.residual h))=
      (∑index : FixedMatterSpatialWordIndex order,
        let h:=NativeWindowHistorySpatialWords.history seed M index.toList time
        ‖NativeWindowHistoryMeanProjection.projection h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.projection h)+
          ‖NativeWindowHistoryMeanProjection.residual h‖^2+
          (nu.coeff/2)*NativeWindowTraceWholeHistory.gradient M
            (NativeWindowHistoryMeanProjection.residual h)) := by
    apply Finset.sum_congr rfl
    intro index _
    dsimp only
    rw [row index,NativeWindowHistoryMeanProjection.embed_norm]
  rw [identity]
  exact paid radius above outerRadius M order time inside
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

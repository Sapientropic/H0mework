import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeRateWord
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWindowJointGraph

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section

def wholeGraphCost (M order : ℕ) (time : ℝ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    wholeWordGraph M index.toList time

def wholeMass (M order : ℕ) (time : ℝ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    wholeWordMass M index.toList time

def wholeTemporal (M order : ℕ) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    wholeWordTemporal M index.toList time F radius

def wholeLoad (M order : ℕ) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  ∑index : FixedMatterSpatialWordIndex order,
    spatialWordLoad stackedShortCurrent M index.toList time F radius

theorem source_whole_mass_le_history (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∀radius≥low,∀outerRadius M order : ℕ,
      ∀time∈Icc 0 horizon,
        wholeMass M order time≤
          NativeWindowHierarchyHistory.history stackedShortCurrent M order
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius 0 time := by
  obtain ⟨low,paid⟩:=source_stage_nine_window_mean_q_graph
    stackedShortCurrent horizon nonnegative
  refine ⟨low,fun radius above outerRadius M order time inside => ?_⟩
  have row (index : FixedMatterSpatialWordIndex order) :
      wholeWordMass M index.toList time≤
        let h:=NativeWindowHistorySpatialWords.history stackedShortCurrent M index.toList time
        let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M index.toList time
        ‖u‖^2+(butterflyGainViscosity.coeff/2)*
          NativeWindowTraceWholeHistory.gradient M (NativeWindowHistoryMeanProjection.embed u)+
          ‖NativeWindowHistoryMeanProjection.residual h‖^2+
          (butterflyGainViscosity.coeff/2)*
            NativeWindowTraceWholeHistory.gradient M (NativeWindowHistoryMeanProjection.residual h) := by
    let h:=NativeWindowHistorySpatialWords.history stackedShortCurrent M index.toList time
    let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M index.toList time
    have first:=NativeWindowHistoryMeanGradient.gradient_nonnegative stackedShortCurrent M
      (NativeWindowHistoryMeanProjection.embed u)
    have last:=NativeWindowHistoryMeanGradient.gradient_nonnegative stackedShortCurrent M
      (NativeWindowHistoryMeanProjection.residual h)
    have scalar : 0≤butterflyGainViscosity.coeff/2:=by positivity [butterflyGainViscosity.coeff_pos]
    have s1:=mul_nonneg scalar first
    have s2:=mul_nonneg scalar last
    dsimp only [wholeWordMass,h,u]
    linarith only [s1,s2]
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex order)))
    (fun index _ => row index)
  change wholeMass M order time≤_
  exact summed.trans (paid radius above outerRadius M order time inside)

theorem source_whole_spatial_rate_gate (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius,∀M≥low,∀order : ℕ,
        ∀time∈Icc 0 horizon,
          let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius
          NativeWindowHierarchyWrite.spatialRate stackedShortCurrent M order F radius 0 time≤
            -(butterflyGainViscosity.coeff^2/4)*wholeGraphCost M order time+
              wholeTemporal M order time F radius+
              wholeLoad M order time F radius+
              C*NativeWindowHierarchyHistory.history stackedShortCurrent M order F radius 0 time := by
  obtain ⟨first,C,C0,wordPaid⟩:=whole_word_signed_action horizon nonnegative
  obtain ⟨second,massPaid⟩:=source_whole_mass_le_history horizon nonnegative
  let low:=max first second
  refine ⟨low,C,C0,fun radius above outerRadius M included order time inside => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
    outerRadius
  have word (index : FixedMatterSpatialWordIndex order) :
      spatialWordDiagonal stackedShortCurrent M index.toList time F radius+
        wordCoupling stackedShortCurrent M index.toList time F radius+
        spatialWordLoad stackedShortCurrent M index.toList time F radius≤
      -(butterflyGainViscosity.coeff^2/4)*wholeWordGraph M index.toList time+
        wholeWordTemporal M index.toList time F radius+
        C*wholeWordMass M index.toList time+
        spatialWordLoad stackedShortCurrent M index.toList time F radius := by
    have paid:=wordPaid radius ((le_max_left first second).trans above) outerRadius
      M ((le_max_left first second).trans included) time inside index.toList
    linarith only [paid]
  have summed:=Finset.sum_le_sum
    (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex order)))
    (fun index _ => word index)
  have mass:=massPaid radius ((le_max_right first second).trans above)
    outerRadius M order time inside
  have Cmass:=mul_le_mul_of_nonneg_left mass C0
  change NativeWindowHierarchyWrite.spatialRate stackedShortCurrent M order F radius 0 time≤
    -(butterflyGainViscosity.coeff^2/4)*wholeGraphCost M order time+
      wholeTemporal M order time F radius+
      wholeLoad M order time F radius+
      C*NativeWindowHierarchyHistory.history stackedShortCurrent M order F radius 0 time
  rw [spatialRate_action_blocks]
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum] at summed
  dsimp only [wholeGraphCost,wholeTemporal,wholeLoad,wholeMass] at *
  simp only [Finset.sum_add_distrib]
  linarith only [summed,Cmass]
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

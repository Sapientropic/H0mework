import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.WorkGate
import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualLoad

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredWorkResidual
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
variable {nu : Viscosity}

theorem source_remainder_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistorySchurAction.remainder seed M time=
      NativeWindowHistoryMeanResidualLoad.residualLoad seed M time-
        NativeWindowHistorySchurAction.feedback seed M time (mean (finiteHistory seed time M)) := by
  let w:=mean (finiteHistory seed time M)
  let r:=mean (NativeWindowHistoryOseen.rateHistory seed M time)
  let L:=laplacianFiber nu M w
  let d:=NativeWindowHistoryMeanDrift.drift seed M time w
  let b:=NativeWindowHistorySchurAction.feedback seed M time w
  let a:=NativeWindowHistorySchurAction.effective seed M time w
  let f:=NativeWindowHistorySchurAction.remainder seed M time
  let R:=NativeWindowHistoryMeanResidualLoad.residualLoad seed M time
  have source : r=a+f:=NativeWindowHistorySchurAction.source_rate seed M time
  have balance : r+nu.coeff • L=d+R:=NativeWindowHistoryMeanResidualLoad.source_mean_balance seed M time
  have principal : a+nu.coeff • L=d+b :=
    NativeWindowHistoryAllOrderPrincipal.lower_original seed M time w
  change f=R-b
  calc
    f=(r+nu.coeff • L)-(a+nu.coeff • L) := by rw [source]; abel
    _=(d+R)-(d+b) := by rw [balance,principal]
    _=R-b := by abel

theorem source_original_input (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    let w:=mean (finiteHistory seed time M)
    NativeWindowHistoryMeanAction.meanOperator seed M time w+
      NativeWindowHistoryMeanResidualLoad.residualLoad seed M time=
        mean (NativeWindowHistoryOseen.rateHistory seed M time) := by
  intro w
  have rate:=NativeWindowHistorySchurAction.source_rate seed M time
  calc
    _=NativeWindowHistorySchurAction.effective seed M time w+
        NativeWindowHistorySchurAction.remainder seed M time := by
      rw [source_remainder_original]
      simp only [NativeWindowHistorySchurAction.effective,add_apply]
      abel
    _=_ := rate.symm

theorem source_retained_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (word : List ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) (time : ℝ) :
    let w:=mean (finiteHistory seed time M)
    NativeWindowHistoryAllOrderWord.retained seed M word time=
      NativeWindowHistorySpatialWords.fiber M word
        (NativeWindowHistoryMeanAction.meanOperator seed M time w+
          NativeWindowHistoryMeanResidualLoad.residualLoad seed M time)-
        NativeWindowHistorySchurAction.effective seed M time
          (NativeWindowHistoryAllOrderWord.value seed M word time) := by
  intro w
  have split : NativeWindowHistorySchurAction.effective seed M time w+
      NativeWindowHistorySchurAction.remainder seed M time=
      NativeWindowHistoryMeanAction.meanOperator seed M time w+
        NativeWindowHistoryMeanResidualLoad.residualLoad seed M time := by
    rw [source_remainder_original]
    simp only [NativeWindowHistorySchurAction.effective,
      NativeWindowHistorySchurAction.feedback,add_apply]
    abel
  unfold NativeWindowHistoryAllOrderWord.retained NativeWindowHistoryAllOrderWord.bracket
  simp only [sub_apply,ContinuousLinearMap.comp_apply]
  calc
    _=NativeWindowHistorySpatialWords.fiber M word
        (NativeWindowHistorySchurAction.effective seed M time w+
          NativeWindowHistorySchurAction.remainder seed M time)-
        NativeWindowHistorySchurAction.effective seed M time
          (NativeWindowHistorySpatialWords.fiber M word w) := by rw [map_add]; abel
    _=_ := by rw [split]; rfl

theorem source_all_word_original_action (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) :
    let w:=mean (finiteHistory seed time M)
    NativeWindowHistoryAllOrderSpatial.principalWork seed M order time+
      NativeWindowHistoryAllOrderSpatial.work seed M order time=
      ∑word : SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy.FixedMatterSpatialWordIndex order,
        2*inner ℝ
          (NativeWindowHistoryAllOrderPrincipal.weight nu M
            (NativeWindowHistoryAllOrderWord.value seed M word.toList time))
          (NativeWindowHistorySpatialWords.fiber M word.toList
            (NativeWindowHistoryMeanAction.meanOperator seed M time w+
              NativeWindowHistoryMeanResidualLoad.residualLoad seed M time)) := by
  intro w
  simp only [NativeWindowHistoryAllOrderSpatial.principalWork,
    NativeWindowHistoryAllOrderSpatial.work,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro word _
  rw [source_retained_original]
  rw [inner_sub_right]
  ring

theorem source_all_word_original_rate (seed : GeneratedWholeRestartCurrent nu)
    (M order : ℕ) (time : ℝ) :
    let w:=mean (finiteHistory seed time M)
    deriv (NativeWindowHistoryAllOrderSpatial.energy seed M order) time=
      ∑word : SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy.FixedMatterSpatialWordIndex order,
        2*inner ℝ
          (NativeWindowHistoryAllOrderPrincipal.weight nu M
            (NativeWindowHistoryAllOrderWord.value seed M word.toList time))
          (NativeWindowHistorySpatialWords.fiber M word.toList
            (NativeWindowHistoryMeanAction.meanOperator seed M time w+
              NativeWindowHistoryMeanResidualLoad.residualLoad seed M time)) := by
  intro w
  rw [(NativeWindowHistoryAllOrderSpatial.source_hasDerivAt seed M order time).deriv]
  exact source_all_word_original_action seed M order time

end
end SaturationMonoid.NavierStokes.NativeCenteredWorkResidual

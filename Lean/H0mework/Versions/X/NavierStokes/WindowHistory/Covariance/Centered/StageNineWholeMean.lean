import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedRelative
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineBathArithmetic
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineMeanDiagonalSource

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
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section

theorem whole_word_mean_diagonal_paid (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
        ∀word : List Coordinate,
          let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
          let x:=NativeWindowHistoryMeanProjection.embed u
          let B:=fullMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius
          twoLeg B x (NativeWindowHistoryMeanProjection.embed
            (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))≤
            -(butterflyGainViscosity.coeff^2/2)*
              ‖laplacianFiber butterflyGainViscosity M u‖^2+C*‖u‖^2 := by
  obtain ⟨first,K1,K10,firstBound⟩:=prepared_full_metric_graph horizon nonnegative
  obtain ⟨second,K2,K20,secondBound⟩:=prepared_transpose_metric_graph horizon nonnegative
  let K:=max K1 K2
  have K0 : 0≤K:=K10.trans (le_max_left _ _)
  let epsilon:=butterflyGainViscosity.coeff^2/4
  have epsilon0 : 0<epsilon:=by dsimp only [epsilon]; positivity [butterflyGainViscosity.coeff_pos]
  let delta:=epsilon/(8*(K+1))
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let eta:=epsilon*delta/2
  have eta0 : 0<eta:=by dsimp only [eta]; positivity
  obtain ⟨Cd,Cd0,driftPaid⟩:=NativeStageNinePreparedCovariance.prepared_drift_relative
    horizon eta nonnegative eta0
  let C:=K+2*K*delta+Cd/(2*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨max first second,C,C0,fun radius above outerRadius M time inside word => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
  let x:=NativeWindowHistoryMeanProjection.embed u
  let L:=laplacianAction butterflyGainViscosity M x
  let LU:=laplacianFiber butterflyGainViscosity M u
  let d:=NativeWindowHistoryMeanProjection.embed
    (NativeWindowHistoryMeanDrift.drift stackedShortCurrent M time u)
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  have prepared : time∈Icc (-2 : ℝ) horizon:=inside
  have lap : ‖L‖=‖LU‖ := by
    dsimp only [L,x,LU,laplacianAction]
    rw [NativeWindowHistoryMeanProjection.comp_embed,
      NativeWindowHistoryMeanProjection.embed_norm]
  have mass : ‖x‖=‖u‖:=NativeWindowHistoryMeanProjection.embed_norm u
  have firstGraph:‖B x‖^2≤K*(‖L‖^2+‖x‖^2) :=
    ((firstBound radius ((le_max_left first second).trans above)
      outerRadius M time prepared x).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have secondGraph:‖T x‖^2≤K*(‖L‖^2+‖x‖^2) :=
    ((secondBound radius ((le_max_right first second).trans above)
      outerRadius M time prepared x).1).trans
      (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have firstHeat : -2*butterflyGainViscosity.coeff*inner ℝ (B x) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K*‖x‖^2 :=
    ((firstBound radius ((le_max_left first second).trans above)
      outerRadius M time prepared x).2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left K1 K2) (sq_nonneg _)))
  have secondHeat : -2*butterflyGainViscosity.coeff*inner ℝ (T x) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K*‖x‖^2 :=
    ((secondBound radius ((le_max_right first second).trans above)
      outerRadius M time prepared x).2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right K1 K2) (sq_nonneg _)))
  have small : ‖d‖^2≤eta*‖L‖^2+Cd*‖x‖^2 := by
    rw [show ‖d‖=‖NativeWindowHistoryMeanDrift.drift stackedShortCurrent M time u‖
      from NativeWindowHistoryMeanProjection.embed_norm _,lap,mass]
    exact driftPaid M time inside u
  have source:=mean_word_diagonal_split stackedShortCurrent M word time F radius
  have paid:=signed_bath_arithmetic butterflyGainViscosity.coeff K
    (‖x‖^2) (Cd*‖x‖^2) butterflyGainViscosity.coeff_pos K0
    x L d 0 (B x) (T x) le_rfl firstGraph secondGraph firstHeat secondHeat
    (by simpa only [epsilon,delta,eta] using small)
  have sourceRead : twoLeg B x (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))=
      inner ℝ ((-butterflyGainViscosity.coeff) • L+d) (B x+T x) := by
    change twoLeg B x _=inner ℝ _ _ at source
    exact source
  change twoLeg B x (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))≤
      -(butterflyGainViscosity.coeff^2/2)*‖LU‖^2+C*‖u‖^2
  rw [sourceRead]
  have paidRead : inner ℝ ((-butterflyGainViscosity.coeff) • L+d) (B x+T x)≤
      -(butterflyGainViscosity.coeff^2/2)*‖L‖^2+C*‖x‖^2 := by
    have paid' := paid
    simp only [add_zero,inner_zero_left] at paid'
    convert paid' using 1
    dsimp only [C,epsilon,delta]
    ring
  rw [← lap,← mass]
  exact paidRead
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

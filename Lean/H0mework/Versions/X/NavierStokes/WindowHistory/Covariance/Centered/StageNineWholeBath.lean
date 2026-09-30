import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeRelative
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineBathArithmetic

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
noncomputable section

theorem whole_word_bath_reduced (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius,∀M≥low,∀(time : ℝ),time∈Icc 0 horizon →
        ∀word : List Coordinate,
          let q:=NativeWindowHistoryMeanProjection.residual
            (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
          let B:=fullMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius
          let T:=transposeMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius
          twoLeg B q (NativeWindowHistoryMeanBlocks.bath stackedShortCurrent M time q)≤
            -(butterflyGainViscosity.coeff^2/2)*
              ‖laplacianAction butterflyGainViscosity M q‖^2+
            inner ℝ (NativeWindowHistoryMeanProjection.residual
              (NativeWindowHistorySchurAdvectorAction.wAction stackedShortCurrent M time q))
              (B q+T q)+C*‖q‖^2 := by
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
  obtain ⟨third,Cx,Cx0,xPaid⟩:=source_x_relative
    stackedShortCurrent horizon nonnegative eta eta0
  let C:=K+2*K*delta+Cx/(2*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  let low:=max (max first second) third
  refine ⟨low,C,C0,fun radius above outerRadius M included time inside word => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let q:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
  let L:=laplacianAction butterflyGainViscosity M q
  let X:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySchurAdvectorAction.xAction stackedShortCurrent M time q)
  let W:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySchurAdvectorAction.wAction stackedShortCurrent M time q)
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  have prepared : time∈Icc (-2 : ℝ) horizon:=⟨by linarith [inside.1],inside.2⟩
  have firstIndex : first≤low:=(le_max_left first second).trans (le_max_left _ _)
  have secondIndex : second≤low:=(le_max_right first second).trans (le_max_left _ _)
  have thirdIndex : third≤low:=le_max_right _ _
  have firstGraph:‖B q‖^2≤K*(‖L‖^2+‖q‖^2) :=
    ((firstBound radius (firstIndex.trans above) outerRadius M time prepared q).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have secondGraph:‖T q‖^2≤K*(‖L‖^2+‖q‖^2) :=
    ((secondBound radius (secondIndex.trans above) outerRadius M time prepared q).1).trans
      (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have firstHeat : -2*butterflyGainViscosity.coeff*inner ℝ (B q) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K*‖q‖^2 :=
    ((firstBound radius (firstIndex.trans above) outerRadius M time prepared q).2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left K1 K2) (sq_nonneg _)))
  have secondHeat : -2*butterflyGainViscosity.coeff*inner ℝ (T q) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K*‖q‖^2 :=
    ((secondBound radius (secondIndex.trans above) outerRadius M time prepared q).2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right K1 K2) (sq_nonneg _)))
  have xSmall : ‖X‖^2≤eta*‖L‖^2+Cx*‖q‖^2 :=
    xPaid M (thirdIndex.trans included) time inside q
  have source:=bath_word_split stackedShortCurrent M word time F radius
  have paid:=signed_bath_arithmetic butterflyGainViscosity.coeff K (‖q‖^2) (Cx*‖q‖^2)
    butterflyGainViscosity.coeff_pos K0 q L X W (B q) (T q)
    le_rfl firstGraph secondGraph firstHeat secondHeat
    (by simpa only [epsilon,delta,eta] using xSmall)
  have sourceRead : twoLeg B q (NativeWindowHistoryMeanBlocks.bath stackedShortCurrent M time q)=
      inner ℝ ((-butterflyGainViscosity.coeff) • L+X+W) (B q+T q) := by
    change twoLeg B q _=inner ℝ _ _ at source
    exact source
  change twoLeg B q (NativeWindowHistoryMeanBlocks.bath stackedShortCurrent M time q)≤
    -(butterflyGainViscosity.coeff^2/2)*‖L‖^2+
      inner ℝ W (B q+T q)+C*‖q‖^2
  have paidRead : inner ℝ ((-butterflyGainViscosity.coeff) • L+X+W) (B q+T q)≤
      -(butterflyGainViscosity.coeff^2/2)*‖L‖^2+
        inner ℝ W (B q+T q)+C*‖q‖^2 := by
    have paid' := paid
    convert paid' using 1
    dsimp only [C,epsilon,delta]
    ring
  exact sourceRead.trans_le paidRead
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

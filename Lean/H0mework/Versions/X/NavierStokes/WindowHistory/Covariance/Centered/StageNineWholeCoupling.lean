import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedAnnihilation
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineTransposeCoupling
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineCouplingArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1600000
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

theorem whole_word_coupling_paid (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc (-2 : ℝ) horizon →
        ∀word : List Coordinate,
          let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
          let q:=NativeWindowHistoryMeanProjection.residual
            (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
          wordCoupling stackedShortCurrent M word time
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius≤
            epsilon*(‖laplacianFiber butterflyGainViscosity M u‖^2+
              ‖laplacianAction butterflyGainViscosity M q‖^2)+
            C*(‖u‖^2+‖q‖^2) := by
  obtain ⟨first,K1,K10,firstBound⟩:=prepared_full_metric_graph horizon nonnegative
  obtain ⟨second,K2,K20,secondBound⟩:=prepared_transpose_metric_graph horizon nonnegative
  let K:=max K1 K2
  have K0 : 0≤K:=K10.trans (le_max_left _ _)
  let delta:=epsilon/(8*(K+1))
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let eta:=epsilon*delta/2
  have eta0 : 0<eta:=by dsimp only [eta]; positivity
  obtain ⟨Ca,Ca0,annPaid⟩:=NativeStageNinePreparedCovariance.prepared_annihilation_relative
    horizon eta nonnegative eta0
  obtain ⟨Cc,Cc0,crePaid⟩:=NativeStageNinePreparedCovariance.prepared_creation_relative
    horizon eta nonnegative eta0
  let D:=max Ca Cc
  have D0 : 0≤D:=Ca0.trans (le_max_left _ _)
  let C:=2*K*delta+D/(2*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨max first second,C,C0,fun radius above outerRadius M time inside word => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let h:=NativeWindowHistorySpatialWords.history stackedShortCurrent M word time
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let x:=NativeWindowHistoryMeanProjection.embed u
  let a:=NativeWindowHistoryMeanProjection.embed
    (NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h)
  let c:=NativeWindowHistoryMeanAction.creation stackedShortCurrent M time u
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  let LU:=laplacianFiber butterflyGainViscosity M u
  let LQ:=laplacianAction butterflyGainViscosity M q
  have prepared : time∈Icc (-2 : ℝ) horizon:=inside
  have lap : ‖laplacianAction butterflyGainViscosity M x‖=‖LU‖ := by
    dsimp only [x,LU,laplacianAction]
    rw [NativeWindowHistoryMeanProjection.comp_embed,
      NativeWindowHistoryMeanProjection.embed_norm]
  have mass : ‖x‖=‖u‖:=NativeWindowHistoryMeanProjection.embed_norm u
  have graphBx:‖B x‖^2≤K*(‖LU‖^2+‖u‖^2) := by
    have source:=(firstBound radius ((le_max_left first second).trans above)
      outerRadius M time prepared x).1
    rw [lap,mass] at source
    exact source.trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphTx:‖T x‖^2≤K*(‖LU‖^2+‖u‖^2) := by
    have source:=(secondBound radius ((le_max_right first second).trans above)
      outerRadius M time prepared x).1
    rw [lap,mass] at source
    exact source.trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphBq:‖B q‖^2≤K*(‖LQ‖^2+‖q‖^2) :=
    ((firstBound radius ((le_max_left first second).trans above)
      outerRadius M time prepared q).1).trans
      (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphTq:‖T q‖^2≤K*(‖LQ‖^2+‖q‖^2) :=
    ((secondBound radius ((le_max_right first second).trans above)
      outerRadius M time prepared q).1).trans
      (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have annSame : NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h=
      NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time q := by
    dsimp only [NativeWindowHistoryMeanBlocks.annihilation,
      ContinuousLinearMap.comp_apply,q]
    rw [NativeWindowHistoryBathResolvent.residual_square]
  have ann:‖a‖^2≤eta*‖LQ‖^2+Ca*‖q‖^2 := by
    rw [show ‖a‖=‖NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h‖
      from NativeWindowHistoryMeanProjection.embed_norm _,annSame]
    exact annPaid M time inside q
  have cre:‖c‖^2≤eta*‖LU‖^2+Cc*‖u‖^2 := crePaid M time inside u
  have actual:=wordCoupling_abs stackedShortCurrent M word time F radius
  have upper : wordCoupling stackedShortCurrent M word time F radius≤
      ‖a‖*(‖B x‖+‖T x‖)+‖c‖*(‖B q‖+‖T q‖) :=
    (le_abs_self _).trans actual
  have paid:=coupling_scalar epsilon K (‖u‖^2) (‖q‖^2)
    (Ca*‖q‖^2) (Cc*‖u‖^2)
    ‖LU‖ ‖LQ‖ ‖u‖ ‖q‖ ‖a‖ ‖c‖ ‖B x‖ ‖T x‖ ‖B q‖ ‖T q‖
    positive K0 graphBx graphTx graphBq graphTq le_rfl le_rfl
    (by simpa only [eta,delta] using ann)
    (by simpa only [eta,delta] using cre)
  have cap : Ca*‖q‖^2+Cc*‖u‖^2≤D*(‖u‖^2+‖q‖^2) := by
    have first:=mul_le_mul_of_nonneg_right (le_max_left Ca Cc) (sq_nonneg ‖q‖)
    have second:=mul_le_mul_of_nonneg_right (le_max_right Ca Cc) (sq_nonneg ‖u‖)
    nlinarith only [first,second]
  have scaled:=div_le_div_of_nonneg_right cap (by positivity : 0≤2*delta)
  have scaledRead : D*(‖u‖^2+‖q‖^2)/(2*delta)=
      (D/(2*delta))*(‖u‖^2+‖q‖^2) := by ring
  rw [scaledRead] at scaled
  change wordCoupling stackedShortCurrent M word time F radius≤
    epsilon*(‖LU‖^2+‖LQ‖^2)+C*(‖u‖^2+‖q‖^2)
  have paidRead : ‖a‖*(‖B x‖+‖T x‖)+‖c‖*(‖B q‖+‖T q‖)≤
      epsilon*(‖LU‖^2+‖LQ‖^2)+C*(‖u‖^2+‖q‖^2) := by
    dsimp only [C]
    nlinarith only [paid,scaled]
  exact upper.trans paidRead
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineCouplingArithmetic
set_option autoImplicit false
set_option maxHeartbeats 800000
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

theorem prepared_first_word_coupling_paid (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc 0 horizon →
        ∀j : Coordinate,
          let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time
          let q:=NativeCenteredWeightedResidualRate.centeredWord stackedShortCurrent M j time
          wordCoupling stackedShortCurrent M [j] time
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius≤
            epsilon*(‖laplacianFiber butterflyGainViscosity M u‖^2+
              ‖laplacianAction butterflyGainViscosity M q‖^2)+C := by
  obtain ⟨first,K1,K10,firstBound⟩ :=
    prepared_full_metric_graph horizon nonnegative
  obtain ⟨last,K2,K20,lastBound⟩ :=
    prepared_transpose_metric_graph horizon nonnegative
  let K:=max K1 K2
  have K0 : 0≤K := le_trans K10 (le_max_left _ _)
  let delta:=epsilon/(8*(K+1))
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let eta:=epsilon*delta/2
  have eta0 : 0<eta := by dsimp only [eta]; positivity
  obtain ⟨Ca,Ca0,annPaid⟩ := NativeCenteredCouplingPaid.source_annihilation_q_paid
    stackedShortCurrent horizon eta eta0
  obtain ⟨Cc,Cc0,crePaid⟩ := NativeCenteredCouplingPaid.source_creation_u_paid
    stackedShortCurrent horizon eta eta0
  let GU:=max 0 (NativeWindowAugmentedPayment.graphBudget stackedShortCurrent 0 horizon)
  let GQ:=NativeWindowHistorySchurTemporalControl.gradientBudget stackedShortCurrent horizon
  have GU0 : 0≤GU := le_max_left _ _
  have GQ0 : 0≤GQ := le_max_left _ _
  let C:=2*K*delta*(GU+GQ)+(Ca+Cc)/(2*delta)
  have C0 : 0≤C := by dsimp only [C]; positivity
  refine ⟨max first last,C,C0,fun radius above outerRadius M time inside j => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time
  let h:=NativeWindowHistorySpatialWords.history stackedShortCurrent M [j] time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let x:=NativeWindowHistoryMeanProjection.embed u
  let a:=NativeWindowHistoryMeanProjection.embed
    (NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h)
  let c:=NativeWindowHistoryMeanAction.creation stackedShortCurrent M time u
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  let LU:=laplacianFiber butterflyGainViscosity M u
  let LQ:=laplacianAction butterflyGainViscosity M q
  have timePrepared : time∈Icc (-2 : ℝ) horizon := ⟨by linarith [inside.1],inside.2⟩
  have graphBx:‖B x‖^2≤K*(‖LU‖^2+‖u‖^2) := by
    have source:=(firstBound radius ((le_max_left first last).trans above)
      outerRadius M time timePrepared x).1
    have lap : ‖laplacianAction butterflyGainViscosity M x‖=‖LU‖ := by
      dsimp only [x,LU,laplacianAction]
      rw [NativeWindowHistoryMeanProjection.comp_embed,
        NativeWindowHistoryMeanProjection.embed_norm]
    rw [lap,show ‖x‖=‖u‖ from NativeWindowHistoryMeanProjection.embed_norm u] at source
    exact source.trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphTx:‖T x‖^2≤K*(‖LU‖^2+‖u‖^2) := by
    have source:=(lastBound radius ((le_max_right first last).trans above)
      outerRadius M time timePrepared x).1
    have lap : ‖laplacianAction butterflyGainViscosity M x‖=‖LU‖ := by
      dsimp only [x,LU,laplacianAction]
      rw [NativeWindowHistoryMeanProjection.comp_embed,
        NativeWindowHistoryMeanProjection.embed_norm]
    rw [lap,show ‖x‖=‖u‖ from NativeWindowHistoryMeanProjection.embed_norm u] at source
    exact source.trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphBq:‖B q‖^2≤K*(‖LQ‖^2+‖q‖^2) :=
    ((firstBound radius ((le_max_left first last).trans above)
      outerRadius M time timePrepared q).1).trans
        (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have graphTq:‖T q‖^2≤K*(‖LQ‖^2+‖q‖^2) :=
    ((lastBound radius ((le_max_right first last).trans above)
      outerRadius M time timePrepared q).1).trans
        (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
          (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have massU:‖u‖^2≤GU :=
    NativeCenteredMeanPrincipal.source_first_word_u_mass stackedShortCurrent horizon M time inside j
  have massQ:‖q‖^2≤GQ :=
    NativeCenteredBathPaid.source_first_word_q_mass stackedShortCurrent horizon M time inside j
  have annSame : NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h=
      NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time q := by
    dsimp only [NativeWindowHistoryMeanBlocks.annihilation,
      ContinuousLinearMap.comp_apply,q]
    rw [NativeWindowHistoryBathResolvent.residual_square]
  have ann:‖a‖^2≤eta*‖LQ‖^2+Ca := by
    rw [show ‖a‖=‖NativeWindowHistoryMeanBlocks.annihilation stackedShortCurrent M time h‖
      from NativeWindowHistoryMeanProjection.embed_norm _ ,annSame]
    exact annPaid M time inside j
  have cre:‖c‖^2≤eta*‖LU‖^2+Cc := crePaid M time inside j
  have actual:=wordCoupling_abs stackedShortCurrent M [j] time F radius
  have upper : wordCoupling stackedShortCurrent M [j] time F radius≤
      ‖a‖*(‖B x‖+‖T x‖)+‖c‖*(‖B q‖+‖T q‖) :=
    (le_abs_self _).trans actual
  have paid:=coupling_scalar epsilon K GU GQ Ca Cc
    ‖LU‖ ‖LQ‖ ‖u‖ ‖q‖ ‖a‖ ‖c‖ ‖B x‖ ‖T x‖ ‖B q‖ ‖T q‖
    positive K0 graphBx graphTx graphBq graphTq massU massQ
    (by simpa only [eta,delta] using ann)
    (by simpa only [eta,delta] using cre)
  change wordCoupling stackedShortCurrent M [j] time F radius≤
    epsilon*(‖LU‖^2+‖LQ‖^2)+C
  have paid' : ‖a‖*(‖B x‖+‖T x‖)+‖c‖*(‖B q‖+‖T q‖)≤
      epsilon*(‖LU‖^2+‖LQ‖^2)+C := by
    simpa only [C,delta,add_assoc] using paid
  exact upper.trans paid'

theorem prepared_first_order_coupling_paid (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc 0 horizon →
        (∑j : Coordinate,wordCoupling stackedShortCurrent M [j] time
          (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius) radius)≤
          epsilon*(∑j : Coordinate,
            (‖laplacianFiber butterflyGainViscosity M
              (NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time)‖^2+
            ‖laplacianAction butterflyGainViscosity M
              (NativeCenteredWeightedResidualRate.centeredWord stackedShortCurrent M j time)‖^2))+C := by
  obtain ⟨low,C,C0,paid⟩ :=
    prepared_first_word_coupling_paid horizon nonnegative epsilon positive
  refine ⟨low,3*C,by positivity,fun radius above outerRadius M time inside => ?_⟩
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun j _ => paid radius above outerRadius M time inside j)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using summed
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

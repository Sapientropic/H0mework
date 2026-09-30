import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineMeanDiagonalSource
set_option autoImplicit false
set_option maxHeartbeats 800000
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
variable {nu : Viscosity}

theorem prepared_first_word_mean_diagonal_paid
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc 0 horizon →
        ∀j : Coordinate,
          let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time
          let x:=NativeWindowHistoryMeanProjection.embed u
          let B:=fullMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius
          twoLeg B x (NativeWindowHistoryMeanProjection.embed
            (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))≤
            -(butterflyGainViscosity.coeff^2/2)*
              ‖laplacianFiber butterflyGainViscosity M u‖^2+C := by
  obtain ⟨first,K1,K10,firstBound⟩:=prepared_full_metric_graph horizon nonnegative
  obtain ⟨last,K2,K20,lastBound⟩:=prepared_transpose_metric_graph horizon nonnegative
  let K:=max K1 K2
  have K0 : 0≤K:=(le_max_left K1 K2).trans' K10
  let epsilon:=butterflyGainViscosity.coeff^2/4
  have epsilon0 : 0<epsilon:=by dsimp only [epsilon]; positivity [butterflyGainViscosity.coeff_pos]
  let delta:=epsilon/(8*(K+1))
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let eta:=epsilon*delta/2
  have eta0 : 0<eta:=by dsimp only [eta]; positivity
  obtain ⟨Cd,Cd0,driftPaid⟩:=source_first_word_drift_paid
    stackedShortCurrent horizon eta eta0
  let GU:=max 0 (NativeWindowAugmentedPayment.graphBudget stackedShortCurrent 0 horizon)
  have GU0 : 0≤GU:=le_max_left _ _
  let C:=(K+2*K*delta)*GU+Cd/(2*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨max first last,C,C0,fun radius above outerRadius M time inside j => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time
  let x:=NativeWindowHistoryMeanProjection.embed u
  let L:=laplacianAction butterflyGainViscosity M x
  let LU:=laplacianFiber butterflyGainViscosity M u
  let d:=NativeWindowHistoryMeanProjection.embed
    (NativeWindowHistoryMeanDrift.drift stackedShortCurrent M time u)
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  have prepared : time∈Icc (-2 : ℝ) horizon:=⟨by linarith [inside.1],inside.2⟩
  have lap : ‖L‖=‖LU‖ := by
    dsimp only [L,x,LU,laplacianAction]
    rw [NativeWindowHistoryMeanProjection.comp_embed,
      NativeWindowHistoryMeanProjection.embed_norm]
  have mass : ‖x‖^2≤GU := by
    rw [show ‖x‖=‖u‖ from NativeWindowHistoryMeanProjection.embed_norm u]
    exact NativeCenteredMeanPrincipal.source_first_word_u_mass
      stackedShortCurrent horizon M time inside j
  have firstGraph:‖B x‖^2≤K*(‖LU‖^2+‖x‖^2) := by
    have paid:=(firstBound radius ((le_max_left first last).trans above)
      outerRadius M time prepared x).1
    rw [lap] at paid
    exact paid.trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have lastGraph:‖T x‖^2≤K*(‖LU‖^2+‖x‖^2) := by
    have paid:=(lastBound radius ((le_max_right first last).trans above)
      outerRadius M time prepared x).1
    rw [lap] at paid
    exact paid.trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have firstHeat: -2*butterflyGainViscosity.coeff*inner ℝ (B x) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K1*‖x‖^2 :=
    (firstBound radius ((le_max_left first last).trans above)
      outerRadius M time prepared x).2
  have lastHeat: -2*butterflyGainViscosity.coeff*inner ℝ (T x) L≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+K2*‖x‖^2 :=
    (lastBound radius ((le_max_right first last).trans above)
      outerRadius M time prepared x).2
  have viscous : -butterflyGainViscosity.coeff*
      (inner ℝ L (B x)+inner ℝ L (T x))≤
      -butterflyGainViscosity.coeff^2*‖LU‖^2+K*‖x‖^2 := by
    have firstSwap:=real_inner_comm (B x) L
    have lastSwap:=real_inner_comm (T x) L
    have k1:=mul_le_mul_of_nonneg_right (le_max_left K1 K2) (sq_nonneg ‖x‖)
    have k2:=mul_le_mul_of_nonneg_right (le_max_right K1 K2) (sq_nonneg ‖x‖)
    rw [← lap]
    change -butterflyGainViscosity.coeff*
      (inner ℝ L (B x)+inner ℝ L (T x))≤
      -butterflyGainViscosity.coeff^2*‖L‖^2+
        (max K1 K2)*‖x‖^2
    rw [firstSwap,lastSwap]
    have heatSum:=add_le_add firstHeat lastHeat
    have capSum:=add_le_add k1 k2
    nlinarith only [heatSum,capSum]
  have driftBound:‖d‖^2≤eta*‖LU‖^2+Cd := by
    rw [show ‖d‖=‖NativeWindowHistoryMeanDrift.drift stackedShortCurrent M time u‖
      from NativeWindowHistoryMeanProjection.embed_norm _]
    exact driftPaid M time inside j
  have driftCost:=drift_scalar epsilon K GU Cd ‖LU‖ ‖x‖ ‖d‖ ‖B x‖ ‖T x‖
    epsilon0 K0 firstGraph lastGraph mass
    (by simpa only [eta,delta] using driftBound)
  have driftPair:inner ℝ d (B x+T x)≤
      epsilon*‖LU‖^2+2*K*delta*GU+Cd/(2*delta) := by
    have pair:=real_inner_le_norm d (B x+T x)
    have norm:=norm_add_le (B x) (T x)
    have scaled:=mul_le_mul_of_nonneg_left norm (norm_nonneg d)
    exact (pair.trans scaled).trans driftCost
  have split:=mean_word_diagonal_split stackedShortCurrent M [j] time F radius
  have algebra : inner ℝ ((-butterflyGainViscosity.coeff) • L+d) (B x+T x)=
      -butterflyGainViscosity.coeff*(inner ℝ L (B x)+inner ℝ L (T x))+
        inner ℝ d (B x+T x) := by
    have addLeft:=inner_add_left (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H)
      ((-butterflyGainViscosity.coeff) • L) d (B x+T x)
    have smulLeft:=real_inner_smul_left (F := NativeWindowTraceWholeHistory.H)
      L (B x+T x) (-butterflyGainViscosity.coeff)
    have addRight:=inner_add_right (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H)
      L (B x) (T x)
    calc
      _=inner ℝ ((-butterflyGainViscosity.coeff) • L) (B x+T x)+
          inner ℝ d (B x+T x) := addLeft
      _=(-butterflyGainViscosity.coeff)*inner ℝ L (B x+T x)+
          inner ℝ d (B x+T x) := congrArg (fun z : ℝ => z+inner ℝ d (B x+T x)) smulLeft
      _=(-butterflyGainViscosity.coeff)*
          (inner ℝ L (B x)+inner ℝ L (T x))+
          inner ℝ d (B x+T x) :=
        congrArg (fun z : ℝ => (-butterflyGainViscosity.coeff)*z+
          inner ℝ d (B x+T x)) addRight
      _=_ := by ring
  change twoLeg B x (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))≤
      -(butterflyGainViscosity.coeff^2/2)*‖LU‖^2+C
  rw [split,algebra]
  have massScaled:=mul_le_mul_of_nonneg_left mass K0
  have combined : -butterflyGainViscosity.coeff*
      (inner ℝ L (B x)+inner ℝ L (T x))+
        inner ℝ d (B x+T x)≤
      (-butterflyGainViscosity.coeff^2+epsilon)*‖LU‖^2+C := by
    dsimp only [C]
    nlinarith only [viscous,driftPair,massScaled]
  have coefficient : -butterflyGainViscosity.coeff^2+epsilon≤
      -(butterflyGainViscosity.coeff^2/2) := by
    dsimp only [epsilon]
    nlinarith only [sq_nonneg butterflyGainViscosity.coeff]
  have scaled:=mul_le_mul_of_nonneg_right coefficient (sq_nonneg ‖LU‖)
  exact combined.trans (add_le_add scaled le_rfl)

theorem prepared_first_order_mean_diagonal_paid
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius M (time : ℝ),time∈Icc 0 horizon →
        (∑j : Coordinate,
          let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time
          let x:=NativeWindowHistoryMeanProjection.embed u
          let B:=fullMetricAction stackedShortCurrent time M
            (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
              outerRadius) radius
          twoLeg B x (NativeWindowHistoryMeanProjection.embed
            (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u)))≤
          -(butterflyGainViscosity.coeff^2/2)*
            (∑j : Coordinate,
              ‖laplacianFiber butterflyGainViscosity M
                (NativeWindowHistoryAllOrderWord.value stackedShortCurrent M [j] time)‖^2)+C := by
  obtain ⟨low,C,C0,paid⟩ :=
    prepared_first_word_mean_diagonal_paid horizon nonnegative
  refine ⟨low,3*C,by positivity,fun radius above outerRadius M time inside => ?_⟩
  have summed:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun j _ => paid radius above outerRadius M time inside j)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using summed
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeMean
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeBath
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineWholeCoupling
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineActionBlocks

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

def wholeWordGraph (M : ℕ) (word : List Coordinate) (time : ℝ) : ℝ :=
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
  let q:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
  ‖laplacianFiber butterflyGainViscosity M u‖^2+
    ‖laplacianAction butterflyGainViscosity M q‖^2

def wholeWordMass (M : ℕ) (word : List Coordinate) (time : ℝ) : ℝ :=
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
  let q:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
  ‖u‖^2+‖q‖^2

def wholeWordTemporal (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) : ℝ :=
  let q:=NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySpatialWords.history stackedShortCurrent M word time)
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  inner ℝ (NativeWindowHistoryMeanProjection.residual
    (NativeWindowHistorySchurAdvectorAction.wAction stackedShortCurrent M time q))
    (B q+T q)

theorem whole_word_signed_action (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧
      ∀radius≥low,∀outerRadius,∀M≥low,∀(time : ℝ),time∈Icc 0 horizon →
        ∀word : List Coordinate,
          let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube
            outerRadius
          spatialWordDiagonal stackedShortCurrent M word time F radius+
            wordCoupling stackedShortCurrent M word time F radius≤
          -(butterflyGainViscosity.coeff^2/4)*wholeWordGraph M word time+
            wholeWordTemporal M word time F radius+
            C*wholeWordMass M word time := by
  obtain ⟨first,Cm,Cm0,meanPaid⟩:=whole_word_mean_diagonal_paid horizon nonnegative
  obtain ⟨second,Cb,Cb0,bathPaid⟩:=whole_word_bath_reduced horizon nonnegative
  let epsilon:=butterflyGainViscosity.coeff^2/4
  have epsilon0 : 0<epsilon:=by dsimp only [epsilon]; positivity [butterflyGainViscosity.coeff_pos]
  obtain ⟨third,Cc,Cc0,couplingPaid⟩:=whole_word_coupling_paid
    horizon nonnegative epsilon epsilon0
  let low:=max (max first second) third
  let C:=Cm+Cb+Cc
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨low,C,C0,fun radius above outerRadius M included time inside word => ?_⟩
  let F:=ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube outerRadius
  let u:=NativeWindowHistoryAllOrderWord.value stackedShortCurrent M word time
  let h:=NativeWindowHistorySpatialWords.history stackedShortCurrent M word time
  let q:=NativeWindowHistoryMeanProjection.residual h
  let x:=NativeWindowHistoryMeanProjection.embed u
  let B:=fullMetricAction stackedShortCurrent time M F radius
  let T:=transposeMetricAction stackedShortCurrent time M F radius
  let U:=‖laplacianFiber butterflyGainViscosity M u‖^2
  let Q:=‖laplacianAction butterflyGainViscosity M q‖^2
  let U0:=‖u‖^2
  let Q0:=‖q‖^2
  let W:=wholeWordTemporal M word time F radius
  have prepared : time∈Icc (-2 : ℝ) horizon:=⟨by linarith [inside.1],inside.2⟩
  have mean : twoLeg B x (NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))≤
      -(butterflyGainViscosity.coeff^2/2)*U+Cm*U0 := by
    have paid:=meanPaid radius ((le_max_left first second).trans (le_max_left _ _ |>.trans above))
      outerRadius M time prepared word
    exact paid
  have bath : twoLeg B q (NativeWindowHistoryMeanBlocks.bath stackedShortCurrent M time q)≤
      -(butterflyGainViscosity.coeff^2/2)*Q+W+Cb*Q0 := by
    have paid:=bathPaid radius ((le_max_right first second).trans (le_max_left _ _ |>.trans above))
      outerRadius M ((le_max_right first second).trans (le_max_left _ _ |>.trans included))
      time inside word
    exact paid
  have coupling : wordCoupling stackedShortCurrent M word time F radius≤
      epsilon*(U+Q)+Cc*(U0+Q0) := by
    have paid:=couplingPaid radius ((le_max_right _ _).trans above)
      outerRadius M time prepared word
    exact paid
  have row : spatialWordDiagonal stackedShortCurrent M word time F radius=
      twoLeg B x (NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryMeanAction.meanOperator stackedShortCurrent M time u))+
      twoLeg B q (NativeWindowHistoryMeanBlocks.bath stackedShortCurrent M time q) := rfl
  change spatialWordDiagonal stackedShortCurrent M word time F radius+
      wordCoupling stackedShortCurrent M word time F radius≤
      -(butterflyGainViscosity.coeff^2/4)*(U+Q)+W+C*(U0+Q0)
  rw [row]
  have cross1:=mul_nonneg Cm0 (sq_nonneg ‖q‖)
  have cross2:=mul_nonneg Cb0 (sq_nonneg ‖u‖)
  dsimp only [C,epsilon] at *
  nlinarith only [mean,bath,coupling,cross1,cross2]
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

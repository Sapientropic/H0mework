import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineTransposeHistory
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNineCoupling

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
noncomputable section
variable {nu : Viscosity}

theorem twoLeg_adjoint (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) (x y : NativeWindowTraceWholeHistory.H) :
    twoLeg (fullMetricAction seed time M F radius) x y=
      inner ℝ y ((fullMetricAction seed time M F radius) x+
        (transposeMetricAction seed time M F radius) x) := by
  have dual:=transpose_action_dual seed time M F radius y x
  have split : inner ℝ y
      ((fullMetricAction seed time M F radius) x+
        (transposeMetricAction seed time M F radius) x)=
      inner ℝ y ((fullMetricAction seed time M F radius) x)+
        inner ℝ y ((transposeMetricAction seed time M F radius) x) :=
    inner_add_right (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H) _ _ _
  dsimp only [twoLeg]
  linarith only [dual,split]

theorem wordCoupling_adjoint (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let q:=NativeWindowHistoryMeanProjection.residual h
    let x:=NativeWindowHistoryMeanProjection.embed u
    let a:=NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanBlocks.annihilation seed M time h)
    let c:=NativeWindowHistoryMeanAction.creation seed M time u
    let B:=fullMetricAction seed time M F radius
    let T:=transposeMetricAction seed time M F radius
    wordCoupling seed M word time F radius=
      inner ℝ a (B x+T x)+inner ℝ c (B q+T q) := by
  intro h u q x a c B T
  have first:=transpose_action_dual seed time M F radius a x
  have last:=transpose_action_dual seed time M F radius c q
  change inner ℝ a (B x)+inner ℝ x (B a)+inner ℝ c (B q)+inner ℝ q (B c)=
    inner ℝ a (B x+T x)+inner ℝ c (B q+T q)
  have splitA : inner ℝ a (B x+T x)=inner ℝ a (B x)+inner ℝ a (T x) :=
    inner_add_right (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H) a (B x) (T x)
  have splitC : inner ℝ c (B q+T q)=inner ℝ c (B q)+inner ℝ c (T q) :=
    inner_add_right (𝕜 := ℝ) (E := NativeWindowTraceWholeHistory.H) c (B q) (T q)
  rw [splitA,splitC]
  linarith only [first,last]

theorem wordCoupling_abs (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (word : List Coordinate) (time : ℝ)
    (F : Finset ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector)
    (radius : ℕ) :
    let h:=NativeWindowHistorySpatialWords.history seed M word time
    let u:=NativeWindowHistoryAllOrderWord.value seed M word time
    let q:=NativeWindowHistoryMeanProjection.residual h
    let x:=NativeWindowHistoryMeanProjection.embed u
    let a:=NativeWindowHistoryMeanProjection.embed
      (NativeWindowHistoryMeanBlocks.annihilation seed M time h)
    let c:=NativeWindowHistoryMeanAction.creation seed M time u
    let B:=fullMetricAction seed time M F radius
    let T:=transposeMetricAction seed time M F radius
    |wordCoupling seed M word time F radius|≤
      ‖a‖*(‖B x‖+‖T x‖)+‖c‖*(‖B q‖+‖T q‖) := by
  intro h u q x a c B T
  rw [wordCoupling_adjoint seed M word time F radius]
  exact (abs_add_le _ _).trans
    (add_le_add
      ((abs_real_inner_le_norm a (B x+T x)).trans
        (mul_le_mul_of_nonneg_left (norm_add_le (B x) (T x)) (norm_nonneg a)))
      ((abs_real_inner_le_norm c (B q+T q)).trans
        (mul_le_mul_of_nonneg_left (norm_add_le (B q) (T q)) (norm_nonneg c))))
end
end SaturationMonoid.NavierStokes.NativeStageNineWindowEnergy

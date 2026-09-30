import H0mework.NavierStokes.Restart.PositiveOutputWorkDualBudget

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SpaceTimeWork

open scoped ENNReal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork

noncomputable section

variable {time : Real} (left right : SpaceTimeState time)

def row (wave : IntegerWavevector) (actual : Icc (0 : Real) time) : Real :=
  2 * complexCoordinateRealInner (left actual wave) (right actual wave)

private def envelope (wave : IntegerWavevector) (actual : Icc (0 : Real) time) : Real :=
  3 * (‖left actual wave‖ ^ 2 + ‖right actual wave‖ ^ 2)

private theorem norm_row_le (wave : IntegerWavevector) (actual : Icc (0 : Real) time) :
    ‖row left right wave actual‖ ≤ envelope left right wave actual := by
  have pairing := abs_complexCoordinateRealInner_le_three_mul_norm
    (left actual wave) (right actual wave)
  have square := sq_nonneg (‖left actual wave‖ - ‖right actual wave‖)
  rw [row, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
  unfold envelope
  nlinarith

private theorem envelope_hasSum (actual : Icc (0 : Real) time) :
    HasSum (fun wave => envelope left right wave actual)
      (3 * (‖left actual‖ ^ 2 + ‖right actual‖ ^ 2)) := by
  have sumLeft : HasSum (fun wave : IntegerWavevector => ‖left actual wave‖ ^ 2) (‖left actual‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (left actual)
  have sumRight : HasSum (fun wave : IntegerWavevector => ‖right actual wave‖ ^ 2) (‖right actual‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (right actual)
  exact (sumLeft.add sumRight).mul_left 3

theorem row_measurable (wave : IntegerWavevector) :
    AEStronglyMeasurable (row left right wave) (commonTimeMeasure time) := by
  have leftRow := (lp.evalCLM Complex (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous
    |>.comp_aestronglyMeasurable (MeasureTheory.Lp.aestronglyMeasurable left)
  have rightRow := (lp.evalCLM Complex (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous
    |>.comp_aestronglyMeasurable (MeasureTheory.Lp.aestronglyMeasurable right)
  exact (complexCoordinateRealInner_prod_continuous.comp_aestronglyMeasurable
    (leftRow.prodMk rightRow)).const_mul 2

theorem row_summable (actual : Icc (0 : Real) time) :
    Summable fun wave => row left right wave actual :=
  (envelope_hasSum left right actual).summable.of_norm_bounded
    (norm_row_le left right · actual)

private theorem envelope_integrable :
    Integrable (fun actual => ∑' wave, envelope left right wave actual) (commonTimeMeasure time) := by
  have same : (fun actual => ∑' wave, envelope left right wave actual) =
      fun actual => 3 * (‖left actual‖ ^ 2 + ‖right actual‖ ^ 2) :=
    funext fun actual => (envelope_hasSum left right actual).tsum_eq
  rw [same]
  exact ((MeasureTheory.Lp.memLp left).integrable_norm_pow (by norm_num) |>.add
    ((MeasureTheory.Lp.memLp right).integrable_norm_pow (by norm_num))).const_mul 3

theorem total_integrable :
    Integrable (fun actual => ∑' wave, row left right wave actual) (commonTimeMeasure time) := by
  apply (envelope_integrable left right).mono'
  · exact AEStronglyMeasurable.tsum (row_measurable left right)
  · filter_upwards with actual
    have absolute := (row_summable left right actual).norm
    exact (norm_tsum_le_tsum_norm absolute).trans
      (absolute.tsum_le_tsum (norm_row_le left right · actual) (envelope_hasSum left right actual).summable)

/-- Absolute domination permits whole-row summation through the actual time
integral on every subwindow, using only the two generated L² carriers. -/
theorem integral_hasSum (region : Set (Icc (0 : Real) time)) :
    HasSum (fun wave : IntegerWavevector => ∫ actual in region, row left right wave actual
      ∂(commonTimeMeasure time))
      (∫ actual in region, ∑' wave, row left right wave actual ∂(commonTimeMeasure time)) := by
  apply MeasureTheory.hasSum_integral_of_dominated_convergence (envelope left right)
    (fun wave => (row_measurable left right wave).restrict)
  · intro wave
    filter_upwards with actual
    exact norm_row_le left right wave actual
  · filter_upwards with actual
    exact (envelope_hasSum left right actual).summable
  · exact (envelope_integrable left right).restrict
  · filter_upwards with actual
    exact (row_summable left right actual).hasSum

end
end SaturationMonoid.NavierStokes.SpaceTimeWork

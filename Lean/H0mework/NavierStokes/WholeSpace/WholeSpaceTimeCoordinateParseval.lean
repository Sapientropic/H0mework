import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeGradientLowerSemicontinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Whole space-time coordinate Parseval

The whole time-`L²` Fourier carrier is exactly the square-summable family of
its fixed-wave time-`L²` restrictions.  This is the time-by-frequency
Parseval/Fubini identity needed to assemble the source-generated per-wave
Duhamel laws back into one whole continuous Fourier state.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval

open scoped BigOperators ENNReal

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity

noncomputable section

/-- The squared norm of a whole time-`L²` Fourier state is its pointwise
Hilbert norm squared integrated over the common time carrier. -/
theorem spaceTimeState_norm_sq_eq_integral
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    ‖state‖ ^ 2 =
      ∫ time,
        ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.Lp.norm_def]
  rw [MeasureTheory.toReal_eLpNorm
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (MeasureTheory.Lp.aestronglyMeasurable state)]
  norm_num
  have powerIdentity :
      ((∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ time,
          ‖state time‖ ^ 2 ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  convert powerIdentity using 1
  all_goals norm_num

/--
Exact time-by-frequency Parseval/Fubini identity on the actual whole
space-time carrier.

No finite support, tail silence, or coordinate summability witness is
supplied by a caller.  Pointwise `ℓ²` Parseval and the time-`L²` membership of
`state` generate the summability needed to interchange time integration and
the complete integer-frequency series.
-/
theorem hasSum_fixedWaveSpaceTimeRestriction_norm_sq
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    HasSum
      (fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction
          requestedTime wave state‖ ^ 2)
      (‖state‖ ^ 2) := by
  let coordinateDensity :
      IntegerWavevector →
        Set.Icc (0 : ℝ) requestedTime → ℝ :=
    fun wave time => ‖state time wave‖ ^ 2
  have coordinateDensityMeasurable :
      ∀ wave : IntegerWavevector,
        AEStronglyMeasurable
          (coordinateDensity wave)
          (commonTimeMeasure requestedTime) := by
    intro wave
    have rowMeasurable :
        AEStronglyMeasurable
          (fun time => state time wave)
          (commonTimeMeasure requestedTime) :=
      (lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave).continuous.comp_aestronglyMeasurable
          (MeasureTheory.Lp.aestronglyMeasurable state)
    exact
      (continuous_pow 2).comp_aestronglyMeasurable
        rowMeasurable.norm
  have coordinateHasSum :
      ∀ time : Set.Icc (0 : ℝ) requestedTime,
        HasSum
          (fun wave : IntegerWavevector =>
            coordinateDensity wave time)
          (‖state time‖ ^ 2) := by
    intro time
    simpa only [coordinateDensity, ENNReal.toReal_ofNat,
      Real.rpow_two] using
      (lp.hasSum_norm
        (p := (2 : ℝ≥0∞)) (by norm_num) (state time))
  have wholeDensityIntegrable :
      Integrable
        (fun time : Set.Icc (0 : ℝ) requestedTime =>
          ‖state time‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp state).integrable_norm_pow
      (by norm_num)
  have integratedHasSum :
      HasSum
        (fun wave : IntegerWavevector =>
          ∫ time,
            coordinateDensity wave time
            ∂(commonTimeMeasure requestedTime))
        (∫ time,
          ‖state time‖ ^ 2
          ∂(commonTimeMeasure requestedTime)) := by
    apply
      MeasureTheory.hasSum_integral_of_dominated_convergence
        coordinateDensity
        coordinateDensityMeasurable
    · intro wave
      filter_upwards with time
      exact
        Real.norm_of_nonneg
          (sq_nonneg ‖state time wave‖) |>.le
    · filter_upwards with time
      exact (coordinateHasSum time).summable
    · rw [show
        (fun time =>
          ∑' wave : IntegerWavevector,
            coordinateDensity wave time) =
          (fun time => ‖state time‖ ^ 2) by
            funext time
            exact (coordinateHasSum time).tsum_eq]
      exact wholeDensityIntegrable
    · filter_upwards with time
      exact coordinateHasSum time
  have perWaveIntegral :
      ∀ wave : IntegerWavevector,
        ‖fixedWaveSpaceTimeRestriction
          requestedTime wave state‖ ^ 2 =
          ∫ time,
            coordinateDensity wave time
            ∂(commonTimeMeasure requestedTime) := by
    intro wave
    rw [fixedWaveSpaceTimeState_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave state] with time rowEq
    simp only [coordinateDensity]
    rw [rowEq]
  rw [show
    (fun wave : IntegerWavevector =>
      ‖fixedWaveSpaceTimeRestriction
        requestedTime wave state‖ ^ 2) =
      (fun wave : IntegerWavevector =>
        ∫ time,
          coordinateDensity wave time
          ∂(commonTimeMeasure requestedTime)) by
        funext wave
        exact perWaveIntegral wave]
  rw [spaceTimeState_norm_sq_eq_integral]
  exact integratedHasSum

/-- The fixed-wave squared time-`L²` norms form a genuine summable family. -/
theorem summable_fixedWaveSpaceTimeRestriction_norm_sq
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    Summable fun wave : IntegerWavevector =>
      ‖fixedWaveSpaceTimeRestriction
        requestedTime wave state‖ ^ 2 :=
  (hasSum_fixedWaveSpaceTimeRestriction_norm_sq
    requestedTime state).summable

/-- Tsum form of the exact time-by-frequency Parseval identity. -/
theorem tsum_fixedWaveSpaceTimeRestriction_norm_sq
    (requestedTime : ℝ)
    (state : SpaceTimeState requestedTime) :
    (∑' wave : IntegerWavevector,
        ‖fixedWaveSpaceTimeRestriction
          requestedTime wave state‖ ^ 2) =
      ‖state‖ ^ 2 :=
  (hasSum_fixedWaveSpaceTimeRestriction_norm_sq
    requestedTime state).tsum_eq

end

end ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
end NavierStokes
end SaturationMonoid

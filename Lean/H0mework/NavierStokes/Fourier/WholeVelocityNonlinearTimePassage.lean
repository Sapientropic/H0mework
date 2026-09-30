import H0mework.NavierStokes.Fourier.FixedOutputNonlinearTimeContinuity
import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow

/-!
# Strong velocity convergence pays the nonlinear time row

The whole-velocity fixed-output row is locally Lipschitz on `ℓ²`.  Time
Cauchy--Schwarz upgrades that pointwise law to the exact bilinear mapping

`L²_t(ℓ²) × L²_t(ℓ²) → L¹_t(ℂ³)`.

This is the nonlinear passage consumed by the velocity Galerkin compactness
producer.  It contains no critical enstrophy, cutoff, target solution, or
compactness witness.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeVelocityNonlinearTimePassage

open scoped ENNReal Topology Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearTimeContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow

noncomputable section

theorem wholeStateVelocityNonlinearCoefficientAt_comp_continuousOn
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (a b : ℝ)
    (trajectoryContinuous : ContinuousOn trajectory (Icc a b))
    (trajectoryTransverse :
      ∀ t ∈ Icc a b, WholeStateTransverse (trajectory t)) :
    ContinuousOn
      (fun t =>
        wholeStateVelocityNonlinearCoefficientAt
          (trajectory t) output)
      (Icc a b) := by
  rw [continuousOn_iff_continuous_restrict]
  rw [continuous_iff_continuousAt]
  intro time
  exact
    tendsto_wholeStateVelocityNonlinearCoefficientAt
      (fun later : Icc a b => trajectory later.1)
      (trajectory time.1)
      (fun later => trajectoryTransverse later.1 later.2)
      (trajectoryTransverse time.1 time.2)
      trajectoryContinuous.restrict.continuousAt
      output

/-- Every fixed infinite velocity-convection row is locally Lipschitz from
the whole transverse `L²_t(ℓ²)` carrier to `L¹_t`. -/
theorem
    wholeStateVelocityNonlinearCoefficientAt_sub_norm_intervalIntegral_le
    (left right : ℝ → ComplexVorticityHilbertState)
    (output : IntegerWavevector)
    (a b : ℝ)
    (hab : a ≤ b)
    (leftContinuous : ContinuousOn left (Icc a b))
    (rightContinuous : ContinuousOn right (Icc a b))
    (leftTransverse :
      ∀ t ∈ Icc a b, WholeStateTransverse (left t))
    (rightTransverse :
      ∀ t ∈ Icc a b, WholeStateTransverse (right t)) :
    (∫ t in a..b,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (left t) output -
            wholeStateVelocityNonlinearCoefficientAt
              (right t) output‖) ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt (∫ t in a..b, ‖left t - right t‖ ^ 2) *
        (Real.sqrt (∫ t in a..b, ‖left t‖ ^ 2) +
          Real.sqrt (∫ t in a..b, ‖right t‖ ^ 2)) := by
  let angular : ℝ :=
    (6 * Real.pi) * Real.sqrt (integerWaveNormSq output)
  let differenceAmplitude : ℝ → ℝ :=
    fun t => ‖left t - right t‖
  let leftAmplitude : ℝ → ℝ := fun t => ‖left t‖
  let rightAmplitude : ℝ → ℝ := fun t => ‖right t‖
  have differenceContinuous :
      ContinuousOn differenceAmplitude (Icc a b) :=
    (leftContinuous.sub rightContinuous).norm
  have leftAmplitudeContinuous :
      ContinuousOn leftAmplitude (Icc a b) := leftContinuous.norm
  have rightAmplitudeContinuous :
      ContinuousOn rightAmplitude (Icc a b) := rightContinuous.norm
  have leftNonlinearContinuous :=
    wholeStateVelocityNonlinearCoefficientAt_comp_continuousOn
      left output a b leftContinuous leftTransverse
  have rightNonlinearContinuous :=
    wholeStateVelocityNonlinearCoefficientAt_comp_continuousOn
      right output a b rightContinuous rightTransverse
  have nonlinearDifferenceNormContinuous :
      ContinuousOn
        (fun t =>
          ‖wholeStateVelocityNonlinearCoefficientAt
                (left t) output -
              wholeStateVelocityNonlinearCoefficientAt
                (right t) output‖)
        (Icc a b) :=
    (leftNonlinearContinuous.sub rightNonlinearContinuous).norm
  have pointwise :
      ∀ t ∈ Icc a b,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (left t) output -
            wholeStateVelocityNonlinearCoefficientAt
              (right t) output‖ ≤
          angular *
            (differenceAmplitude t * leftAmplitude t +
              differenceAmplitude t * rightAmplitude t) := by
    intro t timeMem
    have base :=
      wholeStateVelocityNonlinearCoefficientAt_sub_norm_le
        (left t) (right t)
        (leftTransverse t timeMem)
        (rightTransverse t timeMem) output
    simpa [angular, differenceAmplitude, leftAmplitude,
      rightAmplitude, mul_add, mul_assoc] using base
  have nonlinearIntegrable :
      IntervalIntegrable
        (fun t =>
          ‖wholeStateVelocityNonlinearCoefficientAt
                (left t) output -
              wholeStateVelocityNonlinearCoefficientAt
                (right t) output‖)
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc
      hab nonlinearDifferenceNormContinuous
  have differenceLeftIntegrable :
      IntervalIntegrable
        (fun t => differenceAmplitude t * leftAmplitude t)
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (differenceContinuous.mul leftAmplitudeContinuous)
  have differenceRightIntegrable :
      IntervalIntegrable
        (fun t => differenceAmplitude t * rightAmplitude t)
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (differenceContinuous.mul rightAmplitudeContinuous)
  have majorantIntegrable :
      IntervalIntegrable
        (fun t =>
          angular *
            (differenceAmplitude t * leftAmplitude t +
              differenceAmplitude t * rightAmplitude t))
        volume a b :=
    (differenceLeftIntegrable.add differenceRightIntegrable).const_mul
      angular
  have integratedPointwise :
      (∫ t in a..b,
          ‖wholeStateVelocityNonlinearCoefficientAt
                (left t) output -
              wholeStateVelocityNonlinearCoefficientAt
                (right t) output‖) ≤
        ∫ t in a..b,
          angular *
            (differenceAmplitude t * leftAmplitude t +
              differenceAmplitude t * rightAmplitude t) :=
    intervalIntegral.integral_mono_on
      hab nonlinearIntegrable majorantIntegrable pointwise
  have differenceLeftCauchy :
      (∫ t in a..b,
          differenceAmplitude t * leftAmplitude t) ≤
        Real.sqrt
            (∫ t in a..b, differenceAmplitude t ^ 2) *
          Real.sqrt
            (∫ t in a..b, leftAmplitude t ^ 2) :=
    intervalIntegral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq
      differenceAmplitude leftAmplitude a b hab
      differenceContinuous leftAmplitudeContinuous
      (fun _t _timeMem => norm_nonneg _)
      (fun _t _timeMem => norm_nonneg _)
  have differenceRightCauchy :
      (∫ t in a..b,
          differenceAmplitude t * rightAmplitude t) ≤
        Real.sqrt
            (∫ t in a..b, differenceAmplitude t ^ 2) *
          Real.sqrt
            (∫ t in a..b, rightAmplitude t ^ 2) :=
    intervalIntegral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq
      differenceAmplitude rightAmplitude a b hab
      differenceContinuous rightAmplitudeContinuous
      (fun _t _timeMem => norm_nonneg _)
      (fun _t _timeMem => norm_nonneg _)
  have angularNonneg : 0 ≤ angular := by
    dsimp [angular]
    positivity
  calc
    (∫ t in a..b,
        ‖wholeStateVelocityNonlinearCoefficientAt
              (left t) output -
            wholeStateVelocityNonlinearCoefficientAt
              (right t) output‖) ≤
      ∫ t in a..b,
        angular *
          (differenceAmplitude t * leftAmplitude t +
            differenceAmplitude t * rightAmplitude t) :=
      integratedPointwise
    _ = angular *
        ((∫ t in a..b,
            differenceAmplitude t * leftAmplitude t) +
          ∫ t in a..b,
            differenceAmplitude t * rightAmplitude t) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          differenceLeftIntegrable differenceRightIntegrable]
    _ ≤ angular *
        (Real.sqrt
              (∫ t in a..b, differenceAmplitude t ^ 2) *
            Real.sqrt
              (∫ t in a..b, leftAmplitude t ^ 2) +
          Real.sqrt
              (∫ t in a..b, differenceAmplitude t ^ 2) *
            Real.sqrt
              (∫ t in a..b, rightAmplitude t ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add differenceLeftCauchy differenceRightCauchy)
        angularNonneg
    _ =
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        Real.sqrt (∫ t in a..b, ‖left t - right t‖ ^ 2) *
        (Real.sqrt (∫ t in a..b, ‖left t‖ ^ 2) +
          Real.sqrt (∫ t in a..b, ‖right t‖ ^ 2)) := by
      dsimp [angular, differenceAmplitude,
        leftAmplitude, rightAmplitude]
      ring

end

end ThreeDimensionalVorticityCoefficientWholeVelocityNonlinearTimePassage
end NavierStokes
end SaturationMonoid

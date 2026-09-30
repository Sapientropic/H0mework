import H0mework.NavierStokes.Crossing.PairOccurrenceGluing
import H0mework.NavierStokes.PairRestart.PairDuhamelExactHeadroom
import H0mework.NavierStokes.Crossing.TangentPaymentCascade

/-!
# Visible square ledger after crossing pair formation

At finite accumulated physical time every actual whole-restart contact is a
source-generated half-critical crossing.  The receipt-wide pair compiler
therefore splits the visible nonlinear output, before aggregation, into the
primitive source-self table and the complete outgoing gluing table.

This module charges the exact causal visible square to those two generated
responsibilities.  It does not assign a square norm to the aggregation kernel:
kernel components retain their existing componentwise native redirect.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger

open scoped BigOperators ENNReal Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing

noncomputable section

/-! ## Visible readouts of the two pre-quotient tables -/

/-- Visible aggregation of the primitive source-self pair occurrences. -/
def wholeRestartCrossingSourceSelfPairAggregate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  ∑' first : IntegerWavevector,
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
      initial index crossed output first

/-- Visible aggregation of the complete outgoing gluing occurrences at one
time of the same actual receipt. -/
def wholeRestartCrossingCompleteOutgoingPairGluingAggregate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ComplexCoordinateVector :=
  ∑' first : IntegerWavevector,
    wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
      initial index crossed output first time

theorem wholeRestartCrossingSourceSelfPairAggregate_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingSourceSelfPairAggregate
        initial index crossed output =
      wholeRestartCrossingFiniteComponentSelfRow
        initial index crossed output := by
  exact
    tsum_wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq
      initial index crossed output

theorem wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartCrossingCompleteOutgoingPairGluingAggregate
        initial index crossed output time =
      wholeStateVorticityNonlinearCoefficientAt
          ((run initial index).nextContact.prefixReceipt.wholePath time)
          output -
        wholeRestartCrossingSourceSelfPairAggregate
          initial index crossed output := by
  rw [wholeRestartCrossingCompleteOutgoingPairGluingAggregate,
    tsum_wholeRestartCrossingCompleteOutgoingPairGluingOccurrence_eq,
    wholeRestartCrossingSourceSelfPairAggregate_eq]

theorem wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartCrossingCompleteOutgoingPairGluingAggregate
        initial index crossed output time =
      actualWholeContinuousNonlinearRow
          (run initial index).nextContact.prefixReceipt output time.1 -
        wholeRestartCrossingSourceSelfPairAggregate
          initial index crossed output := by
  rw [wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq]
  have aggregateEq :=
    tsum_actualWholeContinuousPairVector_eq_continuousNonlinearRow
      (run initial index).nextContact.prefixReceipt output time
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput] at aggregateEq
  rw [aggregateEq]

/-- The actual visible pair aggregation is the source-self aggregation plus
the complete outgoing gluing aggregation at every time of the receipt. -/
theorem actualPairAggregate_eq_crossingSourceSelf_add_completeGluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    (∑' first : IntegerWavevector,
      actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time) =
      wholeRestartCrossingSourceSelfPairAggregate
          initial index crossed output +
        wholeRestartCrossingCompleteOutgoingPairGluingAggregate
          initial index crossed output time := by
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput,
    wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq]
  abel

/-! ## Exact causal square rows -/

/-- Exact causal fraction of the constant primitive source-self aggregation
on the actual receipt window. -/
def wholeRestartCrossingSourceSelfVisibleSquareRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ℝ :=
  wholeRestartExactCausalVisibleFraction initial index output *
    ∫ _time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      ‖wholeRestartCrossingSourceSelfPairAggregate
          initial index crossed output‖ ^ 2
      ∂(commonTimeMeasure (run initial index).nextContact.time.1)

/-- Exact causal fraction of the complete outgoing gluing aggregation on the
same actual receipt window. -/
def wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) : ℝ :=
  wholeRestartExactCausalVisibleFraction initial index output *
    ∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
          initial index crossed output time‖ ^ 2
      ∂(commonTimeMeasure (run initial index).nextContact.time.1)

theorem wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    0 ≤ wholeRestartCrossingSourceSelfVisibleSquareRow
      initial index crossed output := by
  exact mul_nonneg
    (wholeRestartExactCausalVisibleFraction_nonneg initial index output)
    (integral_nonneg fun _time => sq_nonneg _)

theorem wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    0 ≤ wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
      initial index crossed output := by
  exact mul_nonneg
    (wholeRestartExactCausalVisibleFraction_nonneg initial index output)
    (integral_nonneg fun _time => sq_nonneg _)

/-! ## Exact source-self heat settlement -/

/-- The primitive source-self visible row is exactly the heat headroom of
the same actual receipt applied to the physical `H⁻¹` component row.  No
uniform rate floor, frequency cutoff or quotient coercivity is used. -/
theorem
    wholeRestartCrossingSourceSelfVisibleSquareRow_eq_spectralHeatNegativeOneRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed output =
      ((2 * ν.coeff)⁻¹ *
        (1 - Real.exp
          (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1))) *
        ‖wholeRestartCrossingFiniteComponentSelfNegativeOneState
            initial index crossed output‖ ^ 2 := by
  by_cases outputNonzero : output ≠ 0
  · have multiplierPos :
        0 < integerWaveViscousMultiplier output := by
      unfold integerWaveViscousMultiplier
      exact mul_pos
        (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
        (integerWaveNormSq_pos outputNonzero)
    have sqrtPos :
        0 < Real.sqrt (integerWaveViscousMultiplier output) :=
      Real.sqrt_pos.2 multiplierPos
    have durationPos :
        0 < (run initial index).nextContact.time.1 :=
      (run initial index).nextContact.time_pos
    have constantIntegral :
        (∫ _time :
            Icc (0 : ℝ) (run initial index).nextContact.time.1,
            ‖wholeRestartCrossingSourceSelfPairAggregate
                initial index crossed output‖ ^ 2
          ∂(commonTimeMeasure
            (run initial index).nextContact.time.1)) =
          (run initial index).nextContact.time.1 *
            ‖wholeRestartCrossingSourceSelfPairAggregate
                initial index crossed output‖ ^ 2 := by
      calc
        (∫ _time :
            Icc (0 : ℝ) (run initial index).nextContact.time.1,
            ‖wholeRestartCrossingSourceSelfPairAggregate
                initial index crossed output‖ ^ 2
          ∂(commonTimeMeasure
            (run initial index).nextContact.time.1)) =
            ∫ _time in (0 : ℝ)..(run initial index).nextContact.time.1,
              ‖wholeRestartCrossingSourceSelfPairAggregate
                  initial index crossed output‖ ^ 2 := by
          exact commonTime_integral_eq_intervalIntegral
            (run initial index).nextContact.time.1 durationPos.le
            (fun _ : ℝ =>
              ‖wholeRestartCrossingSourceSelfPairAggregate
                  initial index crossed output‖ ^ 2)
        _ = (run initial index).nextContact.time.1 *
              ‖wholeRestartCrossingSourceSelfPairAggregate
                  initial index crossed output‖ ^ 2 := by
          simp [intervalIntegral.integral_const, smul_eq_mul]
    have negativeOneNormSq :
        ‖wholeRestartCrossingFiniteComponentSelfNegativeOneState
            initial index crossed output‖ ^ 2 =
          ‖wholeRestartCrossingSourceSelfPairAggregate
              initial index crossed output‖ ^ 2 /
            integerWaveViscousMultiplier output := by
      rw [wholeRestartCrossingFiniteComponentSelfNegativeOneState_apply,
        if_neg outputNonzero,
        wholeRestartCrossingSourceSelfPairAggregate_eq
          initial index crossed output,
        norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
      field_simp [sqrtPos.ne', multiplierPos.ne']
      rw [Real.sq_sqrt multiplierPos.le]
      ring
    unfold wholeRestartCrossingSourceSelfVisibleSquareRow
    rw [constantIntegral,
      wholeRestartExactCausalVisibleFraction_eq
        initial index output outputNonzero,
      negativeOneNormSq]
    field_simp [ν.coeff_pos.ne', multiplierPos.ne', durationPos.ne']
  · have outputZero : output = 0 := not_ne_iff.mp outputNonzero
    subst output
    simp [wholeRestartCrossingSourceSelfVisibleSquareRow,
      wholeRestartExactCausalVisibleFraction,
      wholeRestartExactCausalRateHeadroom,
      integerWaveViscousMultiplier]

theorem norm_add_sq_le_two_mul
    {E : Type*} [NormedAddCommGroup E]
    (left right : E) :
    ‖left + right‖ ^ 2 ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have normLe := norm_add_le left right
  have squareLe :
      ‖left + right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  calc
    ‖left + right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 := squareLe
    _ ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
      nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

theorem integrable_actualPairAggregateNormSq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    Integrable
      (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        ‖∑' first : IntegerWavevector,
          actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time‖ ^ 2)
      (commonTimeMeasure (run initial index).nextContact.time.1) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  have continuousNormSq :
      Continuous
        (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          ‖actualWholeContinuousNonlinearRow receipt output time.1‖ ^ 2) :=
    (((actualWholeContinuousNonlinearRow_continuous receipt output).comp
      continuous_subtype_val).norm.pow 2)
  have integrableContinuous :
      Integrable
        (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          ‖actualWholeContinuousNonlinearRow receipt output time.1‖ ^ 2)
        (commonTimeMeasure (run initial index).nextContact.time.1) := by
    simpa using
      (ContinuousOn.integrableOn_compact isCompact_univ
        continuousNormSq.continuousOn)
  exact integrableContinuous.congr
    (Filter.Eventually.of_forall fun time => by
      exact congrArg (fun value : ComplexCoordinateVector => ‖value‖ ^ 2)
        (tsum_actualWholeContinuousPairVector_eq_continuousNonlinearRow
          receipt output time).symm)

theorem integrable_sourceSelfAggregateNormSq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    Integrable
      (fun _time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        ‖wholeRestartCrossingSourceSelfPairAggregate
          initial index crossed output‖ ^ 2)
      (commonTimeMeasure (run initial index).nextContact.time.1) := by
  have continuousNormSq :
      Continuous
        (fun _time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          ‖wholeRestartCrossingSourceSelfPairAggregate
            initial index crossed output‖ ^ 2) :=
    continuous_const
  simp

theorem integrable_completeOutgoingGluingAggregateNormSq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    Integrable
      (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
          initial index crossed output time‖ ^ 2)
      (commonTimeMeasure (run initial index).nextContact.time.1) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let source :=
    wholeRestartCrossingSourceSelfPairAggregate
      initial index crossed output
  have continuousNormSq :
      Continuous
        (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          ‖actualWholeContinuousNonlinearRow receipt output time.1 -
              source‖ ^ 2) :=
    (((((actualWholeContinuousNonlinearRow_continuous receipt output).comp
      continuous_subtype_val).sub continuous_const).norm).pow 2)
  have integrableContinuous :
      Integrable
        (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          ‖actualWholeContinuousNonlinearRow receipt output time.1 -
              source‖ ^ 2)
        (commonTimeMeasure (run initial index).nextContact.time.1) := by
    simpa using
      (ContinuousOn.integrableOn_compact isCompact_univ
        continuousNormSq.continuousOn)
  exact integrableContinuous.congr
    (Filter.Eventually.of_forall fun time => by
      exact congrArg (fun value : ComplexCoordinateVector => ‖value‖ ^ 2)
        (wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq_continuous
          initial index crossed output time).symm)

theorem norm_sub_sq_le_two_mul
    {E : Type*} [NormedAddCommGroup E]
    (left right : E) :
    ‖left - right‖ ^ 2 ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  simpa [sub_eq_add_neg] using
    norm_add_sq_le_two_mul left (-right)

/-! ## Two-sided visible square settlement -/

theorem wholeRestartExactCausalNonlinearSquareRow_le_sourceSelf_add_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartExactCausalNonlinearSquareRow initial index output ≤
      2 * wholeRestartCrossingSourceSelfVisibleSquareRow
          initial index crossed output +
        2 * wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
          initial index crossed output := by
  by_cases outputNonzero : output ≠ 0
  · rw [wholeRestartExactCausalNonlinearSquareRow_eq_visiblePairIntegral
      initial index output outputNonzero]
    unfold wholeRestartCrossingSourceSelfVisibleSquareRow
      wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
    have actualIntegrable :=
      integrable_actualPairAggregateNormSq initial index output
    have sourceIntegrable :=
      integrable_sourceSelfAggregateNormSq
        initial index crossed output
    have gluingIntegrable :=
      integrable_completeOutgoingGluingAggregateNormSq
        initial index crossed output
    have majorantIntegrable :
        Integrable
          (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
            2 * ‖wholeRestartCrossingSourceSelfPairAggregate
                    initial index crossed output‖ ^ 2 +
              2 * ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                    initial index crossed output time‖ ^ 2)
          (commonTimeMeasure (run initial index).nextContact.time.1) :=
      (sourceIntegrable.const_mul 2).add
        (gluingIntegrable.const_mul 2)
    have integralLe :
        (∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            ‖∑' first : IntegerWavevector,
              actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output first time‖ ^ 2
            ∂(commonTimeMeasure (run initial index).nextContact.time.1)) ≤
          ∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            (2 * ‖wholeRestartCrossingSourceSelfPairAggregate
                    initial index crossed output‖ ^ 2 +
              2 * ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                    initial index crossed output time‖ ^ 2)
            ∂(commonTimeMeasure (run initial index).nextContact.time.1) := by
      exact integral_mono_ae actualIntegrable majorantIntegrable
        (Filter.Eventually.of_forall fun time => by
          change
            ‖∑' first : IntegerWavevector,
              actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output first time‖ ^ 2 ≤ _
          rw [actualPairAggregate_eq_crossingSourceSelf_add_completeGluing
            initial index crossed output time]
          exact norm_add_sq_le_two_mul _ _)
    have weightedLe := mul_le_mul_of_nonneg_left integralLe
      (wholeRestartExactCausalVisibleFraction_nonneg
        initial index output)
    rw [integral_add
        (sourceIntegrable.const_mul 2)
        (gluingIntegrable.const_mul 2),
      integral_const_mul, integral_const_mul] at weightedLe
    nlinarith
  · have outputZero : output = 0 := not_ne_iff.mp outputNonzero
    subst output
    calc
      wholeRestartExactCausalNonlinearSquareRow initial index 0 = 0 := by
        simp [wholeRestartExactCausalNonlinearSquareRow,
          wholeRestartExactCausalRateHeadroom,
          integerWaveViscousMultiplier]
      _ ≤ _ := add_nonneg
        (mul_nonneg (by norm_num)
          (wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
            initial index crossed 0))
        (mul_nonneg (by norm_num)
          (wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_nonneg
            initial index crossed 0))

/-- The primitive source-self square cannot disappear into pair aggregation.
On the same actual receipt it is paid, with the exact causal fraction, by
the visible actual row or by the complete outgoing gluing row. -/
theorem wholeRestartCrossingSourceSelfVisibleSquareRow_le_actual_add_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed output ≤
      2 * wholeRestartExactCausalNonlinearSquareRow
          initial index output +
        2 * wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
          initial index crossed output := by
  by_cases outputNonzero : output ≠ 0
  · rw [wholeRestartExactCausalNonlinearSquareRow_eq_visiblePairIntegral
      initial index output outputNonzero]
    unfold wholeRestartCrossingSourceSelfVisibleSquareRow
      wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
    have actualIntegrable :=
      integrable_actualPairAggregateNormSq initial index output
    have sourceIntegrable :=
      integrable_sourceSelfAggregateNormSq
        initial index crossed output
    have gluingIntegrable :=
      integrable_completeOutgoingGluingAggregateNormSq
        initial index crossed output
    have majorantIntegrable :
        Integrable
          (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
            2 * ‖∑' first : IntegerWavevector,
                    actualWholeContinuousPairVector
                      (run initial index).nextContact.prefixReceipt
                      output first time‖ ^ 2 +
              2 * ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                    initial index crossed output time‖ ^ 2)
          (commonTimeMeasure (run initial index).nextContact.time.1) :=
      (actualIntegrable.const_mul 2).add
        (gluingIntegrable.const_mul 2)
    have integralLe :
        (∫ _time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            ‖wholeRestartCrossingSourceSelfPairAggregate
                initial index crossed output‖ ^ 2
            ∂(commonTimeMeasure (run initial index).nextContact.time.1)) ≤
          ∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            (2 * ‖∑' first : IntegerWavevector,
                    actualWholeContinuousPairVector
                      (run initial index).nextContact.prefixReceipt
                      output first time‖ ^ 2 +
              2 * ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                    initial index crossed output time‖ ^ 2)
            ∂(commonTimeMeasure (run initial index).nextContact.time.1) := by
      exact integral_mono_ae sourceIntegrable majorantIntegrable
        (Filter.Eventually.of_forall fun time => by
          let actual :=
            ∑' first : IntegerWavevector,
              actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output first time
          let source :=
            wholeRestartCrossingSourceSelfPairAggregate
              initial index crossed output
          let gluing :=
            wholeRestartCrossingCompleteOutgoingPairGluingAggregate
              initial index crossed output time
          have actualEq : actual = source + gluing := by
            simpa [actual, source, gluing] using
              actualPairAggregate_eq_crossingSourceSelf_add_completeGluing
                initial index crossed output time
          have sourceEq : source = actual - gluing := by
            rw [actualEq]
            abel
          change ‖source‖ ^ 2 ≤
            2 * ‖actual‖ ^ 2 + 2 * ‖gluing‖ ^ 2
          rw [sourceEq]
          exact norm_sub_sq_le_two_mul actual gluing)
    have weightedLe := mul_le_mul_of_nonneg_left integralLe
      (wholeRestartExactCausalVisibleFraction_nonneg
        initial index output)
    rw [integral_add
        (actualIntegrable.const_mul 2)
        (gluingIntegrable.const_mul 2),
      integral_const_mul, integral_const_mul] at weightedLe
    nlinarith
  · have outputZero : output = 0 := not_ne_iff.mp outputNonzero
    subst output
    calc
      wholeRestartCrossingSourceSelfVisibleSquareRow
          initial index crossed 0 = 0 := by
        simp [wholeRestartCrossingSourceSelfVisibleSquareRow,
          wholeRestartExactCausalVisibleFraction,
          wholeRestartExactCausalRateHeadroom,
          integerWaveViscousMultiplier]
      _ ≤ _ := add_nonneg
        (mul_nonneg (by norm_num)
          (wholeRestartExactCausalNonlinearSquareRow_nonneg
            initial index 0))
        (mul_nonneg (by norm_num)
          (wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_nonneg
            initial index crossed 0))

/-- A positive primitive row forces a source-determined fixed fraction into
the actual visible row or the complete outgoing gluing row.  The fraction is
derived from the same-receipt square inequality, not supplied as a cutoff. -/
theorem
    wholeRestartCrossingSourceSelfVisibleSquareRow_quarter_le_actual_or_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingSourceSelfVisibleSquareRow
          initial index crossed output / 4 ≤
        wholeRestartExactCausalNonlinearSquareRow
          initial index output ∨
      wholeRestartCrossingSourceSelfVisibleSquareRow
            initial index crossed output / 4 ≤
        wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
          initial index crossed output := by
  by_cases actualLarge :
      wholeRestartCrossingSourceSelfVisibleSquareRow
            initial index crossed output / 4 ≤
        wholeRestartExactCausalNonlinearSquareRow
          initial index output
  · exact Or.inl actualLarge
  · right
    have actualSmall :
        wholeRestartExactCausalNonlinearSquareRow
            initial index output <
          wholeRestartCrossingSourceSelfVisibleSquareRow
              initial index crossed output / 4 :=
      lt_of_not_ge actualLarge
    have sourceBound :=
      wholeRestartCrossingSourceSelfVisibleSquareRow_le_actual_add_gluing
        initial index crossed output
    nlinarith

theorem wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_le_actual_add_sourceSelf
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
        initial index crossed output ≤
      2 * wholeRestartExactCausalNonlinearSquareRow
          initial index output +
        2 * wholeRestartCrossingSourceSelfVisibleSquareRow
          initial index crossed output := by
  by_cases outputNonzero : output ≠ 0
  · rw [wholeRestartExactCausalNonlinearSquareRow_eq_visiblePairIntegral
      initial index output outputNonzero]
    unfold wholeRestartCrossingSourceSelfVisibleSquareRow
      wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
    have actualIntegrable :=
      integrable_actualPairAggregateNormSq initial index output
    have sourceIntegrable :=
      integrable_sourceSelfAggregateNormSq
        initial index crossed output
    have gluingIntegrable :=
      integrable_completeOutgoingGluingAggregateNormSq
        initial index crossed output
    have majorantIntegrable :
        Integrable
          (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
            2 * ‖∑' first : IntegerWavevector,
                    actualWholeContinuousPairVector
                      (run initial index).nextContact.prefixReceipt
                      output first time‖ ^ 2 +
              2 * ‖wholeRestartCrossingSourceSelfPairAggregate
                    initial index crossed output‖ ^ 2)
          (commonTimeMeasure (run initial index).nextContact.time.1) :=
      (actualIntegrable.const_mul 2).add
        (sourceIntegrable.const_mul 2)
    have integralLe :
        (∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                initial index crossed output time‖ ^ 2
            ∂(commonTimeMeasure (run initial index).nextContact.time.1)) ≤
          ∫ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
            (2 * ‖∑' first : IntegerWavevector,
                    actualWholeContinuousPairVector
                      (run initial index).nextContact.prefixReceipt
                      output first time‖ ^ 2 +
              2 * ‖wholeRestartCrossingSourceSelfPairAggregate
                    initial index crossed output‖ ^ 2)
            ∂(commonTimeMeasure (run initial index).nextContact.time.1) := by
      exact integral_mono_ae gluingIntegrable majorantIntegrable
        (Filter.Eventually.of_forall fun time => by
          change
            ‖wholeRestartCrossingCompleteOutgoingPairGluingAggregate
                initial index crossed output time‖ ^ 2 ≤ _
          rw [wholeRestartCrossingCompleteOutgoingPairGluingAggregate_eq]
          rw [← tsum_actualWholeContinuousPairVector_eq_nonlinearOutput
            (run initial index).nextContact.prefixReceipt output time]
          exact norm_sub_sq_le_two_mul _ _)
    have weightedLe := mul_le_mul_of_nonneg_left integralLe
      (wholeRestartExactCausalVisibleFraction_nonneg
        initial index output)
    rw [integral_add
        (actualIntegrable.const_mul 2)
        (sourceIntegrable.const_mul 2),
      integral_const_mul, integral_const_mul] at weightedLe
    nlinarith
  · have outputZero : output = 0 := not_ne_iff.mp outputNonzero
    subst output
    calc
      wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
          initial index crossed 0 = 0 := by
        simp [wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow,
          wholeRestartExactCausalVisibleFraction,
          wholeRestartExactCausalRateHeadroom,
          integerWaveViscousMultiplier]
      _ ≤ _ := add_nonneg
        (mul_nonneg (by norm_num)
          (wholeRestartExactCausalNonlinearSquareRow_nonneg
            initial index 0))
        (mul_nonneg (by norm_num)
          (wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
            initial index crossed 0))

/-! ## Spatial summability and complete payments -/

theorem wholeRestartCrossingSourceSelfPairAggregate_eq_zero_of_not_mem
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed)) :
    wholeRestartCrossingSourceSelfPairAggregate
        initial index crossed output = 0 := by
  rw [wholeRestartCrossingSourceSelfPairAggregate_eq,
    wholeRestartCrossingFiniteComponentSelfRow_eq_nsmul]
  have componentZero :=
    wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_supported
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (canonicalHalfCriticalComponent ν
        (wholeRestartCrossingFiniteCoreState initial index crossed))
      (wholeRestartCrossingFiniteComponent_supported
        initial index crossed)
      output outputNotMem
  rw [componentZero]
  simp

theorem summable_wholeRestartCrossingSourceSelfVisibleSquareRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    Summable
      (wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed) := by
  apply summable_of_ne_finset_zero
    (s := finiteVorticityPairOutputSupport
      (wholeRestartCrossingFiniteCoreModes initial index crossed))
  intro output outputNotMem
  unfold wholeRestartCrossingSourceSelfVisibleSquareRow
  rw [wholeRestartCrossingSourceSelfPairAggregate_eq_zero_of_not_mem
    initial index crossed output outputNotMem]
  simp

theorem summable_wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    Summable
      (wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
        initial index crossed) := by
  have majorantSummable :
      Summable fun output : IntegerWavevector =>
        2 * wholeRestartExactCausalNonlinearSquareRow
              initial index output +
          2 * wholeRestartCrossingSourceSelfVisibleSquareRow
              initial index crossed output :=
    ((summable_wholeRestartExactCausalNonlinearSquareRow
      initial index).mul_left 2).add
      ((summable_wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed).mul_left 2)
  exact majorantSummable.of_nonneg_of_le
    (wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_nonneg
      initial index crossed)
    (wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_le_actual_add_sourceSelf
      initial index crossed)

/-- Complete primitive source-self visible payment of one crossing receipt. -/
def wholeRestartCrossingSourceSelfVisibleSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℝ :=
  ∑' output : IntegerWavevector,
    wholeRestartCrossingSourceSelfVisibleSquareRow
      initial index crossed output

/-- Complete outgoing gluing visible payment of one crossing receipt. -/
def wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℝ :=
  ∑' output : IntegerWavevector,
    wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
      initial index crossed output

/-- The complete source-self payment retains the exact heat factor of every
actual output row on the generated physical `H⁻¹` component state. -/
theorem
    wholeRestartCrossingSourceSelfVisibleSquarePayment_eq_spectralHeatNegativeOne
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingSourceSelfVisibleSquarePayment
        initial index crossed =
      ∑' output : IntegerWavevector,
        ((2 * ν.coeff)⁻¹ *
          (1 - Real.exp
            (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
              (run initial index).nextContact.time.1))) *
          ‖wholeRestartCrossingFiniteComponentSelfNegativeOneState
              initial index crossed output‖ ^ 2 := by
  unfold wholeRestartCrossingSourceSelfVisibleSquarePayment
  apply tsum_congr
  exact
    wholeRestartCrossingSourceSelfVisibleSquareRow_eq_spectralHeatNegativeOneRow
      initial index crossed

/-- Exact time/frequency headroom reduces the complete source-self stream to
the norm of its actual physical `H⁻¹` state.  This is an upper settlement,
not a post-quotient coercive lower bound. -/
theorem wholeRestartCrossingSourceSelfVisibleSquarePayment_le_negativeOneNormSq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingSourceSelfVisibleSquarePayment
        initial index crossed ≤
      (2 * ν.coeff)⁻¹ *
        ‖wholeRestartCrossingFiniteComponentSelfNegativeOneState
            initial index crossed‖ ^ 2 := by
  let sourceState :=
    wholeRestartCrossingFiniteComponentSelfNegativeOneState
      initial index crossed
  have sourceRowSummable :
      Summable fun output : IntegerWavevector =>
        ‖sourceState output‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) sourceState.2
  have inverseNonneg : 0 ≤ (2 * ν.coeff)⁻¹ :=
    inv_nonneg.mpr
      (mul_nonneg (by norm_num) ν.coeff_pos.le)
  have perOutput : ∀ output : IntegerWavevector,
      ((2 * ν.coeff)⁻¹ *
          (1 - Real.exp
            (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
              (run initial index).nextContact.time.1))) *
          ‖sourceState output‖ ^ 2 ≤
        (2 * ν.coeff)⁻¹ * ‖sourceState output‖ ^ 2 := by
    intro output
    have exponentialNonneg :
        0 ≤ Real.exp
          (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1) :=
      Real.exp_nonneg _
    have oneSubLe :
        1 - Real.exp
            (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
              (run initial index).nextContact.time.1) ≤ 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left oneSubLe inverseNonneg)
      (sq_nonneg _)
  have spectralSummable :
      Summable fun output : IntegerWavevector =>
        ((2 * ν.coeff)⁻¹ *
          (1 - Real.exp
            (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
              (run initial index).nextContact.time.1))) *
          ‖sourceState output‖ ^ 2 := by
    simpa only [sourceState,
      ← wholeRestartCrossingSourceSelfVisibleSquareRow_eq_spectralHeatNegativeOneRow
        initial index crossed] using
      summable_wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed
  have summed := Summable.tsum_le_tsum perOutput spectralSummable
    (sourceRowSummable.mul_left (2 * ν.coeff)⁻¹)
  rw [wholeRestartCrossingSourceSelfVisibleSquarePayment_eq_spectralHeatNegativeOne]
  change
    (∑' output : IntegerWavevector,
      ((2 * ν.coeff)⁻¹ *
        (1 - Real.exp
          (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1))) *
        ‖sourceState output‖ ^ 2) ≤ _
  calc
    (∑' output : IntegerWavevector,
      ((2 * ν.coeff)⁻¹ *
        (1 - Real.exp
          (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1))) *
        ‖sourceState output‖ ^ 2) ≤
        ∑' output : IntegerWavevector,
          (2 * ν.coeff)⁻¹ * ‖sourceState output‖ ^ 2 := summed
    _ = (2 * ν.coeff)⁻¹ *
          ∑' output : IntegerWavevector, ‖sourceState output‖ ^ 2 := by
      rw [tsum_mul_left]
    _ = (2 * ν.coeff)⁻¹ * ‖sourceState‖ ^ 2 := by
      congr 1
      symm
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num) sourceState)

theorem wholeRestartCrossingSourceSelfVisibleSquarePayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 ≤ wholeRestartCrossingSourceSelfVisibleSquarePayment
      initial index crossed :=
  tsum_nonneg fun output =>
    wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
      initial index crossed output

/-- A nonzero primitive source-self `H⁻¹` state generates strictly positive
visible pair-square payment on the same actual receipt.  The output row and
its heat factor are selected internally. -/
theorem
    wholeRestartCrossingSourceSelfVisibleSquare_generates_positive_outputRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (sourceNonzero :
      wholeRestartCrossingFiniteComponentSelfNegativeOneState
        initial index crossed ≠ 0) :
    ∃ output : IntegerWavevector,
      output ≠ 0 ∧
        wholeRestartCrossingFiniteComponentSelfNegativeOneState
            initial index crossed output ≠ 0 ∧
        0 <
          wholeRestartCrossingSourceSelfVisibleSquareRow
            initial index crossed output := by
  let sourceState :=
    wholeRestartCrossingFiniteComponentSelfNegativeOneState
      initial index crossed
  have existsOutput :
      ∃ output : IntegerWavevector, sourceState output ≠ 0 := by
    by_contra noOutput
    push Not at noOutput
    apply sourceNonzero
    apply lp.ext
    funext output
    exact noOutput output
  obtain ⟨output, outputStateNonzero⟩ := existsOutput
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    apply outputStateNonzero
    simp [sourceState,
      wholeRestartCrossingFiniteComponentSelfNegativeOneState_apply]
  have multiplierPos :
      0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNonzero⟩
  have exponentNeg :
      -(2 * ν.coeff * integerWaveViscousMultiplier output) *
          (run initial index).nextContact.time.1 < 0 := by
    exact mul_neg_of_neg_of_pos
      (neg_neg_of_pos
        (mul_pos (mul_pos (by norm_num) ν.coeff_pos) multiplierPos))
      (run initial index).nextContact.time_pos
  have heatFactorPos :
      0 <
        1 - Real.exp
          (-(2 * ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1) := by
    exact sub_pos.mpr
      (Real.exp_lt_one_iff.mpr exponentNeg)
  have inversePos : 0 < (2 * ν.coeff)⁻¹ :=
    inv_pos.mpr (mul_pos (by norm_num) ν.coeff_pos)
  have sourceNormSqPos : 0 < ‖sourceState output‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr outputStateNonzero)
  have rowPos :
      0 <
        wholeRestartCrossingSourceSelfVisibleSquareRow
          initial index crossed output := by
    rw [
      wholeRestartCrossingSourceSelfVisibleSquareRow_eq_spectralHeatNegativeOneRow]
    exact mul_pos (mul_pos inversePos heatFactorPos) sourceNormSqPos
  exact ⟨output, outputNonzero, outputStateNonzero, rowPos⟩

/-- The generated positive output row is retained by the complete
source-self visible payment. -/
theorem
    wholeRestartCrossingSourceSelfVisibleSquarePayment_pos_of_negativeOneState_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (sourceNonzero :
      wholeRestartCrossingFiniteComponentSelfNegativeOneState
        initial index crossed ≠ 0) :
    0 <
      wholeRestartCrossingSourceSelfVisibleSquarePayment
        initial index crossed := by
  obtain ⟨output, _outputNonzero, _outputStateNonzero, rowPos⟩ :=
    wholeRestartCrossingSourceSelfVisibleSquare_generates_positive_outputRow
      initial index crossed sourceNonzero
  have rowLePayment :
      wholeRestartCrossingSourceSelfVisibleSquareRow
            initial index crossed output ≤
        wholeRestartCrossingSourceSelfVisibleSquarePayment
          initial index crossed := by
    unfold wholeRestartCrossingSourceSelfVisibleSquarePayment
    exact
      (summable_wholeRestartCrossingSourceSelfVisibleSquareRow
        initial index crossed).le_tsum output
          (fun other _otherNe =>
            wholeRestartCrossingSourceSelfVisibleSquareRow_nonneg
              initial index crossed other)
  exact rowPos.trans_le rowLePayment

theorem wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 ≤ wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment
      initial index crossed :=
  tsum_nonneg fun output =>
    wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow_nonneg
      initial index crossed output

/-- The generated component count converts the exact source-self heat
payment into the finite core's physical viscous-gradient rate. -/
theorem
    wholeRestartCrossing_componentCount_mul_sourceSelfVisibleSquarePayment_le_gradient
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (canonicalHalfCriticalComponentCount ν
        (wholeRestartCrossingFiniteCoreState
          initial index crossed) : ℝ) *
        wholeRestartCrossingSourceSelfVisibleSquarePayment
          initial index crossed ≤
      ν.coeff * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass
          (wholeRestartCrossingFiniteCoreState initial index crossed) := by
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let count := canonicalHalfCriticalComponentCount ν core
  let sourceState :=
    wholeRestartCrossingFiniteComponentSelfNegativeOneState
      initial index crossed
  have countNonneg : 0 ≤ (count : ℝ) := by positivity
  have inverseNonneg : 0 ≤ (2 * ν.coeff)⁻¹ :=
    inv_nonneg.mpr
      (mul_nonneg (by norm_num) ν.coeff_pos.le)
  have paymentBound :=
    wholeRestartCrossingSourceSelfVisibleSquarePayment_le_negativeOneNormSq
      initial index crossed
  have sourceBound :=
    wholeRestartCrossingFiniteComponentSelfNegativeOneState_count_mul_norm_sq_le_component_ceiling
      initial index crossed
  calc
    (count : ℝ) *
          wholeRestartCrossingSourceSelfVisibleSquarePayment
            initial index crossed ≤
        (count : ℝ) * ((2 * ν.coeff)⁻¹ * ‖sourceState‖ ^ 2) :=
      mul_le_mul_of_nonneg_left paymentBound countNonneg
    _ = (2 * ν.coeff)⁻¹ * ((count : ℝ) * ‖sourceState‖ ^ 2) := by
      ring
    _ ≤ (2 * ν.coeff)⁻¹ *
          (4 * criticalEnstrophyLatticeConstant *
            wholeStateVorticityGradientMass core *
            wholeRestartHalfCriticalCoefficientCeiling ν) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [count, core, sourceState] using sourceBound)
        inverseNonneg
    _ = ν.coeff * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass core := by
      unfold wholeRestartHalfCriticalCoefficientCeiling
      field_simp [ν.coeff_pos.ne',
        criticalEnstrophyLatticeConstant_pos.ne']
      ring

/-- Dividing only by the source-generated positive component count gives the
sharp scalar rate that remains to be accumulated along crossing contacts. -/
theorem wholeRestartCrossingSourceSelfVisibleSquarePayment_le_gradient_div_count
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingSourceSelfVisibleSquarePayment
        initial index crossed ≤
      (ν.coeff * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass
          (wholeRestartCrossingFiniteCoreState initial index crossed)) /
        (canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) : ℝ) := by
  have countPos :
      (0 : ℝ) <
        canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState
            initial index crossed) := by
    exact_mod_cast
      canonicalHalfCriticalComponentCount_pos ν
        (wholeRestartCrossingFiniteCoreState initial index crossed)
  apply (le_div_iff₀ countPos).2
  simpa only [mul_comm] using
    wholeRestartCrossing_componentCount_mul_sourceSelfVisibleSquarePayment_le_gradient
      initial index crossed

/-- The complete exact causal payment is charged once to the primitive
source-self visible image and once to the complete outgoing gluing image.
Kernel components are not charged by this inequality. -/
theorem wholeRestartExactCausalNonlinearSquarePayment_le_crossingSourceSelf_add_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartExactCausalNonlinearSquarePayment initial index ≤
      2 * wholeRestartCrossingSourceSelfVisibleSquarePayment
          initial index crossed +
        2 * wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment
          initial index crossed := by
  have leftSummable :=
    summable_wholeRestartExactCausalNonlinearSquareRow initial index
  have sourceSummable :=
    summable_wholeRestartCrossingSourceSelfVisibleSquareRow
      initial index crossed
  have gluingSummable :=
    summable_wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
      initial index crossed
  have rightSummable :
      Summable fun output : IntegerWavevector =>
        2 * wholeRestartCrossingSourceSelfVisibleSquareRow
              initial index crossed output +
          2 * wholeRestartCrossingCompleteOutgoingGluingVisibleSquareRow
              initial index crossed output :=
    (sourceSummable.mul_left 2).add (gluingSummable.mul_left 2)
  have summed := Summable.tsum_le_tsum
    (wholeRestartExactCausalNonlinearSquareRow_le_sourceSelf_add_gluing
      initial index crossed)
    leftSummable rightSummable
  unfold wholeRestartExactCausalNonlinearSquarePayment at summed ⊢
  unfold wholeRestartCrossingSourceSelfVisibleSquarePayment
    wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment at ⊢
  rw [Summable.tsum_add
      (sourceSummable.mul_left 2)
      (gluingSummable.mul_left 2),
    tsum_mul_left, tsum_mul_left] at summed
  exact summed

/-! ## Finite-time exhaustion on the generated crossing lineage -/

/-- Primitive source-self payment selected internally at every index of a
finite accumulated actual restart run. -/
def wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : ℝ :=
  wholeRestartCrossingSourceSelfVisibleSquarePayment
    initial index
      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index)

/-- Complete outgoing gluing payment selected internally at every index of a
finite accumulated actual restart run. -/
def wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : ℝ :=
  wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment
    initial index
      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index)

/-- Source-generated critical rate left after exact heat settlement and the
canonical reciprocal component-count gain. -/
def wholeRestartBoundedElapsedSourceCriticalGradientRate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : ℝ :=
  let crossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  (ν.coeff * (2 * Real.pi) ^ 2 *
      wholeStateVorticityGradientMass
        (wholeRestartCrossingFiniteCoreState initial index crossed)) /
    (canonicalHalfCriticalComponentCount ν
      (wholeRestartCrossingFiniteCoreState initial index crossed) : ℝ)

theorem wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    0 ≤ wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment
      initial elapsedBounded index :=
  wholeRestartCrossingSourceSelfVisibleSquarePayment_nonneg
    initial index
      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index)

theorem wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    0 ≤
      wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment
        initial elapsedBounded index :=
  wholeRestartCrossingCompleteOutgoingGluingVisibleSquarePayment_nonneg
    initial index
      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index)

theorem wholeRestartBoundedElapsedSourceCriticalGradientRate_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    0 ≤ wholeRestartBoundedElapsedSourceCriticalGradientRate
      initial elapsedBounded index := by
  unfold wholeRestartBoundedElapsedSourceCriticalGradientRate
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg ν.coeff_pos.le (sq_nonneg _))
      (by
        unfold wholeStateVorticityGradientMass
        exact tsum_nonneg fun wave =>
          mul_nonneg (integerWaveNormSq_nonneg wave)
            (complexCoordinateAmplitudeSq_nonneg _)))
    (Nat.cast_nonneg _)

/-- Finite accumulated physical time cannot make both generated visible
responsibility streams summable.  Thus the exact causal obstruction is now
forced into either the primitive source-self image or the complete outgoing
gluing image; aggregate cancellation supplies no third numerical sink. -/
theorem elapsedTime_bddAbove_forces_sourceSelf_or_completeGluingVisibleSquare_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (¬ Summable
        (wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment
          initial elapsedBounded)) ∨
      ¬ Summable
        (wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment
          initial elapsedBounded) := by
  by_cases sourceSummable :
      Summable
        (wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment
          initial elapsedBounded)
  · right
    intro gluingSummable
    have majorantSummable :
        Summable fun index : ℕ =>
          2 * wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment
                initial elapsedBounded index +
            2 *
              wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment
                initial elapsedBounded index :=
      (sourceSummable.mul_left 2).add (gluingSummable.mul_left 2)
    have exactSummable :
        Summable
          (wholeRestartExactCausalNonlinearSquarePayment initial) :=
      majorantSummable.of_nonneg_of_le
        (wholeRestartExactCausalNonlinearSquarePayment_nonneg initial)
        (fun index => by
          exact
            wholeRestartExactCausalNonlinearSquarePayment_le_crossingSourceSelf_add_gluing
              initial index
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded index))
    exact
      (elapsedTime_bddAbove_forces_exactCausalNonlinearSquarePayment_not_summable
        initial elapsedBounded) exactSummable
  · exact Or.inl sourceSummable

/-- Finite-time accumulation has now lost the primitive self-forcing escape:
after exact receipt heat settlement, its only remaining scalar responsibility
is the source-generated finite-core gradient divided by the actual component
count.  Otherwise the complete outgoing gluing stream itself is non-summable.
-/
theorem
    elapsedTime_bddAbove_forces_sourceCriticalGradientRate_or_completeGluingVisibleSquare_not_summable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (¬ Summable
        (wholeRestartBoundedElapsedSourceCriticalGradientRate
          initial elapsedBounded)) ∨
      ¬ Summable
        (wholeRestartBoundedElapsedCompleteOutgoingGluingVisibleSquarePayment
          initial elapsedBounded) := by
  rcases
      elapsedTime_bddAbove_forces_sourceSelf_or_completeGluingVisibleSquare_not_summable
        initial elapsedBounded with
    sourceNotSummable | gluingNotSummable
  · left
    intro criticalRateSummable
    apply sourceNotSummable
    exact criticalRateSummable.of_nonneg_of_le
      (wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment_nonneg
        initial elapsedBounded)
      (fun index => by
        simpa [wholeRestartBoundedElapsedSourceSelfVisibleSquarePayment,
          wholeRestartBoundedElapsedSourceCriticalGradientRate] using
          wholeRestartCrossingSourceSelfVisibleSquarePayment_le_gradient_div_count
            initial index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                initial elapsedBounded index))
  · exact Or.inr gluingNotSummable

end


end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger
end NavierStokes
end SaturationMonoid

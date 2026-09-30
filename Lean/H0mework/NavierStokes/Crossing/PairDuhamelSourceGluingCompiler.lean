import H0mework.NavierStokes.PairRestart.PairDuhamelTangentInnovation
import H0mework.NavierStokes.Crossing.PairGluingNativeCocycle

/-!
# Crossing source/gluing compiler for one actual causal pair occurrence

At bounded accumulated physical time the source itself selects a
half-critical crossing at every current of the actual restart run.  The
existing crossing compiler splits each pointwise pair occurrence on the
outgoing receipt into its canonical component-self part and its complete
outgoing gluing part.

This module transports that split through the same causal heat integral
before input-pair aggregation:

```text
pair Duhamel occurrence
  = canonical source-self Duhamel occurrence
    + complete outgoing gluing Duhamel occurrence.
```

After the frozen contact occurrence is removed, the canonical self term
cancels exactly.  Thus the existing pair innovation is the complete gluing
causal write minus its frozen contact gluing write.  A nonzero such residual
immediately enters the already generated next-pair / same-receipt trace
disposition.

No crossing branch, output nonzero proof, path, target state, norm,
summability certificate, or settlement witness is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairDuhamelSourceGluingCompiler

open scoped Interval

open Set MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle

noncomputable section

private def wholeRestartPairDuhamelTerminal
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    Icc (0 : ℝ) (run initial index).nextContact.time.1 :=
  ⟨(run initial index).nextContact.time.1,
    ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

/-- Time zero in the actual outgoing receipt used by the frozen-contact
gluing subtraction. -/
def wholeRestartPairDuhamelZero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    Icc (0 : ℝ) (run initial index).nextContact.time.1 :=
  ⟨0, ⟨le_rfl, (run initial index).nextContact.time_pos.le⟩⟩

/-! ## Same-receipt causal source and gluing occurrences -/

/-- Causal Duhamel transport of one canonical component-self occurrence.
The crossing proof is generated internally from bounded elapsed time. -/
def wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  let crossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  ∫ earlier in Iic (wholeRestartPairDuhamelTerminal initial index),
    finiteStateVorticityHeatMultiplier ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1) output •
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        initial index crossed output first
    ∂(commonTimeMeasure (run initial index).nextContact.time.1)

/-- Causal Duhamel transport of the complete outgoing gluing occurrence on
the same actual receipt and the same ordered input pair. -/
def wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  let crossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  ∫ earlier in Iic (wholeRestartPairDuhamelTerminal initial index),
    finiteStateVorticityHeatMultiplier ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1) output •
      wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
        initial index crossed output first earlier
    ∂(commonTimeMeasure (run initial index).nextContact.time.1)

/-- Causal heat transport preserves the existing pointwise crossing
source/gluing split on every actual output-by-pair occurrence. -/
theorem
    wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingSourceSelf_add_completeGluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartPairDuhamelOccurrence initial index output first =
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          initial elapsedBounded index output first +
        wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output first := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let requestedTime := (run initial index).nextContact.time.1
  let terminal := wholeRestartPairDuhamelTerminal initial index
  let crossed :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index
  let source :=
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
      initial index crossed output first
  let sourceIntegrand := fun earlier : Icc (0 : ℝ) requestedTime =>
    finiteStateVorticityHeatMultiplier ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1) output • source
  let gluingIntegrand := fun earlier : Icc (0 : ℝ) requestedTime =>
    finiteStateVorticityHeatMultiplier ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1) output •
      wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
        initial index crossed output first earlier
  have sourceContinuous : Continuous sourceIntegrand := by
    unfold sourceIntegrand finiteStateVorticityHeatMultiplier
    fun_prop
  have sourceIntegrable :
      Integrable sourceIntegrand
        ((commonTimeMeasure requestedTime).restrict (Iic terminal)) := by
    have wholeIntegrable :
        Integrable sourceIntegrand (commonTimeMeasure requestedTime) := by
      simpa using
        (ContinuousOn.integrableOn_compact isCompact_univ
          sourceContinuous.continuousOn)
    exact wholeIntegrable.integrableOn
  have gluingEq :
      (fun earlier : Icc (0 : ℝ) requestedTime =>
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index crossed output first earlier) =
        fun earlier =>
          actualWholeContinuousPairVector receipt output first earlier -
            source := by
    funext earlier
    have split :=
      actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
        initial index crossed output first earlier
    change _ = _ - source
    rw [split]
    abel
  have gluingContinuous : Continuous gluingIntegrand := by
    unfold gluingIntegrand
    have gluingOccurrenceContinuous :
        Continuous fun earlier : Icc (0 : ℝ) requestedTime =>
          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            initial index crossed output first earlier := by
      rw [gluingEq]
      exact
        (actualWholeContinuousPairVector_continuous
          receipt output first).sub continuous_const
    have heatContinuous :
        Continuous fun earlier : Icc (0 : ℝ) requestedTime =>
          finiteStateVorticityHeatMultiplier ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1) output := by
      unfold finiteStateVorticityHeatMultiplier
      fun_prop
    exact heatContinuous.smul gluingOccurrenceContinuous
  have gluingIntegrable :
      Integrable gluingIntegrand
        ((commonTimeMeasure requestedTime).restrict (Iic terminal)) := by
    have wholeIntegrable :
        Integrable gluingIntegrand (commonTimeMeasure requestedTime) := by
      simpa using
        (ContinuousOn.integrableOn_compact isCompact_univ
          gluingContinuous.continuousOn)
    exact wholeIntegrable.integrableOn
  unfold wholeRestartPairDuhamelOccurrence
    actualWholePairDuhamelOccurrence
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
    wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
  change
    (∫ earlier in Iic terminal,
        actualWholeCausalPairVector
          receipt output first terminal earlier
        ∂(commonTimeMeasure requestedTime)) =
      (∫ earlier in Iic terminal, sourceIntegrand earlier
        ∂(commonTimeMeasure requestedTime)) +
        ∫ earlier in Iic terminal, gluingIntegrand earlier
          ∂(commonTimeMeasure requestedTime)
  rw [← integral_add sourceIntegrable gluingIntegrable]
  apply integral_congr_ae
  filter_upwards with earlier
  unfold actualWholeCausalPairVector sourceIntegrand gluingIntegrand source
  rw [← smul_add]
  exact congrArg
    (fun row : ComplexCoordinateVector =>
      finiteStateVorticityHeatMultiplier ν.coeff
          ((run initial index).nextContact.time.1 - earlier.1) output • row)
    (actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
      initial index crossed output first earlier)

private theorem norm_sub_sq_le_two_mul
    {E : Type*} [NormedAddCommGroup E]
    (left right : E) :
    ‖left - right‖ ^ 2 ≤
      2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have normLe := norm_sub_le left right
  have squareLe :
      ‖left - right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  calc
    ‖left - right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 := squareLe
    _ ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
      nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

/-- The exact source-self Duhamel occurrence cannot be hidden by complete
gluing cancellation.  A source-generated quarter of its square remains in
the actual pair occurrence or in the complete-gluing Duhamel occurrence. -/
theorem
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_normSq_quarter_le_actual_or_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) :
    ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
        initial elapsedBounded index output first‖ ^ 2 / 4 ≤
        ‖wholeRestartPairDuhamelOccurrence
          initial index output first‖ ^ 2 ∨
      ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          initial elapsedBounded index output first‖ ^ 2 / 4 ≤
        ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output first‖ ^ 2 := by
  let source :=
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
      initial elapsedBounded index output first
  let actual :=
    wholeRestartPairDuhamelOccurrence initial index output first
  let gluing :=
    wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
      initial elapsedBounded index output first
  have actualEq : actual = source + gluing := by
    simpa [source, actual, gluing] using
      wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingSourceSelf_add_completeGluing
        initial elapsedBounded index output first
  have sourceEq : source = actual - gluing := by
    rw [actualEq]
    abel
  have sourceBound :
      ‖source‖ ^ 2 ≤
        2 * ‖actual‖ ^ 2 + 2 * ‖gluing‖ ^ 2 := by
    rw [sourceEq]
    exact norm_sub_sq_le_two_mul actual gluing
  by_cases actualLarge : ‖source‖ ^ 2 / 4 ≤ ‖actual‖ ^ 2
  · exact Or.inl (by simpa [source, actual] using actualLarge)
  · right
    have actualSmall : ‖actual‖ ^ 2 < ‖source‖ ^ 2 / 4 :=
      lt_of_not_ge actualLarge
    have gluingLarge : ‖source‖ ^ 2 / 4 ≤ ‖gluing‖ ^ 2 := by
      nlinarith
    simpa [source, gluing] using gluingLarge

/-- Positive complete-gluing Duhamel square exposes one nonzero pointwise
gluing occurrence on the same output-by-pair coordinate, then enters the
native adjacent-source/gluing cocycle. -/
theorem
    wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamel_normSq_pos_nativeRedirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector)
    (gluingPositive :
      0 <
        ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output first‖ ^ 2) :
    ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first time ≠ 0 ∧
        (wholeRestartPairOccurrenceTrace
            initial index output first time ≠ 0 ∨
          wholeRestartCrossingSourceSelfPairUpdate
              initial index
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded index)
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded (index + 1))
              output first ≠ 0 ∨
            wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
              initial (index + 1)
                (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                  initial elapsedBounded (index + 1))
              output first
                ⟨0, ⟨le_rfl,
                  (run initial
                    (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0) := by
  have gluingNonzero :
      wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
        initial elapsedBounded index output first ≠ 0 := by
    intro gluingZero
    rw [gluingZero] at gluingPositive
    simp at gluingPositive
  have existsTime :
      ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first time ≠ 0 := by
    by_contra noTime
    push Not at noTime
    apply gluingNonzero
    unfold
      wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
    simp [noTime]
  obtain ⟨time, occurrenceNonzero⟩ := existsTime
  exact
    ⟨time, occurrenceNonzero,
      wholeRestartCrossingCompleteOutgoingPairGluing_ne_zero_redirect
        initial index
          (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
            initial elapsedBounded index)
          (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
            initial elapsedBounded (index + 1))
        output first time occurrenceNonzero⟩

/-! ## Frozen source cancellation and native gluing disposition -/

/-- On an actual nonzero output, the source-self causal integral is exactly
the existing frozen causal gain applied to the canonical self occurrence. -/
theorem
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
        initial elapsedBounded index output.1 first =
      wholeRestartCausalTangentGain initial index output.1 •
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output.1 first := by
  unfold wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
  rw [integral_smul_const]
  simp only [wholeRestartPairDuhamelTerminal]
  rw [← wholeRestartCausalTangentGain_eq_heatIntegral
    initial index output.1 output.2]

/-- A nonzero source-selected primitive pair occurrence generates a positive
same-coordinate Duhamel square.  A fixed quarter is then paid by the actual
pair Duhamel occurrence or by a concrete complete-gluing native redirect. -/
theorem
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeNativeExhaustion
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (sourcePairNonzero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first ≠ 0) :
    0 <
        ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          initial elapsedBounded index output first‖ ^ 2 ∧
      (‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
            initial elapsedBounded index output first‖ ^ 2 / 4 ≤
          ‖wholeRestartPairDuhamelOccurrence
            initial index output first‖ ^ 2 ∨
        ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
          ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
                initial elapsedBounded index output first‖ ^ 2 / 4 ≤
              ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
                initial elapsedBounded index output first‖ ^ 2 ∧
            wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                initial index
                  (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                    initial elapsedBounded index)
                output first time ≠ 0 ∧
              (wholeRestartPairOccurrenceTrace
                  initial index output first time ≠ 0 ∨
                wholeRestartCrossingSourceSelfPairUpdate
                    initial index
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded index)
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded (index + 1))
                    output first ≠ 0 ∨
                  wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                    initial (index + 1)
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded (index + 1))
                    output first
                      ⟨0, ⟨le_rfl,
                        (run initial
                          (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0)) := by
  have sourceDuhamelNonzero :
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
        initial elapsedBounded index output first ≠ 0 := by
    rw [
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
        initial elapsedBounded index ⟨output, outputNonzero⟩ first]
    exact
      smul_ne_zero
        (ne_of_gt
          (wholeRestartCausalTangentGain_pos
            initial index output outputNonzero))
        sourcePairNonzero
  have sourceSquarePositive :
      0 <
        ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          initial elapsedBounded index output first‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr sourceDuhamelNonzero)
  refine ⟨sourceSquarePositive, ?_⟩
  rcases
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_normSq_quarter_le_actual_or_gluing
        initial elapsedBounded index output first with
    actualLarge | gluingLarge
  · exact Or.inl actualLarge
  · right
    have sourceQuarterPositive :
        0 <
          ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
            initial elapsedBounded index output first‖ ^ 2 / 4 := by
      positivity
    have gluingPositive :
        0 <
          ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
            initial elapsedBounded index output first‖ ^ 2 :=
      sourceQuarterPositive.trans_le gluingLarge
    obtain ⟨time, occurrenceNonzero, redirect⟩ :=
      wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamel_normSq_pos_nativeRedirect
        initial elapsedBounded index output first gluingPositive
    exact
      ⟨time, gluingLarge, occurrenceNonzero, redirect⟩

/-- Complete consume-before-quotient settlement for one source-selected
primitive pair.  Its internally generated positive source-Duhamel rate is
paid by the same output's exact causal row, or the responsible actual/gluing
pair coordinate is retained by an existing native path. -/
theorem
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeVisibleOrNativeExhaustion
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (sourcePairNonzero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first ≠ 0) :
    let sourceSquare :=
      ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
        initial elapsedBounded index output first‖ ^ 2
    let duration := (run initial index).nextContact.time.1
    let sourceRateQuantum := (sourceSquare / 16) / duration
    0 < sourceRateQuantum ∧
      (sourceRateQuantum ≤
          wholeRestartExactCausalNonlinearSquareRow
            initial index output ∨
        (sourceSquare / 4 ≤
            ‖wholeRestartPairDuhamelOccurrence
              initial index output first‖ ^ 2 ∧
          ∀ steps : ℕ,
            wholeRestartPairDuhamelPathTable
                  initial index steps output first ≠ 0 ∨
              ((generatedWholeRestartPairDuhamelEffectiveProcess
                  initial index).pathTrace 0 steps)
                0 output first ≠ 0) ∨
        ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
          sourceSquare / 4 ≤
              ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
                initial elapsedBounded index output first‖ ^ 2 ∧
            wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                initial index
                  (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                    initial elapsedBounded index)
                output first time ≠ 0 ∧
              (wholeRestartPairOccurrenceTrace
                  initial index output first time ≠ 0 ∨
                wholeRestartCrossingSourceSelfPairUpdate
                    initial index
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded index)
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded (index + 1))
                    output first ≠ 0 ∨
                  wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                    initial (index + 1)
                      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                        initial elapsedBounded (index + 1))
                    output first
                      ⟨0, ⟨le_rfl,
                        (run initial
                          (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0)) := by
  dsimp only
  have sourceExhaustion :=
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeNativeExhaustion
      initial elapsedBounded index output first outputNonzero
      sourcePairNonzero
  have durationPositive :
      0 < (run initial index).nextContact.time.1 :=
    (run initial index).nextContact.time_pos
  have sourceRatePositive :
      0 <
        (‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
            initial elapsedBounded index output first‖ ^ 2 / 16) /
          (run initial index).nextContact.time.1 := by
    exact div_pos (div_pos sourceExhaustion.1 (by norm_num))
      durationPositive
  refine ⟨sourceRatePositive, ?_⟩
  rcases sourceExhaustion.2 with actualLarge | gluingRedirect
  · have sourceQuarterPositive :
        0 <
          ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
            initial elapsedBounded index output first‖ ^ 2 / 4 := by
      exact div_pos sourceExhaustion.1 (by norm_num)
    have actualSquarePositive :
        0 <
          ‖wholeRestartPairDuhamelOccurrence
            initial index output first‖ ^ 2 :=
      sourceQuarterPositive.trans_le actualLarge
    have actualOccurrenceNonzero :
        wholeRestartPairDuhamelOccurrence
          initial index output first ≠ 0 := by
      intro actualZero
      rw [actualZero] at actualSquarePositive
      simp at actualSquarePositive
    rcases
        wholeRestartPairDuhamelOccurrence_normSq_quarter_le_visible_or_nativePathTransport
          initial index output first actualOccurrenceNonzero with
      visibleLarge | nativePath
    · left
      have sourceSixteenthLeVisible :
          ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
                initial elapsedBounded index output first‖ ^ 2 / 16 ≤
            ‖∑' other : IntegerWavevector,
              wholeRestartPairDuhamelOccurrence
                initial index output other‖ ^ 2 := by
        nlinarith
      calc
        (‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
              initial elapsedBounded index output first‖ ^ 2 / 16) /
              (run initial index).nextContact.time.1 ≤
            ‖∑' other : IntegerWavevector,
              wholeRestartPairDuhamelOccurrence
                initial index output other‖ ^ 2 /
              (run initial index).nextContact.time.1 :=
          div_le_div_of_nonneg_right sourceSixteenthLeVisible
            durationPositive.le
        _ ≤
            wholeRestartExactCausalNonlinearSquareRow
              initial index output :=
          wholeRestartPairDuhamelVisibleRate_le_exactCausalNonlinearSquareRow
            initial index output outputNonzero
    · exact Or.inr (Or.inl ⟨actualLarge, nativePath.2⟩)
  · exact Or.inr (Or.inr gluingRedirect)

/-- Nonzero-output form consumed directly by the anchored Fourier compiler:
one actual pair Duhamel occurrence is the canonical source-self occurrence
transported by the exact causal gain plus the complete causal gluing
occurrence. -/
theorem
    wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingGainSourceSelf_add_completeGluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartPairDuhamelOccurrence initial index output.1 first =
      wholeRestartCausalTangentGain initial index output.1 •
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
            initial index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                initial elapsedBounded index)
            output.1 first +
        wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output.1 first := by
  rw [
    wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingSourceSelf_add_completeGluing
      initial elapsedBounded index output.1 first,
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
      initial elapsedBounded index output first]

/-- The frozen contact table has the same source-self / complete-gluing
split, at time zero of that very receipt. -/
theorem
    wholeRestartContactPairOccurrenceTable_eq_boundedElapsedCrossingSourceSelf_add_completeGluingZero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartContactPairOccurrenceTable initial index output first =
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first +
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index
            (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
              initial elapsedBounded index)
          output first (wholeRestartPairDuhamelZero initial index) := by
  have split :=
    actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
      initial index
        (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
          initial elapsedBounded index)
      output first (wholeRestartPairDuhamelZero initial index)
  simpa [wholeRestartPairDuhamelZero,
    actualWholeContinuousPairVector_zero_eq_contact] using split

/-- The pair innovation is not a second source term.  The canonical
source-self contribution cancels exactly against the frozen contact
subtraction, leaving the causal complete-gluing write minus its own frozen
contact value. -/
theorem
    wholeRestartPairDuhamelInnovationOccurrence_eq_boundedElapsedCrossingCompleteGluingResidual
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartPairDuhamelInnovationOccurrence
        initial index output.1 first =
      wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output.1 first -
        wholeRestartCausalTangentGain initial index output.1 •
          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            initial index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                initial elapsedBounded index)
            output.1 first (wholeRestartPairDuhamelZero initial index) := by
  unfold wholeRestartPairDuhamelInnovationOccurrence
  rw [
    wholeRestartPairDuhamelOccurrence_eq_boundedElapsedCrossingSourceSelf_add_completeGluing
      initial elapsedBounded index output.1 first,
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
      initial elapsedBounded index output first,
    wholeRestartContactPairOccurrenceTable_eq_boundedElapsedCrossingSourceSelf_add_completeGluingZero
      initial elapsedBounded index output.1 first,
    smul_add]
  module

/-- Compatibility regression with the authoritative dynamic-gluing theorem:
the newly exposed complete-gluing residual is exactly the old same-receipt
dynamic gluing causal integral, not a parallel observer or a new normed
carrier. -/
theorem
    wholeRestartBoundedElapsedCrossingCompleteGluingResidual_eq_dynamicGluingIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output.1 first -
        wholeRestartCausalTangentGain initial index output.1 •
          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            initial index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                initial elapsedBounded index)
            output.1 first (wholeRestartPairDuhamelZero initial index) =
      ∫ earlier in Iic (wholeRestartPairDuhamelTerminal initial index),
        finiteStateVorticityHeatMultiplier ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1) output.1 •
          wholeRestartCrossingDynamicPairGluingOccurrence
            initial index output.1 first earlier
        ∂(commonTimeMeasure (run initial index).nextContact.time.1) := by
  rw [←
    wholeRestartPairDuhamelInnovationOccurrence_eq_boundedElapsedCrossingCompleteGluingResidual
      initial elapsedBounded index output first]
  simpa [wholeRestartPairDuhamelTerminal] using
    wholeRestartPairDuhamelInnovationOccurrence_eq_dynamicGluingIntegral
      initial index output.1 first output.2

/-- Source-facing exact compiler and native no-silent disposition.  The
caller supplies only the actual run, its bounded elapsed fact, one actual
index and one output-by-pair coordinate.  If the generated complete-gluing
causal residual is nonzero, that same pair occurrence survives in the next
actual table or in its same-receipt pointwise trace. -/
theorem
    wholeRestartBoundedElapsedCrossingCompleteGluingResidual_nativeCompiler
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    let gluingResidual :=
      wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
          initial elapsedBounded index output.1 first -
        wholeRestartCausalTangentGain initial index output.1 •
          wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            initial index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                initial elapsedBounded index)
            output.1 first (wholeRestartPairDuhamelZero initial index)
    wholeRestartPairDuhamelInnovationOccurrence
          initial index output.1 first = gluingResidual ∧
      (gluingResidual ≠ 0 →
        wholeRestartNextPairOccurrence
              initial index output.1 first ≠ 0 ∨
          ∃ time :
              Icc (0 : ℝ) (run initial index).nextContact.time.1,
            wholeRestartPairOccurrenceTrace
              initial index output.1 first time ≠ 0) := by
  dsimp only
  have compiler :=
    wholeRestartPairDuhamelInnovationOccurrence_eq_boundedElapsedCrossingCompleteGluingResidual
      initial elapsedBounded index output first
  refine ⟨compiler, ?_⟩
  intro residualNonzero
  apply
    wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
      initial index output.1 first
  intro innovationZero
  apply residualNonzero
  rw [← compiler, innovationZero]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairDuhamelSourceGluingCompiler
end NavierStokes
end SaturationMonoid

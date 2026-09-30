import H0mework.NavierStokes.PairRestart.PairDuhamelExactHeadroom

/-!
# Same-receipt causal redirect of one pair-Duhamel occurrence

One nonzero causal pair-Duhamel component is already a state-sized quantity.
This module transports the existing pointwise read/write split through the
same causal heat kernel:

```text
pairDuhamel = actual-next-pair keep + forced same-receipt causal trace.
```

Consequently, a nonzero pre-aggregation component must remain visible in the
next actual physical current or leave a nonzero causal trace on that exact
pair occurrence.  No uniform quantum, output cutoff, branch, target state,
faithfulness certificate, or continuation witness is accepted.

The causal trace is an actual componentwise redirect.  This module does not
claim that its nonzero value already generates a later macro action.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect

open scoped BigOperators ENNReal Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open AffineRelaxation

noncomputable section

/-! ## Causal keep and forced trace on one actual pair occurrence -/

/-- Causal heat transport of the terminal pair component already written in
the next actual physical current. -/
def wholeRestartPairDuhamelNextKeep
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  ∫ earlier in Iic
      (⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
        Icc (0 : ℝ) (run initial index).nextContact.time.1),
    finiteStateVorticityHeatMultiplier
        ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1)
        output •
      wholeRestartNextPairOccurrence initial index output first
    ∂(commonTimeMeasure (run initial index).nextContact.time.1)

/-- Forced same-receipt trace after causal heat transport, before pair
aggregation. -/
def wholeRestartPairDuhamelCausalTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  ∫ earlier in Iic
      (⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
        Icc (0 : ℝ) (run initial index).nextContact.time.1),
    finiteStateVorticityHeatMultiplier
        ν.coeff
        ((run initial index).nextContact.time.1 - earlier.1)
        output •
      wholeRestartPairOccurrenceTrace
        initial index output first earlier
    ∂(commonTimeMeasure (run initial index).nextContact.time.1)

private theorem integrable_wholeRestartPairDuhamelNextKeepIntegrand
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    Integrable
      (fun earlier :
          Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        finiteStateVorticityHeatMultiplier
            ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1)
            output •
          wholeRestartNextPairOccurrence initial index output first)
      ((commonTimeMeasure (run initial index).nextContact.time.1).restrict
        (Iic
          (⟨(run initial index).nextContact.time.1,
            ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
            Icc (0 : ℝ) (run initial index).nextContact.time.1))) := by
  have integrandContinuous :
      Continuous
        (fun earlier :
            Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          finiteStateVorticityHeatMultiplier
              ν.coeff
              ((run initial index).nextContact.time.1 - earlier.1)
              output •
            wholeRestartNextPairOccurrence
              initial index output first) := by
    unfold finiteStateVorticityHeatMultiplier
    fun_prop
  exact
    (integrandContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn

private theorem integrable_wholeRestartPairDuhamelCausalTraceIntegrand
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    Integrable
      (fun earlier :
          Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        finiteStateVorticityHeatMultiplier
            ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1)
            output •
          wholeRestartPairOccurrenceTrace
            initial index output first earlier)
      ((commonTimeMeasure (run initial index).nextContact.time.1).restrict
        (Iic
          (⟨(run initial index).nextContact.time.1,
            ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
            Icc (0 : ℝ) (run initial index).nextContact.time.1))) := by
  have traceContinuous :
      Continuous
        (wholeRestartPairOccurrenceTrace
          initial index output first) := by
    unfold wholeRestartPairOccurrenceTrace
    exact
      (actualWholeContinuousPairVector_continuous
        (run initial index).nextContact.prefixReceipt output first).sub
        continuous_const
  have multiplierContinuous :
      Continuous
        (fun earlier :
            Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
          finiteStateVorticityHeatMultiplier
            ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1)
            output) := by
    unfold finiteStateVorticityHeatMultiplier
    fun_prop
  exact
    ((multiplierContinuous.smul traceContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn

/-- Exact same-event causal transport of the pointwise pair read/write split.
All three terms use the same receipt, heat kernel, duration, output, input-pair
identity, and state-sized coefficient carrier. -/
theorem wholeRestartPairDuhamelOccurrence_eq_nextKeep_add_causalTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartPairDuhamelOccurrence initial index output first =
      wholeRestartPairDuhamelNextKeep initial index output first +
        wholeRestartPairDuhamelCausalTrace
          initial index output first := by
  unfold wholeRestartPairDuhamelOccurrence
    actualWholePairDuhamelOccurrence
    actualWholeCausalPairVector
    wholeRestartPairDuhamelNextKeep
    wholeRestartPairDuhamelCausalTrace
  rw [← integral_add
    (integrable_wholeRestartPairDuhamelNextKeepIntegrand
      initial index output first)
    (integrable_wholeRestartPairDuhamelCausalTraceIntegrand
      initial index output first)]
  apply integral_congr_ae
  filter_upwards with earlier
  rw [← smul_add]
  rw [← actualWholeContinuousPairVector_eq_next_add_trace
    initial index output first earlier]

/-- A nonzero causal trace cannot be created by integration alone: some
source-generated time slice already carries a nonzero trace in the existing
spliced pair-occurrence effective process.  The witnessing time is generated
from the same receipt rather than supplied by the caller. -/
theorem
    wholeRestartPairDuhamelCausalTrace_ne_zero_generates_splicedProcessTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (causalTraceNonzero :
      wholeRestartPairDuhamelCausalTrace
        initial index output first ≠ 0) :
    ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      (linearResidualTrace wholeRestartSplicedPairOccurrenceTailKeep
          (wholeRestartSplicedPairOccurrenceTail initial index time 0)
          0) output first ≠ 0 := by
  by_contra noTraceTime
  push Not at noTraceTime
  apply causalTraceNonzero
  unfold wholeRestartPairDuhamelCausalTrace
  have integrandZero :
      (fun earlier :
          Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
        finiteStateVorticityHeatMultiplier
              ν.coeff
              ((run initial index).nextContact.time.1 - earlier.1)
              output •
            wholeRestartPairOccurrenceTrace
              initial index output first earlier) = 0 := by
    funext earlier
    change
      finiteStateVorticityHeatMultiplier
            ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1)
            output •
          wholeRestartPairOccurrenceTrace
            initial index output first earlier =
        (0 : ComplexCoordinateVector)
    have traceZero :
        wholeRestartPairOccurrenceTrace
            initial index output first earlier = 0 := by
      change
        (linearResidualTrace wholeRestartSplicedPairOccurrenceTailKeep
            (wholeRestartSplicedPairOccurrenceTail
              initial index earlier 0)
            0) output first = 0
      exact noTraceTime earlier
    rw [traceZero, smul_zero]
  rw [integrandZero]
  simp

/-! ## Exact pair-gluing content of the forced trace -/

/-- The pointwise trace is exactly the polarization defect between the
outgoing path state and the terminal state already written as the next actual
restart contact. -/
theorem wholeRestartPairOccurrenceTrace_eq_terminalPairGluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartPairOccurrenceTrace initial index output first time =
      finiteStateVorticityBilinearPairContribution
          ((run initial index).nextContact.prefixReceipt.wholePath time -
            (run initial (index + 1)).contact.physicalState)
          ((run initial index).nextContact.prefixReceipt.wholePath time)
          (first, output - first) +
        finiteStateVorticityBilinearPairContribution
          ((run initial (index + 1)).contact.physicalState)
          ((run initial index).nextContact.prefixReceipt.wholePath time -
            (run initial (index + 1)).contact.physicalState)
          (first, output - first) := by
  unfold wholeRestartPairOccurrenceTrace
    actualWholeContinuousPairVector
    wholeRestartNextPairOccurrence
  exact finiteStateVorticityNonlinearPairContribution_sub _ _ _

/-- The integrated forced trace is therefore a heat-weighted sum of the two
literal bilinear gluing atoms of the same actual receipt. -/
theorem wholeRestartPairDuhamelCausalTrace_eq_terminalPairGluingIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartPairDuhamelCausalTrace initial index output first =
      ∫ earlier in Iic
          (⟨(run initial index).nextContact.time.1,
            ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
            Icc (0 : ℝ) (run initial index).nextContact.time.1),
        finiteStateVorticityHeatMultiplier
            ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1)
            output •
          (finiteStateVorticityBilinearPairContribution
              ((run initial index).nextContact.prefixReceipt.wholePath earlier -
                (run initial (index + 1)).contact.physicalState)
              ((run initial index).nextContact.prefixReceipt.wholePath earlier)
              (first, output - first) +
            finiteStateVorticityBilinearPairContribution
              ((run initial (index + 1)).contact.physicalState)
              ((run initial index).nextContact.prefixReceipt.wholePath earlier -
                (run initial (index + 1)).contact.physicalState)
              (first, output - first))
        ∂(commonTimeMeasure (run initial index).nextContact.time.1) := by
  unfold wholeRestartPairDuhamelCausalTrace
  apply integral_congr_ae
  filter_upwards with earlier
  rw [wholeRestartPairOccurrenceTrace_eq_terminalPairGluing
    initial index output first earlier]

/-- A nonzero integrated pair component cannot be erased by the terminal
read.  It survives in the next actual physical pair table or in the forced
causal trace of the same receipt and occurrence. -/
theorem wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (occurrenceNonzero :
      wholeRestartPairDuhamelOccurrence
        initial index output first ≠ 0) :
    wholeRestartNextPairOccurrence initial index output first ≠ 0 ∨
      wholeRestartPairDuhamelCausalTrace
        initial index output first ≠ 0 := by
  by_cases nextNonzero :
      wholeRestartNextPairOccurrence initial index output first ≠ 0
  · exact Or.inl nextNonzero
  · right
    intro traceZero
    apply occurrenceNonzero
    rw [wholeRestartPairDuhamelOccurrence_eq_nextKeep_add_causalTrace,
      traceZero, add_zero]
    unfold wholeRestartPairDuhamelNextKeep
    simp [not_ne_iff.mp nextNonzero]

/-- Exact aggregation-kernel cancellation now yields two distinct concrete
components, and each component is immediately redirected to its actual next
pair or its same-receipt causal gluing trace.  The complement equality keeps
the original cancellation provenance; it is not used as a closure witness. -/
theorem pairDuhamelAggregationKernel_componentwise_terminalTraceRedirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (tableNonzero :
      (fun first : IntegerWavevector =>
        wholeRestartPairDuhamelOccurrence
          initial index output first) ≠ 0)
    (aggregateZero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelOccurrence
          initial index output first) = 0) :
    ∃ first second : IntegerWavevector,
      first ≠ second ∧
        wholeRestartPairDuhamelOccurrence
            initial index output first ≠ 0 ∧
        wholeRestartPairDuhamelOccurrence
            initial index output second ≠ 0 ∧
        ((∑' other : IntegerWavevector,
            if other = first then 0 else
              wholeRestartPairDuhamelOccurrence
                initial index output other) =
          -wholeRestartPairDuhamelOccurrence
            initial index output first) ∧
        (wholeRestartNextPairOccurrence
              initial index output first ≠ 0 ∨
          wholeRestartPairDuhamelCausalTrace
              initial index output first ≠ 0) ∧
        (wholeRestartNextPairOccurrence
              initial index output second ≠ 0 ∨
          wholeRestartPairDuhamelCausalTrace
              initial index output second ≠ 0) := by
  rcases
      pairDuhamelAggregationKernel_componentwise_nativePathTransport
        initial index output tableNonzero aggregateZero with
    ⟨first, second, firstNeSecond, firstNonzero, secondNonzero,
      complementEq, futureTransport⟩
  refine ⟨first, second, firstNeSecond, firstNonzero, secondNonzero,
    complementEq, ?_, ?_⟩
  · exact wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
      initial index output first firstNonzero
  · exact wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
      initial index output second secondNonzero

/-! ## Exact-payment keep re-enters the same terminal redirect -/

/-- Any concrete finite-horizon keep now re-enters the exact physical
payment or produces a kernel component carrying both its chronological
future/path transport and its immediate same-receipt terminal redirect. -/
theorem wholeRestartPairDuhamelKeep_positiveExactPayment_or_terminalTraceRedirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index steps : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (keepNonzero :
      wholeRestartPairDuhamelPathTable
        initial index steps output first ≠ 0) :
    (0 <
        ‖wholeRestartNonlinearRegenerationState
            initial (index + steps) output‖ ^ 2 /
          (run initial (index + steps)).nextContact.time.1 ∧
      ‖wholeRestartNonlinearRegenerationState
            initial (index + steps) output‖ ^ 2 /
          (run initial (index + steps)).nextContact.time.1 ≤
        wholeRestartExactCausalNonlinearSquareRow
          initial (index + steps) output) ∨
      ∃ component : IntegerWavevector,
        (∑' other : IntegerWavevector,
          wholeRestartPairDuhamelOccurrence
            initial (index + steps) output other) = 0 ∧
        wholeRestartPairDuhamelOccurrence
            initial (index + steps) output component ≠ 0 ∧
        (wholeRestartNextPairOccurrence
              initial (index + steps) output component ≠ 0 ∨
          wholeRestartPairDuhamelCausalTrace
              initial (index + steps) output component ≠ 0) ∧
        ∀ horizon : ℕ,
          wholeRestartPairDuhamelPathTable
                initial (index + steps) horizon output component ≠ 0 ∨
            ((generatedWholeRestartPairDuhamelEffectiveProcess
                initial (index + steps)).pathTrace 0 horizon)
              0 output component ≠ 0 := by
  rcases
      wholeRestartPairDuhamelKeep_positiveExactPayment_or_kernelTransport
        initial index steps output first outputNonzero keepNonzero with
    visiblePayment | kernelTransport
  · exact Or.inl visiblePayment
  · rcases kernelTransport with
      ⟨component, aggregateZero, componentNonzero, futureTransport⟩
    exact Or.inr
      ⟨component, aggregateZero, componentNonzero,
        wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
          initial (index + steps) output component componentNonzero,
        futureTransport⟩

/-! ## Arbitrarily late native responsibility under finite-time accumulation -/

/-- A nonzero quadratic regeneration rate is generated by a concrete causal
pair occurrence before aggregation.  That occurrence is immediately written
either into the next actual physical pair table or into a nonzero
whole-carrier trace at a source-generated time slice of the same receipt. -/
theorem
    wholeRestartNonlinearRegenerationRateSquare_ne_zero_generates_pairDuhamel_nativeResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (rateNonzero :
      wholeRestartNonlinearRegenerationRateSquare initial index ≠ 0) :
    ∃ output : IntegerWavevector,
      output ≠ 0 ∧
        ∃ first : IntegerWavevector,
          wholeRestartPairDuhamelOccurrence
                initial index output first ≠ 0 ∧
            (wholeRestartNextPairOccurrence
                  initial index output first ≠ 0 ∨
              ∃ time :
                  Icc (0 : ℝ) (run initial index).nextContact.time.1,
                (linearResidualTrace
                    wholeRestartSplicedPairOccurrenceTailKeep
                    (wholeRestartSplicedPairOccurrenceTail
                      initial index time 0)
                    0) output first ≠ 0) := by
  have regenerationStateNonzero :
      wholeRestartNonlinearRegenerationState initial index ≠ 0 := by
    intro regenerationStateZero
    apply rateNonzero
    simp [wholeRestartNonlinearRegenerationRateSquare,
      wholeRestartNonlinearRegenerationNorm, regenerationStateZero]
  have existsOutput :
      ∃ output : IntegerWavevector,
        wholeRestartNonlinearRegenerationState
          initial index output ≠ 0 := by
    by_contra noOutput
    push Not at noOutput
    apply regenerationStateNonzero
    apply lp.ext
    funext output
    exact noOutput output
  obtain ⟨output, outputNonzeroRow⟩ := existsOutput
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    exact outputNonzeroRow
      (wholeRestartNonlinearRegenerationState_zero initial index)
  have aggregateNonzero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelOccurrence
          initial index output first) ≠ 0 := by
    rw [tsum_wholeRestartPairDuhamelOccurrence_eq_regeneration
      initial index output outputNonzero]
    exact outputNonzeroRow
  have existsFirst :
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelOccurrence
          initial index output first ≠ 0 := by
    by_contra noFirst
    push Not at noFirst
    apply aggregateNonzero
    have tableZero :
        (fun first : IntegerWavevector =>
          wholeRestartPairDuhamelOccurrence
            initial index output first) = 0 := by
      funext first
      exact noFirst first
    rw [tableZero]
    exact tsum_zero
  obtain ⟨first, occurrenceNonzero⟩ := existsFirst
  refine ⟨output, outputNonzero, first, occurrenceNonzero, ?_⟩
  rcases
      wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
        initial index output first occurrenceNonzero with
    nextNonzero | causalTraceNonzero
  · exact Or.inl nextNonzero
  · exact Or.inr
      (wholeRestartPairDuhamelCausalTrace_ne_zero_generates_splicedProcessTrace
        initial index output first causalTraceNonzero)

/-- Direct finite-time hard-gate reduction on the native pair carrier.
If actual physical time accumulated, every chronological tail would contain
a newly generated nonzero causal pair occurrence, and that occurrence already
has its actual next/trace disposition.  No summability certificate, output,
pair, horizon, branch, cutoff, continuation, or uniform quantum is supplied
by the caller. -/
theorem
    elapsedTime_bddAbove_generates_arbitrarily_late_pairDuhamel_nativeResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (start : ℕ) :
    ∃ index : ℕ,
      start ≤ index ∧
        ∃ output : IntegerWavevector,
          output ≠ 0 ∧
            ∃ first : IntegerWavevector,
              wholeRestartPairDuhamelOccurrence
                    initial index output first ≠ 0 ∧
                (wholeRestartNextPairOccurrence
                      initial index output first ≠ 0 ∨
                  ∃ time :
                      Icc (0 : ℝ) (run initial index).nextContact.time.1,
                    (linearResidualTrace
                        wholeRestartSplicedPairOccurrenceTailKeep
                        (wholeRestartSplicedPairOccurrenceTail
                          initial index time 0)
                        0) output first ≠ 0) := by
  have rateNotSummable :=
    elapsedTime_bddAbove_forces_nonlinearRegenerationRateSquare_not_summable
      initial elapsedBounded
  have existsRate :
      ∃ index : ℕ,
        start ≤ index ∧
          wholeRestartNonlinearRegenerationRateSquare
            initial index ≠ 0 := by
    by_contra noRate
    push Not at noRate
    have tailZero :
        (fun offset : ℕ =>
          wholeRestartNonlinearRegenerationRateSquare
            initial (offset + start)) = 0 := by
      funext offset
      exact noRate (offset + start) (by omega)
    have tailSummable :
        Summable fun offset : ℕ =>
          wholeRestartNonlinearRegenerationRateSquare
            initial (offset + start) := by
      rw [tailZero]
      exact summable_zero
    apply rateNotSummable
    exact
      (summable_nat_add_iff
        (G := ℝ)
        (f := wholeRestartNonlinearRegenerationRateSquare initial)
        start).mp tailSummable
  obtain ⟨index, startLe, rateNonzero⟩ := existsRate
  exact
    ⟨index, startLe,
      wholeRestartNonlinearRegenerationRateSquare_ne_zero_generates_pairDuhamel_nativeResponsibility
        initial index rateNonzero⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
end NavierStokes
end SaturationMonoid

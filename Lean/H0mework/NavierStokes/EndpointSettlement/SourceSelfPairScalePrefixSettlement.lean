import H0mework.NavierStokes.EndpointSettlement.SourceSelfPairScaleFeedback
import H0mework.NavierStokes.PairRestart.PairDuhamelTerminalTraceRedirect

/-!
# Whole-carrier settlement of source-self pair responsibility along scale prefixes

The adjacent scale feedback is consumed before any scalar pair quotient.
A nonzero Duhamel occurrence at the next source-generated scale is immediately
written into the next actual physical pair table or into the same-receipt
spliced residual trace.  The alternative intervening path trace already is
the unique whole pair-table complement between the two scale states.

Those adjacent complements telescope over every finite prefix of the strict
source lineage.  Thus one thin actual lineage generates both the nodewise
native disposition and one exact prefix write-back ledger.  No horizon,
output, pair, branch, nonzero witness, target state, or continuation witness
is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairVisibleSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairDuhamelSourceGluingCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairGluingNativeCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open AffineRelaxation

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The exact complete pair-table trace generated between adjacent absolute
scale occurrences.  It is a readout of the existing effective process, not
an independently chosen path or ledger entry. -/
def WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTrace
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : WholeRestartPairDuhamelTable :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  ((generatedWholeRestartPairDuhamelEffectiveProcess
    tail index).pathTrace 0 (scale.nextScaleGap step)) 0

/-- The adjacent scale split written with the source-generated gap trace. -/
theorem WholeRestartReducedCoreScaleLineage.pairDuhamel_nextScale_gapTrace_split
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence step) =
      wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence (step + 1)) +
        scale.sourcePairDuhamelGapTrace step := by
  simpa [WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTrace] using
    scale.pairDuhamel_nextScale_split step

/-- Newest-first occurrence ledger of the exact adjacent scale traces.  The
list retains which source edge generated each table before its additive
readout is taken. -/
def WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (length : ℕ) : List WholeRestartPairDuhamelTable :=
  (List.range length).reverse.map scale.sourcePairDuhamelGapTrace

@[simp] theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger_succ
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (length : ℕ) :
    scale.sourcePairDuhamelGapTraceLedger (length + 1) =
      scale.sourcePairDuhamelGapTrace length ::
        scale.sourcePairDuhamelGapTraceLedger length := by
  simp [
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger,
    List.range_succ]

@[simp] theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger_length
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (length : ℕ) :
    (scale.sourcePairDuhamelGapTraceLedger length).length = length := by
  simp [
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger]

/-- Every generated adjacent trace remains an individual occurrence in the
prefix ledger before the additive telescope is read. -/
theorem WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTrace_mem_ledger
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    {step length : ℕ}
    (stepLt : step < length) :
    scale.sourcePairDuhamelGapTrace step ∈
      scale.sourcePairDuhamelGapTraceLedger length := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger
  apply List.mem_map.mpr
  exact
    ⟨step, by
      simpa using (List.mem_range.mpr stepLt), rfl⟩

/-- Exact telescope of the occurrence-preserving adjacent trace ledger.
Restart charts cannot duplicate or erase a payment: only the final actual
table and the additive readout of the source-generated list remain. -/
theorem WholeRestartReducedCoreScaleLineage.pairDuhamel_scalePrefix_split
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (length : ℕ) :
    wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence 0) =
      wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence length) +
        (scale.sourcePairDuhamelGapTraceLedger length).sum := by
  induction length with
  | zero =>
      simp [
        WholeRestartReducedCoreScaleLineage.sourcePairDuhamelGapTraceLedger]
  | succ length ih =>
      rw [scale.sourcePairDuhamelGapTraceLedger_succ, List.sum_cons]
      calc
        wholeRestartPairDuhamelTable
              initial (scale.absoluteOccurrence 0) =
            wholeRestartPairDuhamelTable
                initial (scale.absoluteOccurrence length) +
              (scale.sourcePairDuhamelGapTraceLedger length).sum :=
          ih
        _ =
            (wholeRestartPairDuhamelTable
                initial (scale.absoluteOccurrence (length + 1)) +
              scale.sourcePairDuhamelGapTrace length) +
                (scale.sourcePairDuhamelGapTraceLedger length).sum := by
          rw [scale.pairDuhamel_nextScale_gapTrace_split length]
        _ =
            wholeRestartPairDuhamelTable
                initial (scale.absoluteOccurrence (length + 1)) +
              (scale.sourcePairDuhamelGapTrace length ::
                scale.sourcePairDuhamelGapTraceLedger length).sum := by
          simp only [List.sum_cons]
          abel

/-- Native pair destination after the exact next scale has itself been
consumed before quotient.  A surviving Duhamel occurrence writes the next
actual physical pair table or a same-receipt spliced residual trace; the
intervening whole pair-table trace and complete-gluing cocycle remain native
alternatives. -/
abbrev
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleWholeWriteAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
  (output first : IntegerWavevector) : Prop :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let nextIndex := scale.absoluteOccurrence (step + 1)
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  let sourceSquare :=
    ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
      tail tailElapsedBounded index output first‖ ^ 2
  ((sourceSquare / 4 ≤
        ‖wholeRestartPairDuhamelOccurrence
          tail index output first‖ ^ 2 ∧
      (wholeRestartNextPairOccurrence
            tail index output first ≠ 0 ∨
        ∃ time :
            Icc (0 : ℝ) (run tail index).nextContact.time.1,
          (linearResidualTrace
              wholeRestartSplicedPairOccurrenceTailKeep
              (wholeRestartSplicedPairOccurrenceTail
                tail index time 0)
              0) output first ≠ 0) ∧
      (wholeRestartNextPairOccurrence
            initial nextIndex output first ≠ 0 ∨
        (∃ time :
            Icc (0 : ℝ) (run initial nextIndex).nextContact.time.1,
          (linearResidualTrace
              wholeRestartSplicedPairOccurrenceTailKeep
              (wholeRestartSplicedPairOccurrenceTail
                initial nextIndex time 0)
              0) output first ≠ 0) ∨
        scale.sourcePairDuhamelGapTrace step output first ≠ 0)) ∨
    ∃ time : Icc (0 : ℝ) (run tail index).nextContact.time.1,
      sourceSquare / 4 ≤
          ‖wholeRestartBoundedElapsedCrossingCompleteGluingPairDuhamelOccurrence
            tail tailElapsedBounded index output first‖ ^ 2 ∧
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
            tail index
              (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                tail tailElapsedBounded index)
            output first time ≠ 0 ∧
          (wholeRestartPairOccurrenceTrace
              tail index output first time ≠ 0 ∨
            wholeRestartCrossingSourceSelfPairUpdate
                tail index
                  (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                    tail tailElapsedBounded index)
                  (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                    tail tailElapsedBounded (index + 1))
                output first ≠ 0 ∨
              wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
                tail (index + 1)
                  (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
                    tail tailElapsedBounded (index + 1))
                output first
                  ⟨0, ⟨le_rfl,
                    (run tail
                      (index + 1)).nextContact.time_pos.le⟩⟩ ≠ 0))

/-- Consume a next-scale native occurrence immediately into the physical pair
write or same-receipt spliced residual trace. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleWholeWriteAt_of_nextScaleNativeAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector)
    (nextNative :
      scale.sourcePairDuhamelNextScaleNativeAt
        elapsedBounded step output first)
    (quantumPos :
      0 < scale.sourcePairDuhamelRateQuantum
        elapsedBounded step output first) :
    scale.sourcePairDuhamelNextScaleWholeWriteAt
      elapsedBounded step output first := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleNativeAt
      at nextNative
  unfold
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleWholeWriteAt
  dsimp only at nextNative ⊢
  rcases nextNative with actual | gluing
  · left
    have sourceDuhamelNonzero :
        wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
          (run initial (scale.start step))
          (elapsedTime_run_bddAbove
            initial elapsedBounded (scale.start step))
          (scale.relativeIndex step) output first ≠ 0 := by
      intro sourceZero
      unfold
        WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum
          at quantumPos
      dsimp only at quantumPos
      rw [sourceZero] at quantumPos
      norm_num at quantumPos
    have sourceQuarterPos :
        0 <
          ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
            (run initial (scale.start step))
            (elapsedTime_run_bddAbove
              initial elapsedBounded (scale.start step))
            (scale.relativeIndex step) output first‖ ^ 2 / 4 :=
      div_pos
        (sq_pos_of_pos (norm_pos_iff.mpr sourceDuhamelNonzero))
        (by norm_num)
    have currentSquarePos :
        0 <
          ‖wholeRestartPairDuhamelOccurrence
            (run initial (scale.start step))
            (scale.relativeIndex step) output first‖ ^ 2 :=
      sourceQuarterPos.trans_le actual.1
    have currentNonzero :
        wholeRestartPairDuhamelOccurrence
          (run initial (scale.start step))
          (scale.relativeIndex step) output first ≠ 0 := by
      intro currentZero
      rw [currentZero] at currentSquarePos
      norm_num at currentSquarePos
    have currentWrite :
        wholeRestartNextPairOccurrence
              (run initial (scale.start step))
              (scale.relativeIndex step) output first ≠ 0 ∨
          ∃ time :
              Icc (0 : ℝ)
                (run (run initial (scale.start step))
                  (scale.relativeIndex step)).nextContact.time.1,
            (linearResidualTrace
                wholeRestartSplicedPairOccurrenceTailKeep
                (wholeRestartSplicedPairOccurrenceTail
                  (run initial (scale.start step))
                  (scale.relativeIndex step) time 0)
                0) output first ≠ 0 := by
      rcases
          wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
            (run initial (scale.start step))
            (scale.relativeIndex step) output first currentNonzero with
        nextPhysical | causalTrace
      · exact Or.inl nextPhysical
      · exact Or.inr
          (wholeRestartPairDuhamelCausalTrace_ne_zero_generates_splicedProcessTrace
            (run initial (scale.start step))
            (scale.relativeIndex step) output first causalTrace)
    refine ⟨actual.1, currentWrite, ?_⟩
    rcases actual.2 with future | gapTrace
    · rcases
        wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
          initial (scale.absoluteOccurrence (step + 1))
            output first future with
        nextPhysical | causalTrace
      · exact Or.inl nextPhysical
      · exact Or.inr (Or.inl
          (wholeRestartPairDuhamelCausalTrace_ne_zero_generates_splicedProcessTrace
            initial (scale.absoluteOccurrence (step + 1))
              output first causalTrace))
    · exact Or.inr (Or.inr gapTrace)
  · exact Or.inr gluing

/-- Source-facing adjacent whole-write theorem.  Every node keeps the actual
component update and whole residual transport, writes the exact adjacent
pair-table split, and either pays the annular kinetic charge or generates a
positive reciprocal pair responsibility already consumed into a physical,
spliced-trace, gap-trace, or complete-gluing native destination. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_pairDuhamelNextScaleWholeWrite
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence step) =
        wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence (step + 1)) +
          scale.sourcePairDuhamelGapTrace step ∧
      ((∃ actual : Ioo (0 : ℝ) (run tail index).nextContact.time.1,
          let initialMass :=
            finiteStateVorticityCoefficientEnstrophy
              (scale.annularModes step)
              (run tail index).contact.physicalState
          let charge := ν.coeff * actual.1 * initialMass
          0 < charge ∧
            charge ≤
              wholeRestartNextKineticDissipationPayment tail index ∧
            (2 * Real.pi) ^ 2 *
                  ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                  charge <
              initialMass -
                finiteStateVorticityCoefficientEnstrophy
                  (scale.annularModes step)
                  ((run tail index).nextContact.prefixReceipt.wholePath
                    ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
        ∃ output ∈ scale.sourceSelfPairOutputSupport step,
          ∃ first ∈ scale.sourceSelfPairFiber step output,
            output ≠ 0 ∧
              0 <
                wholeRestartCrossingSourceSelfVisibleSquareRow
                  tail index crossed output ∧
              (canonicalHalfCriticalComponentCount ν
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) : ℝ) *
                  wholeRestartCrossingSourceSelfVisibleSquareRow
                    tail index crossed output ≤
                ν.coeff * (2 * Real.pi) ^ 2 *
                  wholeStateVorticityGradientMass
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) ∧
              0 < scale.sourcePairDuhamelRateQuantum
                    elapsedBounded step output first ∧
              wholeRestartCrossingFiniteComponentSelfPairOccurrence
                    tail index crossed output first =
                ((canonicalHalfCriticalComponentCount ν
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed) : ℝ)⁻¹ : ℂ) •
                  finiteStateVorticityNonlinearPairContribution
                    (wholeRestartCrossingFiniteCoreState
                      tail index crossed)
                    (first, output - first) ∧
              scale.sourcePairDuhamelNextScaleWholeWriteAt
                elapsedBounded step output first) := by
  dsimp only
  have generated :=
    scale.node_pairDuhamelNextScaleFeedback elapsedBounded step
  dsimp only at generated
  rcases generated with
    ⟨updateEq, residualEq, pairSplit, annular | pair⟩
  · exact ⟨updateEq, residualEq, pairSplit, Or.inl annular⟩
  · refine ⟨updateEq, residualEq, pairSplit, Or.inr ?_⟩
    rcases pair with
      ⟨output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumPos,
        sourcePairEq, nextNative⟩
    exact
      ⟨output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumPos,
        sourcePairEq,
        scale.sourcePairDuhamelNextScaleWholeWriteAt_of_nextScaleNativeAt
          elapsedBounded step output first nextNative quantumPos⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

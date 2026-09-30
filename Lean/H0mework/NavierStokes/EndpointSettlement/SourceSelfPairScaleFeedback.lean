import H0mework.NavierStokes.EndpointSettlement.SourceSelfPairNativeSquareSettlement

/-!
# Scale-to-scale feedback of reduced-core source-self pair responsibility

The strict reduced-core lineage itself now chooses the finite horizon at
which a native pair responsibility must be read: the exact gap between two
adjacent absolute occurrences.  The local tail/index chart is proved to be
the same authoritative whole run at both endpoints, and the generated
pair-Duhamel path trace is the exact write-back complement between them.

Thus a positive reciprocal source leaf reaches the next actual scale state,
is written into the intervening whole pair trace, or has already entered the
complete-gluing native cocycle.  No next occurrence, horizon, path, output,
pair, branch, or nonzero witness is supplied by the caller.
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

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Exact chronological distance between adjacent source-generated scale
occurrences on the authoritative whole restart run. -/
def WholeRestartReducedCoreScaleLineage.nextScaleGap
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : ℕ :=
  scale.absoluteOccurrence (step + 1) -
    scale.absoluteOccurrence step

theorem WholeRestartReducedCoreScaleLineage.nextScaleGap_pos
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    0 < scale.nextScaleGap step := by
  unfold WholeRestartReducedCoreScaleLineage.nextScaleGap
  exact Nat.sub_pos_of_lt
    (scale.absoluteOccurrence_strict (Nat.lt_succ_self step))

theorem WholeRestartReducedCoreScaleLineage.absoluteOccurrence_add_nextScaleGap
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    scale.absoluteOccurrence step + scale.nextScaleGap step =
      scale.absoluteOccurrence (step + 1) := by
  unfold WholeRestartReducedCoreScaleLineage.nextScaleGap
  have occurrenceLe :
      scale.absoluteOccurrence step ≤
        scale.absoluteOccurrence (step + 1) :=
    (scale.absoluteOccurrence_strict
      (Nat.lt_succ_self step)).le
  omega

private theorem wholeRestartPairDuhamelOccurrence_run_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartPairDuhamelOccurrence
        (run initial start) index output first =
      wholeRestartPairDuhamelOccurrence
        initial (start + index) output first := by
  let pairAt := fun current : GeneratedWholeRestartCurrent ν =>
    actualWholePairDuhamelOccurrence
      current.nextContact.prefixReceipt output first
      ⟨current.nextContact.time.1,
        ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
  change pairAt (run (run initial start) index) =
    pairAt (run initial (start + index))
  exact congrArg pairAt (run_run initial start index)

private theorem wholeRestartPairDuhamelTable_run_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start index : ℕ) :
    wholeRestartPairDuhamelTable (run initial start) index =
      wholeRestartPairDuhamelTable initial (start + index) := by
  funext output first
  exact
    wholeRestartPairDuhamelOccurrence_run_eq
      initial start index output first

/-- The adjacent scale endpoints and the intervening generated pair trace
form one exact whole-carrier write-back split on the authoritative run. -/
theorem WholeRestartReducedCoreScaleLineage.pairDuhamel_nextScale_split
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let gap := scale.nextScaleGap step
    wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence step) =
      wholeRestartPairDuhamelTable
          initial (scale.absoluteOccurrence (step + 1)) +
        ((generatedWholeRestartPairDuhamelEffectiveProcess
          tail index).pathTrace 0 gap) 0 := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let gap := scale.nextScaleGap step
  have baseIndex :
      scale.start step + index =
        scale.absoluteOccurrence step := by
    rfl
  have nextIndex :
      scale.start step + (index + gap) =
        scale.absoluteOccurrence (step + 1) := by
    rw [← Nat.add_assoc, baseIndex]
    exact scale.absoluteOccurrence_add_nextScaleGap step
  have split :=
    wholeRestartPairDuhamel_path_split tail index gap
  unfold wholeRestartPairDuhamelPathTable at split
  rw [
    wholeRestartPairDuhamelTable_run_eq
      initial (scale.start step) index,
    wholeRestartPairDuhamelTable_run_eq
      initial (scale.start step) (index + gap),
    baseIndex, nextIndex] at split
  exact split

/-- Native destination of one positive source leaf at the exact next
source-generated scale occurrence.  The actual-pair branch is evaluated at
that next whole-run state; the trace branch retains the exact intervening
whole-carrier path trace. -/
abbrev
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleNativeAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector) : Prop :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let gap := scale.nextScaleGap step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  let sourceSquare :=
    ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
      tail tailElapsedBounded index output first‖ ^ 2
  ((sourceSquare / 4 ≤
        ‖wholeRestartPairDuhamelOccurrence
          tail index output first‖ ^ 2 ∧
      (wholeRestartPairDuhamelOccurrence
            initial (scale.absoluteOccurrence (step + 1))
              output first ≠ 0 ∨
        ((generatedWholeRestartPairDuhamelEffectiveProcess
            tail index).pathTrace 0 gap)
          0 output first ≠ 0)) ∨
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

/-- Specialize the arbitrary-horizon native transport generated by one leaf
to the exact next scale occurrence, with local and global run charts proved
identical. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleNativeAt_of_nativeAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector)
    (native :
      scale.sourcePairDuhamelLeafNativeAt
        elapsedBounded step output first) :
    scale.sourcePairDuhamelNextScaleNativeAt
      elapsedBounded step output first := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelLeafNativeAt at native
  unfold
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelNextScaleNativeAt
  dsimp only at native ⊢
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let gap := scale.nextScaleGap step
  rcases native with actual | gluing
  · left
    refine ⟨actual.1, ?_⟩
    rcases actual.2 gap with future | trace
    · left
      have nextIndex :
          scale.start step + (index + gap) =
            scale.absoluteOccurrence (step + 1) := by
        rw [← Nat.add_assoc]
        change
          scale.absoluteOccurrence step + gap =
            scale.absoluteOccurrence (step + 1)
        exact scale.absoluteOccurrence_add_nextScaleGap step
      unfold wholeRestartPairDuhamelPathTable at future
      have future' :
          wholeRestartPairDuhamelTable
              initial (scale.start step + (index + gap))
                output first ≠ 0 := by
        rw [← wholeRestartPairDuhamelTable_run_eq
          initial (scale.start step) (index + gap)]
        exact future
      rw [nextIndex] at future'
      simpa only [wholeRestartPairDuhamelTable_apply] using future'
    · exact Or.inr trace
  · exact Or.inr gluing

/-- Source-facing scale-to-scale feedback theorem.  Besides the physical
component update and whole residual keep law, every node writes the exact
pair-Duhamel trace between adjacent absolute scale occurrences.  A pair node
then reaches the next actual pair table, that intervening trace, or the
complete-gluing native cocycle with its positive reciprocal quantum intact. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_pairDuhamelNextScaleFeedback
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    let gap := scale.nextScaleGap step
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence step) =
        wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence (step + 1)) +
          ((generatedWholeRestartPairDuhamelEffectiveProcess
            tail index).pathTrace 0 gap) 0 ∧
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
              scale.sourcePairDuhamelNextScaleNativeAt
                elapsedBounded step output first) := by
  dsimp only
  have generated :=
    scale.node_pairDuhamelNativeSquareDisposition elapsedBounded step
  dsimp only at generated
  have pairSplit := scale.pairDuhamel_nextScale_split step
  dsimp only at pairSplit
  rcases generated with
    ⟨updateEq, residualEq, annular | pair⟩
  · exact ⟨updateEq, residualEq, pairSplit, Or.inl annular⟩
  · refine ⟨updateEq, residualEq, pairSplit, Or.inr ?_⟩
    rcases pair with
      ⟨output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumPos,
        sourcePairEq, native⟩
    exact
      ⟨output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumPos,
        sourcePairEq,
        scale.sourcePairDuhamelNextScaleNativeAt_of_nativeAt
          elapsedBounded step output first native⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

import H0mework.NavierStokes.EndpointSettlement.SourceSelfPairLeafExhaustion
import H0mework.NavierStokes.EndpointSettlement.FinitePrefixQuantitativeSettlement

/-!
# Native square settlement of complete reduced-core source-self pairs

The complete finite source-self pair carrier is now consumed without making
the scalar visible quotient authoritative.  A nonzero primitive leaf carries
its source-generated Duhamel rate quantum and, independently of whether its
aggregate output is visible, remains in the actual pair future/path process
or enters the complete-gluing native cocycle.

Finite Cauchy on the source-generated pair fiber also transports the complete
aggregate source-Duhamel square into the leaf ledger with exactly the actual
spectral multiplicity.  No support, output, pair, branch, horizon, nonzero
witness, or multiplicity bound is accepted from the caller.
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

private theorem finite_norm_sum_sq_le_card_mul_sum_norm_sq
    {ι E : Type*}
    [DecidableEq ι]
    [NormedAddCommGroup E]
    (indices : Finset ι)
    (value : ι → E) :
    ‖∑ index ∈ indices, value index‖ ^ 2 ≤
      (indices.card : ℝ) *
        ∑ index ∈ indices, ‖value index‖ ^ 2 := by
  have normLe := norm_sum_le indices value
  have squareLe :
      ‖∑ index ∈ indices, value index‖ ^ 2 ≤
        (∑ index ∈ indices, ‖value index‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun index _indexMem =>
        norm_nonneg (value index))).2 normLe
  exact squareLe.trans
    (sq_sum_le_card_mul_sum_sq
      (s := indices) (f := fun index => ‖value index‖))

/-- Exact rate of the complete source-self Duhamel aggregate at one
source-generated output, before it is compared with any scalar visible
quotient. -/
def WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateRow
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output : IntegerWavevector) : ℝ :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  ‖∑ first ∈ scale.sourceSelfPairFiber step output,
      wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
        tail tailElapsedBounded index output first‖ ^ 2 /
    (16 * (run tail index).nextContact.time.1)

/-- Complete aggregate source-Duhamel rate on the actual nonzero output
support of one reduced-core node. -/
def WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateLedger
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) : ℝ :=
  ∑ output ∈ scale.sourceSelfPairOutputSupport step,
    scale.sourceSelfPairDuhamelAggregateRateRow
      elapsedBounded step output

theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateRow_nonneg
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output : IntegerWavevector) :
    0 ≤ scale.sourceSelfPairDuhamelAggregateRateRow
      elapsedBounded step output := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateRow
  dsimp only
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (run _ _).nextContact.time_pos.le)

theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateLedger_nonneg
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    0 ≤ scale.sourceSelfPairDuhamelAggregateRateLedger
      elapsedBounded step := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateLedger
  exact Finset.sum_nonneg fun output _outputMem =>
    scale.sourceSelfPairDuhamelAggregateRateRow_nonneg
      elapsedBounded step output

/-- Finite Cauchy on one actual source-generated pair fiber.  This is the
precise consume-before-quotient bridge from the aggregate Duhamel square to
the complete leaf-square ledger. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateRow_le_fiberLedger
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output : IntegerWavevector) :
    scale.sourceSelfPairDuhamelAggregateRateRow
        elapsedBounded step output ≤
      (scale.sourceSelfPairFiber step output).card *
        ∑ first ∈ scale.sourceSelfPairFiber step output,
          scale.sourcePairDuhamelRateQuantum
            elapsedBounded step output first := by
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  let fiber := scale.sourceSelfPairFiber step output
  let occurrence := fun first : IntegerWavevector =>
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
      tail tailElapsedBounded index output first
  have durationPos :
      0 < 16 * (run tail index).nextContact.time.1 :=
    mul_pos (by norm_num) (run tail index).nextContact.time_pos
  have cauchy :
      ‖∑ first ∈ fiber, occurrence first‖ ^ 2 ≤
        (fiber.card : ℝ) *
          ∑ first ∈ fiber, ‖occurrence first‖ ^ 2 :=
    finite_norm_sum_sq_le_card_mul_sum_norm_sq fiber occurrence
  unfold
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateRow
  dsimp only
  unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum
  dsimp only
  calc
    ‖∑ first ∈ fiber, occurrence first‖ ^ 2 /
          (16 * (run tail index).nextContact.time.1) ≤
        ((fiber.card : ℝ) *
            ∑ first ∈ fiber, ‖occurrence first‖ ^ 2) /
          (16 * (run tail index).nextContact.time.1) :=
      div_le_div_of_nonneg_right cauchy durationPos.le
    _ =
        (fiber.card : ℝ) *
          ∑ first ∈ fiber,
            (‖occurrence first‖ ^ 2 / 16) /
              (run tail index).nextContact.time.1 := by
      calc
        ((fiber.card : ℝ) *
              ∑ first ∈ fiber, ‖occurrence first‖ ^ 2) /
            (16 * (run tail index).nextContact.time.1) =
          (fiber.card : ℝ) *
            ((∑ first ∈ fiber, ‖occurrence first‖ ^ 2) /
              (16 * (run tail index).nextContact.time.1)) := by
          ring
        _ =
          (fiber.card : ℝ) *
            ∑ first ∈ fiber,
              ‖occurrence first‖ ^ 2 /
                (16 * (run tail index).nextContact.time.1) := by
          rw [Finset.sum_div]
        _ =
          (fiber.card : ℝ) *
            ∑ first ∈ fiber,
              (‖occurrence first‖ ^ 2 / 16) /
                (run tail index).nextContact.time.1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro first _firstMem
          rw [div_div]

/-- The complete aggregate source-Duhamel square is captured by the complete
leaf ledger with one, and only one, source-generated spectral multiplicity. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateLedger_le
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    scale.sourceSelfPairDuhamelAggregateRateLedger
        elapsedBounded step ≤
      (scale.sourceSelfPairModes step).card *
        scale.sourcePairDuhamelRateLedger elapsedBounded step := by
  unfold
    WholeRestartReducedCoreScaleLineage.sourceSelfPairDuhamelAggregateRateLedger
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateLedger
  calc
    (∑ output ∈ scale.sourceSelfPairOutputSupport step,
        scale.sourceSelfPairDuhamelAggregateRateRow
          elapsedBounded step output) ≤
        ∑ output ∈ scale.sourceSelfPairOutputSupport step,
          (scale.sourceSelfPairFiber step output).card *
            ∑ first ∈ scale.sourceSelfPairFiber step output,
              scale.sourcePairDuhamelRateQuantum
                elapsedBounded step output first := by
      exact Finset.sum_le_sum fun output _outputMem =>
        scale.sourceSelfPairDuhamelAggregateRateRow_le_fiberLedger
          elapsedBounded step output
    _ ≤
        ∑ output ∈ scale.sourceSelfPairOutputSupport step,
          (scale.sourceSelfPairModes step).card *
            ∑ first ∈ scale.sourceSelfPairFiber step output,
              scale.sourcePairDuhamelRateQuantum
                elapsedBounded step output first := by
      exact Finset.sum_le_sum fun output _outputMem => by
        have fiberCard :
            ((scale.sourceSelfPairFiber step output).card : ℝ) ≤
              (scale.sourceSelfPairModes step).card := by
          exact_mod_cast
            Finset.card_le_card
              (Finset.filter_subset
                (fun first =>
                  output - first ∈ scale.sourceSelfPairModes step)
                (scale.sourceSelfPairModes step))
        exact mul_le_mul_of_nonneg_right fiberCard
          (Finset.sum_nonneg fun first _firstMem =>
            scale.sourcePairDuhamelRateQuantum_nonneg
              elapsedBounded step output first)
    _ =
        (scale.sourceSelfPairModes step).card *
          ∑ output ∈ scale.sourceSelfPairOutputSupport step,
            ∑ first ∈ scale.sourceSelfPairFiber step output,
              scale.sourcePairDuhamelRateQuantum
                elapsedBounded step output first := by
      rw [Finset.mul_sum]

/-- Every nonzero primitive source leaf carries a positive exact rate quantum
and a native future/path or complete-gluing continuation.  Visibility of the
aggregate output is not used as a terminal branch. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum_pos_and_nativeAt_of_sourcePair_ne_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (sourcePairNonzero :
      let tail := run initial (scale.start step)
      let index := scale.relativeIndex step
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index (scale.crossed step) output first ≠ 0) :
    0 < scale.sourcePairDuhamelRateQuantum
          elapsedBounded step output first ∧
      scale.sourcePairDuhamelLeafNativeAt
        elapsedBounded step output first := by
  dsimp only at sourcePairNonzero
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  let generatedCrossed :
      wholeRestartHalfCriticalCrossed tail index :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      tail tailElapsedBounded index
  have crossedEq : generatedCrossed = scale.crossed step :=
    Subsingleton.elim _ _
  have generatedSourcePairNonzero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index generatedCrossed output first ≠ 0 := by
    simpa [crossedEq] using sourcePairNonzero
  have exhaustion :=
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeNativeExhaustion
      tail tailElapsedBounded index output first outputNonzero
        generatedSourcePairNonzero
  have durationPos :
      0 < (run tail index).nextContact.time.1 :=
    (run tail index).nextContact.time_pos
  constructor
  · unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum
    dsimp only
    exact div_pos (div_pos exhaustion.1 (by norm_num)) durationPos
  · unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelLeafNativeAt
    dsimp only
    rcases exhaustion.2 with actualLarge | gluing
    · left
      refine ⟨actualLarge, ?_⟩
      have sourceQuarterPos :
          0 <
            ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
              tail tailElapsedBounded index output first‖ ^ 2 / 4 :=
        div_pos exhaustion.1 (by norm_num)
      have actualSquarePos :
          0 <
            ‖wholeRestartPairDuhamelOccurrence
              tail index output first‖ ^ 2 :=
        sourceQuarterPos.trans_le actualLarge
      have actualNonzero :
          wholeRestartPairDuhamelOccurrence
            tail index output first ≠ 0 := by
        intro actualZero
        rw [actualZero] at actualSquarePos
        simp at actualSquarePos
      intro steps
      exact
        wholeRestartPairDuhamelOccurrence_ne_zero_future_or_pathTrace
          tail index output first steps actualNonzero
    · exact Or.inr gluing

/-- Source-only native quantitative node disposition.  A zero whole
nonlinearity writes the existing annular kinetic payment.  Otherwise the
source-selected reciprocal-count pair belongs to the complete generated
fiber, carries a positive Duhamel rate quantum, and natively survives the
pair quotient. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_pairDuhamelNativeSquareDisposition
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
              scale.sourcePairDuhamelLeafNativeAt
                elapsedBounded step output first) := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let crossed := scale.crossed step
  have generated :=
    scale.node_pairQuantitativeSettlement elapsedBounded step
  dsimp only at generated
  rcases generated with
    ⟨updateEq, residualEq, annular | pair⟩
  · exact ⟨updateEq, residualEq, Or.inl annular⟩
  · refine ⟨updateEq, residualEq, Or.inr ?_⟩
    rcases pair with
      ⟨output, first, outputNonzero, outputSquarePos,
        outputSquareCountLe, sourcePairSquarePos, sourcePairEq,
        _settlement⟩
    have sourcePairNonzero :
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
          tail index crossed output first ≠ 0 := by
      intro sourcePairZero
      rw [sourcePairZero] at sourcePairSquarePos
      simp at sourcePairSquarePos
    have outputMem :
        output ∈ scale.sourceSelfPairOutputSupport step := by
      by_contra outputNotMem
      exact sourcePairNonzero
        (scale.sourceSelfPairOccurrence_eq_zero_of_output_not_mem_support
          step output outputNotMem first)
    have firstMem :
        first ∈ scale.sourceSelfPairFiber step output := by
      by_contra firstNotMem
      exact sourcePairNonzero
        (scale.sourceSelfPairOccurrence_eq_zero_of_first_not_mem_fiber
          step output first firstNotMem)
    have quantumNative :=
      scale.sourcePairDuhamelRateQuantum_pos_and_nativeAt_of_sourcePair_ne_zero
        elapsedBounded step output first outputNonzero sourcePairNonzero
    exact
      ⟨output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumNative.1,
        sourcePairEq, quantumNative.2⟩

/-- Finite-prefix source settlement on the strict reduced-core lineage.
Annular nodes are charged once to the existing whole kinetic telescope.
Every zero-charge pair node retains its reciprocal-count occurrence, positive
source-Duhamel square rate, and native future/path or gluing continuation.
The caller selects neither the branch nor any coordinate. -/
theorem
    WholeRestartReducedCoreScaleLineage.finitePrefix_pairDuhamelNativeSquareSettlement
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (length : ℕ) :
    ∃ kineticCharge : ℕ → ℝ,
      (∀ step < length,
        let tail := run initial (scale.start step)
        let index := scale.relativeIndex step
        let crossed := scale.crossed step
        run tail (wholeRestartComponentGluingNativeUpdate index) =
            (run tail index).next ∧
          wholeRestartComponentGluingResidualTail tail (index + 1) =
            wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail tail index) ∧
          0 ≤ kineticCharge step ∧
          ((0 < kineticCharge step ∧
            kineticCharge step ≤
              wholeRestartNextKineticDissipationPayment
                initial (scale.absoluteOccurrence step) ∧
            ∃ actual :
                Ioo (0 : ℝ) (run tail index).nextContact.time.1,
              let initialMass :=
                finiteStateVorticityCoefficientEnstrophy
                  (scale.annularModes step)
                  (run tail index).contact.physicalState
              kineticCharge step =
                  ν.coeff * actual.1 * initialMass ∧
                (2 * Real.pi) ^ 2 *
                      ((scale.requestedRadius step + 1 : ℕ) : ℝ) ^ 2 *
                      kineticCharge step <
                  initialMass -
                    finiteStateVorticityCoefficientEnstrophy
                      (scale.annularModes step)
                      ((run tail index).nextContact.prefixReceipt.wholePath
                        ⟨actual.1, actual.2.1.le, actual.2.2.le⟩)) ∨
          (kineticCharge step = 0 ∧
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
                  scale.sourcePairDuhamelLeafNativeAt
                    elapsedBounded step output first))) ∧
      (∑ step ∈ Finset.range length, kineticCharge step) ≤
        puncturedWholeVorticityKineticMass
          initial.contact.physicalState := by
  obtain ⟨kineticCharge, perStep, kineticBound⟩ :=
    scale.finitePrefix_pairQuantitativeSettlement elapsedBounded length
  refine ⟨kineticCharge, ?_, kineticBound⟩
  intro step stepLt
  have generated := perStep step stepLt
  dsimp only at generated ⊢
  rcases generated with
    ⟨updateEq, residualEq, chargeNonneg, annular | pair⟩
  · exact
      ⟨updateEq, residualEq, chargeNonneg, Or.inl annular⟩
  · refine
      ⟨updateEq, residualEq, chargeNonneg, Or.inr ?_⟩
    rcases pair with
      ⟨chargeZero, output, first, outputNonzero, outputSquarePos,
        outputSquareCountLe, sourcePairSquarePos, sourcePairEq,
        _settlement⟩
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    let crossed := scale.crossed step
    have sourcePairNonzero :
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
          tail index crossed output first ≠ 0 := by
      intro sourcePairZero
      rw [sourcePairZero] at sourcePairSquarePos
      simp at sourcePairSquarePos
    have outputMem :
        output ∈ scale.sourceSelfPairOutputSupport step := by
      by_contra outputNotMem
      exact sourcePairNonzero
        (scale.sourceSelfPairOccurrence_eq_zero_of_output_not_mem_support
          step output outputNotMem first)
    have firstMem :
        first ∈ scale.sourceSelfPairFiber step output := by
      by_contra firstNotMem
      exact sourcePairNonzero
        (scale.sourceSelfPairOccurrence_eq_zero_of_first_not_mem_fiber
          step output first firstNotMem)
    have quantumNative :=
      scale.sourcePairDuhamelRateQuantum_pos_and_nativeAt_of_sourcePair_ne_zero
        elapsedBounded step output first outputNonzero sourcePairNonzero
    exact
      ⟨chargeZero, output, outputMem, first, firstMem, outputNonzero,
        outputSquarePos, outputSquareCountLe, quantumNative.1,
        sourcePairEq, quantumNative.2⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

import H0mework.NavierStokes.EndpointSettlement.PairDuhamelQuantumCascade

/-!
# Complete source-self pair-leaf exhaustion

The reduced-core source now exposes its complete finite `output × first`
domain before pair aggregation.  Every leaf is computed from the actual
finite core.  Zero leaves close faithfully; every nonzero leaf enters the
existing same-occurrence visible payment or native pair/gluing redirect.

The output support, pair fiber, branch, and nonzero witness are not supplied
by the caller.  The amplitude component count and the spectral pair
multiplicity remain distinct.
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
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
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

/-- Actual finite Fourier inventory of one source-generated reduced-core
node. -/
def WholeRestartReducedCoreScaleLineage.sourceSelfPairModes
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : Finset IntegerWavevector :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  wholeRestartCrossingFiniteCoreModes tail index (scale.crossed step)

/-- Nonzero output inventory of the complete ordered-pair table. -/
def WholeRestartReducedCoreScaleLineage.sourceSelfPairOutputSupport
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ) : Finset IntegerWavevector :=
  (finiteVorticityPairOutputSupport
    (scale.sourceSelfPairModes step)).erase 0

/-- Complete first-coordinate fiber at one generated output.  The second
coordinate is definitionally `output - first`. -/
def WholeRestartReducedCoreScaleLineage.sourceSelfPairFiber
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    (output : IntegerWavevector) : Finset IntegerWavevector :=
  (scale.sourceSelfPairModes step).filter fun first =>
    output - first ∈ scale.sourceSelfPairModes step

@[simp] theorem WholeRestartReducedCoreScaleLineage.mem_sourceSelfPairFiber_iff
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    (output first : IntegerWavevector) :
    first ∈ scale.sourceSelfPairFiber step output ↔
      first ∈ scale.sourceSelfPairModes step ∧
        output - first ∈ scale.sourceSelfPairModes step := by
  simp [WholeRestartReducedCoreScaleLineage.sourceSelfPairFiber]

/-- Zero total frequency is silent leafwise by the transverse law of the
actual finite core, before any pair aggregation. -/
theorem wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_zero_of_output_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector)
    (outputZero : output = 0) :
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
        initial index crossed output first = 0 := by
  subst output
  rw [
    wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_core_smul]
  let core :=
    wholeRestartCrossingFiniteCoreState initial index crossed
  have coreTransverse : WholeStateTransverse core :=
    wholeStateTransverse_sharpSupportProjection
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (run initial index).contact.physicalState
      (run initial index).contact.transverse
  have secondWave : (0 : IntegerWavevector) - first = waveNeg first := by
    ext coordinate
    simp [waveNeg]
  have stateDot :
      complexWavevector ((0 : IntegerWavevector) - first) ⬝ᵥ
          core first = 0 := by
    rw [secondWave, complexWavevector_waveNeg]
    simpa using congrArg Neg.neg (coreTransverse first)
  have velocityDot :
      complexWavevector ((0 : IntegerWavevector) - first) ⬝ᵥ
          finiteStateVelocityCoefficient core first = 0 := by
    rw [secondWave, complexWavevector_waveNeg, neg_dotProduct]
    simpa [finiteStateVelocityCoefficient] using
      congrArg Neg.neg
        (complexWavevector_dot_biotSavartVelocityCoefficient
          first (core first))
  unfold finiteStateVorticityNonlinearPairContribution
  rw [stateDot, velocityDot]
  simp

/-- A first coordinate outside the generated fiber contributes zero.  Thus
the finite fiber is an exact carrier, not a caller-provided cutoff. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairOccurrence_eq_zero_of_first_not_mem_fiber
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    (output first : IntegerWavevector)
    (firstNotMem : first ∉ scale.sourceSelfPairFiber step output) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
      tail index (scale.crossed step) output first = 0 := by
  dsimp only
  rw [
    wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_core_smul]
  by_cases firstMem : first ∈ scale.sourceSelfPairModes step
  · have secondOutside :
        output - first ∉ scale.sourceSelfPairModes step := by
      intro secondMem
      exact firstNotMem
        ((scale.mem_sourceSelfPairFiber_iff step output first).2
          ⟨firstMem, secondMem⟩)
    have secondOutsideCore :
        output - first ∉
          wholeRestartCrossingFiniteCoreModes
            (run initial (scale.start step))
            (scale.relativeIndex step) (scale.crossed step) := by
      simpa only [
        WholeRestartReducedCoreScaleLineage.sourceSelfPairModes]
        using secondOutside
    apply smul_eq_zero.mpr
    right
    apply finiteStateVorticityNonlinearPairContribution_zero_second
    rw [wholeRestartCrossingFiniteCoreState_eq_sharpSupportProjection]
    simp [complexSharpSupportProjection_apply, secondOutsideCore]
  · apply smul_eq_zero.mpr
    right
    apply finiteStateVorticityNonlinearPairContribution_zero_first
    have firstOutsideCore :
        first ∉
          wholeRestartCrossingFiniteCoreModes
            (run initial (scale.start step))
            (scale.relativeIndex step) (scale.crossed step) := by
      simpa only [
        WholeRestartReducedCoreScaleLineage.sourceSelfPairModes]
        using firstMem
    rw [wholeRestartCrossingFiniteCoreState_eq_sharpSupportProjection]
    simp [complexSharpSupportProjection_apply, firstOutsideCore]

/-- Every primitive occurrence outside the generated nonzero output support
is zero.  The erased zero output is discharged by transversality, not by a
coverage premise. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourceSelfPairOccurrence_eq_zero_of_output_not_mem_support
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    (output : IntegerWavevector)
    (outputNotMem : output ∉ scale.sourceSelfPairOutputSupport step)
    (first : IntegerWavevector) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
      tail index (scale.crossed step) output first = 0 := by
  dsimp only
  by_cases outputZero : output = 0
  · exact
      wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_zero_of_output_eq_zero
        (run initial (scale.start step)) (scale.relativeIndex step)
          (scale.crossed step) output first outputZero
  · have outputNotFull :
        output ∉
          finiteVorticityPairOutputSupport
            (scale.sourceSelfPairModes step) := by
      intro outputMem
      exact outputNotMem
        (Finset.mem_erase.mpr ⟨outputZero, outputMem⟩)
    have firstNotMem :
        first ∉ scale.sourceSelfPairFiber step output := by
      intro firstMem
      have fiberSpec :=
        (scale.mem_sourceSelfPairFiber_iff step output first).mp
          firstMem
      apply outputNotFull
      unfold finiteVorticityPairOutputSupport
      apply Finset.mem_image.mpr
      refine
        ⟨(first, output - first),
          Finset.mem_product.mpr fiberSpec, ?_⟩
      simp
    exact
      scale.sourceSelfPairOccurrence_eq_zero_of_first_not_mem_fiber
        step output first firstNotMem

/-- The generated finite fiber reconstructs the complete primitive
source-self output row exactly. -/
theorem
    WholeRestartReducedCoreScaleLineage.sum_sourceSelfPairFiber_eq_selfRow
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (step : ℕ)
    (output : IntegerWavevector) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    ∑ first ∈ scale.sourceSelfPairFiber step output,
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
          tail index (scale.crossed step) output first =
      wholeRestartCrossingFiniteComponentSelfRow
        tail index (scale.crossed step) output := by
  dsimp only
  calc
    (∑ first ∈ scale.sourceSelfPairFiber step output,
        wholeRestartCrossingFiniteComponentSelfPairOccurrence
          (run initial (scale.start step)) (scale.relativeIndex step)
            (scale.crossed step) output first) =
        ∑' first : IntegerWavevector,
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
            (run initial (scale.start step)) (scale.relativeIndex step)
              (scale.crossed step) output first := by
      symm
      apply tsum_eq_sum
      intro first firstNotMem
      exact
        scale.sourceSelfPairOccurrence_eq_zero_of_first_not_mem_fiber
          step output first firstNotMem
    _ =
        wholeRestartCrossingFiniteComponentSelfRow
          (run initial (scale.start step)) (scale.relativeIndex step)
            (scale.crossed step) output :=
      tsum_wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq
        (run initial (scale.start step)) (scale.relativeIndex step)
          (scale.crossed step) output

/-- Concrete native destination of one nonzero source-self pair leaf. -/
abbrev WholeRestartReducedCoreScaleLineage.sourcePairDuhamelLeafNativeAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector) : Prop :=
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  let sourceSquare :=
    ‖wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence
      tail tailElapsedBounded index output first‖ ^ 2
  ((sourceSquare / 4 ≤
        ‖wholeRestartPairDuhamelOccurrence
          tail index output first‖ ^ 2 ∧
      ∀ steps : ℕ,
        wholeRestartPairDuhamelPathTable
              tail index steps output first ≠ 0 ∨
          ((generatedWholeRestartPairDuhamelEffectiveProcess
              tail index).pathTrace 0 steps)
            0 output first ≠ 0) ∨
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

theorem WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum_nonneg
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector) :
    0 ≤ scale.sourcePairDuhamelRateQuantum
      elapsedBounded step output first := by
  unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum
  dsimp only
  exact div_nonneg (by positivity) (run _ _).nextContact.time_pos.le

/-- A faithfully zero primitive occurrence writes zero to its exact causal
rate coordinate. -/
theorem
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum_eq_zero_of_sourcePair_eq_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (sourcePairZero :
      let tail := run initial (scale.start step)
      let index := scale.relativeIndex step
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index (scale.crossed step) output first = 0) :
    scale.sourcePairDuhamelRateQuantum
      elapsedBounded step output first = 0 := by
  dsimp only at sourcePairZero
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
  have generatedSourcePairZero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index generatedCrossed output first = 0 := by
    simpa [crossedEq] using sourcePairZero
  unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum
  dsimp only
  rw [
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamelOccurrence_eq_gain
      tail tailElapsedBounded index ⟨output, outputNonzero⟩ first]
  rw [generatedSourcePairZero, smul_zero]
  simp

/-- Total exact source-self pair-Duhamel rate over the complete generated
finite leaf domain of one reduced-core node. -/
def WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateLedger
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) : ℝ :=
  ∑ output ∈ scale.sourceSelfPairOutputSupport step,
    ∑ first ∈ scale.sourceSelfPairFiber step output,
      scale.sourcePairDuhamelRateQuantum
        elapsedBounded step output first

theorem WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateLedger_nonneg
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    0 ≤ scale.sourcePairDuhamelRateLedger elapsedBounded step := by
  unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateLedger
  exact Finset.sum_nonneg fun output _outputMem =>
    Finset.sum_nonneg fun first _firstMem =>
      scale.sourcePairDuhamelRateQuantum_nonneg
        elapsedBounded step output first

/-- Every leaf of the source-generated finite pair domain is faithfully zero
or carries a positive same-occurrence rate quantum into the visible row or a
native pair/gluing write.  The same theorem retains the actual node update
and whole residual keep law. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_sourceSelfPairLeafwiseExhaustion
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
      ∀ output ∈ scale.sourceSelfPairOutputSupport step,
        ∀ first ∈ scale.sourceSelfPairFiber step output,
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
                tail index crossed output first = 0 ∨
            (0 < scale.sourcePairDuhamelRateQuantum
                elapsedBounded step output first ∧
              (scale.sourcePairDuhamelRateQuantum
                    elapsedBounded step output first ≤
                  wholeRestartExactCausalNonlinearSquareRow
                    tail index output ∨
                scale.sourcePairDuhamelLeafNativeAt
                  elapsedBounded step output first)) := by
  dsimp only
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  let crossed := scale.crossed step
  let tailElapsedBounded :
      BddAbove (Set.range (elapsedTime tail)) :=
    elapsedTime_run_bddAbove initial elapsedBounded (scale.start step)
  refine
    ⟨wholeRestartComponentGluingNativeUpdate_physical tail index,
      wholeRestartComponentGluingResidual_transport tail index, ?_⟩
  intro output outputMem first _firstMem
  by_cases sourcePairZero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index crossed output first = 0
  · exact Or.inl sourcePairZero
  right
  have outputNonzero : output ≠ 0 :=
    (Finset.mem_erase.mp outputMem).1
  let generatedCrossed :
      wholeRestartHalfCriticalCrossed tail index :=
    elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      tail tailElapsedBounded index
  have crossedEq : generatedCrossed = crossed :=
    Subsingleton.elim _ _
  have generatedSourcePairNonzero :
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        tail index generatedCrossed output first ≠ 0 := by
    simpa [crossedEq] using sourcePairZero
  have exhaustion :=
    wholeRestartBoundedElapsedCrossingSourceSelfPairDuhamel_quantitativeVisibleOrNativeExhaustion
      tail tailElapsedBounded index output first outputNonzero
        generatedSourcePairNonzero
  simpa only [
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateQuantum,
    WholeRestartReducedCoreScaleLineage.sourcePairDuhamelLeafNativeAt]
    using exhaustion

/-- The complete source-self pair table of one generated node is exhausted
without a caller-selected coordinate.  If no leaf enters the native
pair/gluing continuation, the whole finite rate ledger is paid by the exact
same-receipt causal payment, with the spectral fiber multiplicity explicit.
The theorem retains the actual node update and whole residual keep law. -/
theorem
    WholeRestartReducedCoreScaleLineage.node_sourceSelfPairRateLedgerExhaustion
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (step : ℕ) :
    let tail := run initial (scale.start step)
    let index := scale.relativeIndex step
    run tail (wholeRestartComponentGluingNativeUpdate index) =
        (run tail index).next ∧
      wholeRestartComponentGluingResidualTail tail (index + 1) =
        wholeRestartComponentGluingResidualTailKeep
          (wholeRestartComponentGluingResidualTail tail index) ∧
      (scale.sourcePairDuhamelRateLedger elapsedBounded step ≤
          (scale.sourceSelfPairModes step).card *
            wholeRestartExactCausalNonlinearSquarePayment tail index ∨
        ∃ output ∈ scale.sourceSelfPairOutputSupport step,
          ∃ first ∈ scale.sourceSelfPairFiber step output,
            0 < scale.sourcePairDuhamelRateQuantum
                elapsedBounded step output first ∧
              scale.sourcePairDuhamelLeafNativeAt
                elapsedBounded step output first) := by
  dsimp only
  have leafwise :=
    scale.node_sourceSelfPairLeafwiseExhaustion elapsedBounded step
  dsimp only at leafwise
  rcases leafwise with ⟨updateEq, residualEq, everyLeaf⟩
  refine ⟨updateEq, residualEq, ?_⟩
  by_cases nativeExists :
      ∃ output ∈ scale.sourceSelfPairOutputSupport step,
        ∃ first ∈ scale.sourceSelfPairFiber step output,
          0 < scale.sourcePairDuhamelRateQuantum
              elapsedBounded step output first ∧
            scale.sourcePairDuhamelLeafNativeAt
              elapsedBounded step output first
  · exact Or.inr nativeExists
  left
  let tail := run initial (scale.start step)
  let index := scale.relativeIndex step
  have perLeaf
      (output : IntegerWavevector)
      (outputMem : output ∈ scale.sourceSelfPairOutputSupport step)
      (first : IntegerWavevector)
      (firstMem : first ∈ scale.sourceSelfPairFiber step output) :
      scale.sourcePairDuhamelRateQuantum
          elapsedBounded step output first ≤
        wholeRestartExactCausalNonlinearSquareRow tail index output := by
    rcases everyLeaf output outputMem first firstMem with
      sourcePairZero | ⟨quantumPos, visible | native⟩
    · have outputNonzero : output ≠ 0 :=
        (Finset.mem_erase.mp outputMem).1
      have quantumZero :=
        scale.sourcePairDuhamelRateQuantum_eq_zero_of_sourcePair_eq_zero
          elapsedBounded step output first outputNonzero sourcePairZero
      rw [quantumZero]
      exact
        wholeRestartExactCausalNonlinearSquareRow_nonneg
          tail index output
    · exact visible
    · exact
        (nativeExists
          ⟨output, outputMem, first, firstMem, quantumPos, native⟩).elim
  have perOutput
      (output : IntegerWavevector)
      (outputMem : output ∈ scale.sourceSelfPairOutputSupport step) :
      (∑ first ∈ scale.sourceSelfPairFiber step output,
          scale.sourcePairDuhamelRateQuantum
            elapsedBounded step output first) ≤
        (scale.sourceSelfPairModes step).card *
          wholeRestartExactCausalNonlinearSquareRow tail index output := by
    have fiberCard :
        ((scale.sourceSelfPairFiber step output).card : ℝ) ≤
          (scale.sourceSelfPairModes step).card := by
      exact_mod_cast
        Finset.card_le_card
          (Finset.filter_subset
            (fun first =>
              output - first ∈ scale.sourceSelfPairModes step)
            (scale.sourceSelfPairModes step))
    calc
      (∑ first ∈ scale.sourceSelfPairFiber step output,
          scale.sourcePairDuhamelRateQuantum
            elapsedBounded step output first) ≤
          ∑ first ∈ scale.sourceSelfPairFiber step output,
            wholeRestartExactCausalNonlinearSquareRow
              tail index output := by
        exact Finset.sum_le_sum fun first firstMem =>
          perLeaf output outputMem first firstMem
      _ =
          (scale.sourceSelfPairFiber step output).card *
            wholeRestartExactCausalNonlinearSquareRow
              tail index output := by
        simp
      _ ≤
          (scale.sourceSelfPairModes step).card *
            wholeRestartExactCausalNonlinearSquareRow
              tail index output :=
        mul_le_mul_of_nonneg_right fiberCard
          (wholeRestartExactCausalNonlinearSquareRow_nonneg
            tail index output)
  have supportRowsLe :
      (∑ output ∈ scale.sourceSelfPairOutputSupport step,
          wholeRestartExactCausalNonlinearSquareRow
            tail index output) ≤
        wholeRestartExactCausalNonlinearSquarePayment tail index := by
    unfold wholeRestartExactCausalNonlinearSquarePayment
    exact
      (summable_wholeRestartExactCausalNonlinearSquareRow
        tail index).sum_le_tsum
          (scale.sourceSelfPairOutputSupport step)
          (fun output _outputMem =>
            wholeRestartExactCausalNonlinearSquareRow_nonneg
              tail index output)
  unfold WholeRestartReducedCoreScaleLineage.sourcePairDuhamelRateLedger
  calc
    (∑ output ∈ scale.sourceSelfPairOutputSupport step,
        ∑ first ∈ scale.sourceSelfPairFiber step output,
          scale.sourcePairDuhamelRateQuantum
            elapsedBounded step output first) ≤
        ∑ output ∈ scale.sourceSelfPairOutputSupport step,
          (scale.sourceSelfPairModes step).card *
            wholeRestartExactCausalNonlinearSquareRow
              tail index output := by
      exact Finset.sum_le_sum fun output outputMem =>
        perOutput output outputMem
    _ =
        (scale.sourceSelfPairModes step).card *
          (∑ output ∈ scale.sourceSelfPairOutputSupport step,
            wholeRestartExactCausalNonlinearSquareRow
              tail index output) := by
      rw [Finset.mul_sum]
    _ ≤
        (scale.sourceSelfPairModes step).card *
          wholeRestartExactCausalNonlinearSquarePayment tail index :=
      mul_le_mul_of_nonneg_left supportRowsLe (by positivity)

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

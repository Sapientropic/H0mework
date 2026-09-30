import H0mework.NavierStokes.EndpointWork.SourceAnchorNativePairExhaustion
import H0mework.NavierStokes.EndpointTransport.PairDuhamelMacroWrite

/-!
# Source-anchor native pairs written by the endpoint macro

The endpoint causal macro already writes a source-selected cofinal
pair-Duhamel tail.  A positive endpoint kinetic atom, however, selects its
negative anchored work at an arbitrary actual old-run index.  This module
writes the complete native pair-Duhamel tail, beginning at old-run index
zero, by that identical endpoint event.

The decisive consume-before-quotient step is algebraic.  If one symmetric
anchored direct work is negative, its two actual pair-Duhamel coordinates
cannot both vanish.  Thus the source-selected negative direct-work branch
survives as a nonzero coordinate of the endpoint-written whole pair carrier,
while the already generated ordinary/reflected next-or-trace responsibility
is retained on the same frame.  The physical projection remains the endpoint
step's actual unforced `next`.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorCollectiveWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess.WholeRestartAnchoredReflectedPairFrame
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredMixedWorkNativeCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairExhaustion
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Complete native pair tail in the endpoint write -/

/-- Whole endpoint responsibility retaining the already aligned
component/kinetic stream and every actual pair-Duhamel table of the old run.
No cofinal reindexing is needed for the source-selected anchored frame. -/
abbrev WholeRestartEndpointFullPairResponsibility :=
  WholeRestartEndpointAlignedResponsibilityTail ×
    WholeRestartPairDuhamelTail

/-- Before the endpoint write, the whole aligned stream and complete native
pair tail are pending. -/
def wholeRestartEndpointFullPairMacroPending
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointFullPairResponsibility
  | accumulationRead =>
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartPairDuhamelTail initial 0 0)
  | endpointWritten => 0

/-- The identical endpoint event writes both complete carriers. -/
def wholeRestartEndpointFullPairMacroTraceLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointFullPairResponsibility
  | accumulationRead => 0
  | endpointWritten =>
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartPairDuhamelTail initial 0 0)

/-- The endpoint event consumes the pending carrier because it writes that
carrier exactly into the trace ledger. -/
def wholeRestartEndpointFullPairMacroKeep :
    WholeRestartEndpointFullPairResponsibility →ₗ[ℂ]
      WholeRestartEndpointFullPairResponsibility :=
  0

/-- Effective residual process of the full native-pair endpoint write. -/
def generatedWholeRestartEndpointFullPairMacroEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess ℂ
      WholeRestartEndpointFullPairResponsibility
      WholeRestartEndpointComponentMacroPhase where
  target := 0
  keep := wholeRestartEndpointFullPairMacroKeep
  residual :=
    wholeRestartEndpointFullPairMacroPending initial elapsedBounded
  update := wholeRestartEndpointComponentMacroUpdate
  residual_transport_law := by
    intro phase
    cases phase <;> rfl

/-- The forced endpoint trace is the entire aligned/native-pair
responsibility, without a pair or Fourier quotient. -/
theorem wholeRestartEndpointFullPairMacro_trace_eq_responsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    linearResidualTrace wholeRestartEndpointFullPairMacroKeep
        (wholeRestartEndpointFullPairMacroPending
          initial elapsedBounded accumulationRead) =
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartPairDuhamelTail initial 0 0) := by
  simp [linearResidualTrace, wholeRestartEndpointFullPairMacroKeep,
    wholeRestartEndpointFullPairMacroPending]

/-- Exact same-event write-back of the complete carrier. -/
theorem wholeRestartEndpointFullPairMacro_ledger_writeBack
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointFullPairMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      wholeRestartEndpointFullPairMacroTraceLedger
          initial elapsedBounded accumulationRead +
        linearResidualTrace wholeRestartEndpointFullPairMacroKeep
          (wholeRestartEndpointFullPairMacroPending
            initial elapsedBounded accumulationRead) := by
  simp [wholeRestartEndpointFullPairMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointFullPairMacro_trace_eq_responsibility]

/-- Every actual old-run pair-Duhamel coordinate is literally present in the
endpoint-written ledger. -/
theorem wholeRestartEndpointFullPairMacro_writtenPair
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (output first : IntegerWavevector) :
    (wholeRestartEndpointFullPairMacroTraceLedger
        initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
          index output first =
      wholeRestartPairDuhamelOccurrence
        initial index output first := by
  simp [wholeRestartEndpointFullPairMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartPairDuhamelTail,
    wholeRestartPairDuhamelPathTable,
    wholeRestartPairDuhamelTable]

/-! ## Physical projection of the same endpoint event -/

/-- The full-pair macro frame uses the existing endpoint physical current;
the pair carrier is not injected into the PDE state. -/
def wholeRestartEndpointFullPairMacroFrame
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (phase : WholeRestartEndpointComponentMacroPhase) :
    GeneratedWholeRestartCurrent ν ×
      (WholeRestartEndpointFullPairResponsibility ×
        WholeRestartEndpointFullPairResponsibility) :=
  (wholeRestartEndpointComponentMacroPhysicalCurrent
      initial elapsedBounded phase,
    wholeRestartEndpointFullPairMacroPending
      initial elapsedBounded phase,
    wholeRestartEndpointFullPairMacroTraceLedger
      initial elapsedBounded phase)

/-- One endpoint step writes its actual unforced target together with the
complete native-pair ledger. -/
theorem GeneratedWholeRestartEndpointMacroStep.fullPairMacroFrame_update
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointFullPairMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        (wholeRestartEndpointAlignedResponsibilityTail
            current step.elapsedBounded 0,
          wholeRestartPairDuhamelTail current 0 0)) := by
  cases step with
  | advance elapsedBounded =>
      apply Prod.ext
      · exact
          (wholeRestartEndpointComponentMacroPhysicalCurrent_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
      · rfl

/-! ## Negative symmetric work survives the endpoint ledger -/

/-- A negative symmetric anchored direct work forces at least one of its two
actual pair-Duhamel coordinates to be nonzero.  This uses the already proved
pair-plus-swap compiler before the pair quotient. -/
theorem
    wholeRestartAnchoredSymmetricDirectDuhamelWork_lt_zero_generates_pairDuhamelCoordinate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector)
    (symmetricNegative :
      wholeRestartAnchoredSymmetricDirectDuhamelWork
        initial frame wave first < 0) :
    wholeRestartPairDuhamelOccurrence
          initial frame.currentIndex wave.1 first ≠ 0 ∨
      wholeRestartPairDuhamelOccurrence
          initial frame.currentIndex wave.1 (wave.1 - first) ≠ 0 := by
  by_contra bothSilent
  have firstZero :
      wholeRestartPairDuhamelOccurrence
        initial frame.currentIndex wave.1 first = 0 :=
    not_ne_iff.mp (not_or.mp bothSilent).1
  have secondZero :
      wholeRestartPairDuhamelOccurrence
        initial frame.currentIndex wave.1 (wave.1 - first) = 0 :=
    not_ne_iff.mp (not_or.mp bothSilent).2
  have firstWorkZero :
      wholeRestartAnchoredPairDuhamelVelocityWork
        initial frame wave first = 0 := by
    unfold wholeRestartAnchoredPairDuhamelVelocityWork
    rw [firstZero, biotSavartVelocityCoefficient_zero_vorticity]
    exact complexCoordinateRealInner_zero_right _
  have secondWorkZero :
      wholeRestartAnchoredPairDuhamelVelocityWork
        initial frame wave (wave.1 - first) = 0 := by
    unfold wholeRestartAnchoredPairDuhamelVelocityWork
    rw [secondZero, biotSavartVelocityCoefficient_zero_vorticity]
    exact complexCoordinateRealInner_zero_right _
  have compiler :=
    wholeRestartAnchoredPairDuhamelVelocityWork_add_swap_eq_symmetricDirect
      initial frame wave first
  rw [firstWorkZero, secondWorkZero, zero_add] at compiler
  linarith

/-- If a source-selected anchored output is negative and its viscous branch
is not, the existing symmetric compiler internally selects a nonzero native
pair-Duhamel coordinate already present in the endpoint macro ledger. -/
theorem
    wholeRestartAnchoredOutput_negative_of_viscous_nonnegative_generates_fullPairMacro_nonzero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (outputNegative :
      wholeRestartAnchoredCausalTangentVelocityWork initial frame wave +
          ∑' first : IntegerWavevector,
            wholeRestartAnchoredPairInnovationVelocityWork
              initial frame wave first < 0)
    (viscousNonnegative :
      0 ≤ wholeRestartAnchoredViscousHeatDisplacementVelocityWork
        initial frame wave) :
    ∃ first : IntegerWavevector,
      (wholeRestartEndpointFullPairMacroTraceLedger
          initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
            frame.currentIndex wave.1 first ≠ 0 := by
  have outputCompiler :=
    two_mul_wholeRestartAnchoredOutputContribution_eq_viscousHeat_add_tsum_symmetricDirect
      initial frame wave
  have symmetricTsumNegative :
      (∑' first : IntegerWavevector,
        wholeRestartAnchoredSymmetricDirectDuhamelWork
          initial frame wave first) < 0 := by
    linarith
  have negativeSymmetricPair :
      ∃ first : IntegerWavevector,
        wholeRestartAnchoredSymmetricDirectDuhamelWork
          initial frame wave first < 0 := by
    by_contra noNegativePair
    push Not at noNegativePair
    have symmetricTsumNonnegative :
        0 ≤ ∑' first : IntegerWavevector,
          wholeRestartAnchoredSymmetricDirectDuhamelWork
            initial frame wave first :=
      tsum_nonneg noNegativePair
    linarith
  obtain ⟨first, symmetricNegative⟩ := negativeSymmetricPair
  rcases
      wholeRestartAnchoredSymmetricDirectDuhamelWork_lt_zero_generates_pairDuhamelCoordinate
        initial frame wave first symmetricNegative with
    firstNonzero | secondNonzero
  · refine ⟨first, ?_⟩
    rw [wholeRestartEndpointFullPairMacro_writtenPair]
    exact firstNonzero
  · refine ⟨wave.1 - first, ?_⟩
    rw [wholeRestartEndpointFullPairMacro_writtenPair]
    exact secondNonzero

/-! ## Source-facing whole write -/

/-- A whole endpoint step writes its actual unforced target and exhausts a
positive kinetic atom without an endpoint-quotient silence branch.

For every requested old-run index the source selects an actual negative
anchored output.  Either its viscous work is negative, or the identical
endpoint macro ledger contains a nonzero pair-Duhamel coordinate and the
same frame also carries the already generated ordinary/reflected native
pair responsibility.  No frame, output, pair, time, branch, target, or
nonzero witness is supplied by the caller. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_cofinal_fullPairMacroWriteBack
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointFullPairMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        ∀ requestedStart : ℕ,
          ∃ frame : WholeRestartAnchoredReflectedPairFrame,
            ∃ wave : NonzeroIntegerWavevector,
              requestedStart ≤ frame.currentIndex ∧
                run current (frame.currentIndex + 1) =
                  (run current frame.currentIndex).next ∧
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState
                    current frame.start wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartCausalTangentGain
                            current frame.currentIndex wave.1 •
                          wholeRestartCrossingUnforcedTangentRow
                            current frame.currentIndex wave.1 +
                        ∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current frame.currentIndex wave.1 first)))) < 0 ∧
                (wholeRestartAnchoredViscousHeatDisplacementVelocityWork
                      current frame wave < 0 ∨
                  ((∃ first : IntegerWavevector,
                      (wholeRestartEndpointFullPairMacroTraceLedger
                          current step.elapsedBounded
                          (wholeRestartEndpointComponentMacroUpdate
                            accumulationRead)).2
                            frame.currentIndex wave.1 first ≠ 0) ∧
                    ∃ first second : IntegerWavevector,
                      first + second = wave.1 ∧
                        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
                            current frame first second < 0 ∧
                        ((∃ time :
                              Icc (0 : ℝ)
                                (run current
                                  frame.currentIndex).nextContact.time.1,
                            wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
                                  current frame first second time ≠ 0 ∧
                              actualWholeContinuousVelocityPairVector
                                  (run current
                                    frame.currentIndex).nextContact.prefixReceipt
                                  first second time ≠ 0 ∧
                              (wholeRestartNextVelocityPairOccurrence
                                    current frame.currentIndex
                                      first second ≠ 0 ∨
                                (linearResidualTrace
                                    wholeRestartSplicedVelocityPairOccurrenceTailKeep
                                    (wholeRestartSplicedVelocityPairOccurrenceTail
                                      current frame.currentIndex time 0) 0)
                                      first second ≠ 0) ∧
                              run current frame.next.currentIndex =
                                (run current frame.currentIndex).next) ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current
                                  frame.currentIndex).nextContact.time.1,
                            wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
                                  current frame first second time ≠ 0 ∧
                              actualWholeRestartAnchoredReflectedVelocityPairVector
                                  current frame first
                                    (outputNegSecondEquiv first second)
                                      time ≠ 0 ∧
                              (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                                    current frame first
                                      (outputNegSecondEquiv first second) ≠ 0 ∨
                                wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                                    current frame first
                                      (outputNegSecondEquiv first second)
                                        time ≠ 0) ∧
                              run current frame.next.currentIndex =
                                (run current frame.currentIndex).next)))) := by
  constructor
  · exact congrArg Prod.fst
      (GeneratedWholeRestartEndpointMacroStep.fullPairMacroFrame_update step)
  · obtain ⟨_physicalWrite, atomZeroOrActive⟩ :=
      wholeRestartEndpointMacroStep_generates_zero_or_cofinal_negativeSourceAnchorCollectiveWork
        step
    rcases atomZeroOrActive with atomZero | active
    · exact Or.inl atomZero
    · apply Or.inr
      intro requestedStart
      obtain
          ⟨start, _steps, requestedLeStart, _stepsPositive, _gapEq,
            _collectiveLower, _anchorSumNegative, _anchorIdentity,
            frame, _frameStart, _frameOffsetLt, frameIndex, runNext,
            _writeNonzero, _edgeNegative, wave, outputNegative⟩ :=
        active requestedStart
      have requestedLeFrame : requestedStart ≤ frame.currentIndex := by
        rw [frameIndex]
        exact requestedLeStart.trans
          (Nat.le_add_right start frame.offset)
      have compiledOutputNegative :
          wholeRestartAnchoredCausalTangentVelocityWork
                current frame wave +
              ∑' first : IntegerWavevector,
                wholeRestartAnchoredPairInnovationVelocityWork
                  current frame wave first < 0 := by
        rw [wholeRestartAnchoredOutputContribution_eq_exactCausalRow]
        exact outputNegative
      by_cases viscousNegative :
          wholeRestartAnchoredViscousHeatDisplacementVelocityWork
            current frame wave < 0
      · exact
          ⟨frame, wave, requestedLeFrame, runNext, outputNegative,
            Or.inl viscousNegative⟩
      · have viscousNonnegative :
            0 ≤ wholeRestartAnchoredViscousHeatDisplacementVelocityWork
              current frame wave :=
          le_of_not_gt viscousNegative
        have ledgerNonzero :=
          wholeRestartAnchoredOutput_negative_of_viscous_nonnegative_generates_fullPairMacro_nonzero
            current step.elapsedBounded frame wave
            compiledOutputNegative viscousNonnegative
        rcases
            wholeRestartAnchoredOutputContribution_nativePairDisposition
              current frame wave with
          outputNonnegative | viscousOrPair
        · exact
            (not_lt_of_ge outputNonnegative compiledOutputNegative).elim
        · rcases viscousOrPair with
            selectedViscousNegative | nativePair
          · exact (viscousNegative selectedViscousNegative).elim
          · exact
              ⟨frame, wave, requestedLeFrame, runNext, outputNegative,
                Or.inr ⟨ledgerNonzero, nativePair⟩⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
end NavierStokes
end SaturationMonoid

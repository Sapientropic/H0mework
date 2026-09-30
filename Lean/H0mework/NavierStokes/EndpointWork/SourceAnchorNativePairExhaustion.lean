import H0mework.NavierStokes.EndpointWork.SourceAnchorCollectiveWork
import H0mework.NavierStokes.PairRestart.AnchoredMixedWorkNativeCompiler

/-!
# Source-facing native pair exhaustion of the endpoint kinetic atom

The source-generated negative anchor output is consumed before any output or
pair quotient.  The exact symmetric compiler leaves only two dispositions:

* negative viscous/heat displacement on that output; or
* a concrete negative ordered direct work written into the ordinary or
  reflected actual velocity-pair next/whole trace.

The public theorem takes only the authoritative endpoint macro step.  The
positive branch, arbitrarily late frame, output, ordered pair, sign, time, and
native settlement are all generated internally.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairExhaustion

open scoped BigOperators Interval

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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorCollectiveWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess.WholeRestartAnchoredReflectedPairFrame
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredMixedWorkNativeCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredHeatCommutatorNativeVelocityPairRedirect
open AffineRelaxation

noncomputable section

/-! ## Exact output seam -/

/-- The literal tangent-plus-pair row selected by the source theorem is
exactly the scalar output contribution consumed by the symmetric native
compiler. -/
theorem wholeRestartAnchoredOutputContribution_eq_exactCausalRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartAnchoredCausalTangentVelocityWork initial frame wave +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairInnovationVelocityWork
            initial frame wave first =
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState initial frame.start wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain
                  initial frame.currentIndex wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  initial frame.currentIndex wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  initial frame.currentIndex wave.1 first)))) := by
  have pairTsum :=
    wholeRestartAnchorPairInnovationVelocityRealInner_tsum
      initial frame.start frame.currentIndex wave
  unfold wholeRestartAnchoredCausalTangentVelocityWork
    wholeRestartAnchoredPairInnovationVelocityWork
  rw [← pairTsum]
  change
    RCLike.re (inner ℂ _
        (wholeRestartVelocityEuclideanRowCLM wave.1 _)) +
      RCLike.re (inner ℂ _
        (wholeRestartVelocityEuclideanRowCLM wave.1 _)) =
      RCLike.re (inner ℂ _
        (wholeRestartVelocityEuclideanRowCLM wave.1 (_ + _)))
  rw [map_add, inner_add_right]
  rw [← RCLike.reCLM_apply]
  exact (map_add (RCLike.reCLM : StrongDual ℝ ℂ) _ _).symm

/-! ## Source-facing whole-write exhaustion -/

/-- A whole endpoint macro write has no silent positive kinetic-atom branch.

For every requested old-run index, the source itself selects a later actual
anchored frame and a negative exact output.  The same output is then exhausted
as either negative viscous/heat work or a concrete negative ordered direct
work carrying an ordinary/reflected native velocity-pair responsibility. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_cofinal_anchoredNativePairExhaustion
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
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
                                  (outputNegSecondEquiv first second) time ≠ 0 ∧
                            (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                                  current frame first
                                    (outputNegSecondEquiv first second) ≠ 0 ∨
                              wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                                  current frame first
                                    (outputNegSecondEquiv first second)
                                      time ≠ 0) ∧
                            run current frame.next.currentIndex =
                              (run current frame.currentIndex).next))) := by
  obtain ⟨physicalWrite, atomZeroOrActive⟩ :=
    wholeRestartEndpointMacroStep_generates_zero_or_cofinal_negativeSourceAnchorCollectiveWork
      step
  refine ⟨physicalWrite, ?_⟩
  rcases atomZeroOrActive with atomZero | active
  · exact Or.inl atomZero
  · apply Or.inr
    intro requestedStart
    obtain
        ⟨start, steps, requestedLeStart, _stepsPositive, _gapEq,
          _collectiveLower, _anchorSumNegative, _anchorIdentity,
          frame, frameStart, _frameOffsetLt, frameIndex, runNext,
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
    rcases
        wholeRestartAnchoredOutputContribution_nativePairDisposition
          current frame wave with
      outputNonnegative | viscousOrPair
    · exact (not_lt_of_ge outputNonnegative compiledOutputNegative).elim
    · exact
        ⟨frame, wave, requestedLeFrame, runNext, outputNegative,
          viscousOrPair⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairExhaustion
end NavierStokes
end SaturationMonoid

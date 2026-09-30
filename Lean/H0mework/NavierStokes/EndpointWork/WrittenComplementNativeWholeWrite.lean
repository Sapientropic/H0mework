import H0mework.NavierStokes.EndpointWork.AlignedCausalWrite
import H0mework.NavierStokes.EndpointWork.ComplementNoSilentWrite
import H0mework.NavierStokes.EndpointWork.SourceAnchorNativePairMacroWriteBack

/-!
# Written endpoint atom to complement no-silence on the same native edge

The endpoint causal frame already writes the complete aligned kinetic tail.
For a positive atom, two coordinates of that literal written tail generate a
finite old-run gap and one changed actual edge inside it.

This module consumes that exact edge before any quotient.  A nonzero velocity
coefficient selects its vorticity output, embeds the canonical complement pair
into the two actual coefficient endpoints, excludes componentwise joint
silence, and enters the existing tangent or pair/heat-commutator native
exhaustion.

Thus the written kinetic coordinates, native edge, complement registration,
physical successor, and downstream redirect all have one source provenance.
No written index, edge, output, pair, time, branch, nonzero witness, target,
or settlement certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomWrittenComplementNativeWholeWrite

open scoped BigOperators Interval

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAlignedCausalWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open ComplementObservation
open AffineRelaxation

noncomputable section

/-- One source-selected edge inside a pair of separated coordinates of the
literal endpoint-written kinetic tail, together with its complete
pre-quotient no-silent disposition. -/
structure WrittenKineticComplementNativeRedirect
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (requestedWrittenIndex : ℕ) where
  writtenEarlier : ℕ
  writtenLater : ℕ
  segmentStart : ℕ
  segmentSteps : ℕ
  nativeEdgeIndex : ℕ
  requested_le_writtenEarlier :
    requestedWrittenIndex ≤ writtenEarlier
  writtenEarlier_lt_writtenLater :
    writtenEarlier < writtenLater
  segmentStart_eq :
    segmentStart =
      wholeRestartEndpointSelectedOccurrenceIndex
        current step.elapsedBounded writtenEarlier
  segmentFinish_eq :
    segmentStart + segmentSteps =
      wholeRestartEndpointSelectedOccurrenceIndex
        current step.elapsedBounded writtenLater
  segmentSteps_pos : 0 < segmentSteps
  writtenKineticSeparation :
    step.physicalStageKineticEnergyAtom / 2 <
      ‖((wholeRestartEndpointCausalMacroTraceLedger
            current step.elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate
              accumulationRead)).1 writtenLater).2 -
        ((wholeRestartEndpointCausalMacroTraceLedger
            current step.elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate
              accumulationRead)).1 writtenEarlier).2‖ ^ 2
  segmentStart_le_nativeEdgeIndex :
    segmentStart ≤ nativeEdgeIndex
  nativeEdgeIndex_lt_segmentFinish :
    nativeEdgeIndex < segmentStart + segmentSteps
  nativeEdge_is_actual :
    run current (nativeEdgeIndex + 1) =
      (run current nativeEdgeIndex).next
  nativeEdge_time_pos :
    0 < (run current nativeEdgeIndex).nextContact.time.1
  output : NonzeroIntegerWavevector
  outputVelocityCoefficient_ne_zero :
    puncturedWholeVelocityEuclideanCoefficient
      ((run current nativeEdgeIndex).nextContact.physicalState -
        (run current nativeEdgeIndex).contact.physicalState) output ≠ 0
  output_ne_zero : output.1 ≠ 0
  outputIncrement_ne_zero :
    (run current nativeEdgeIndex).nextContact.physicalState output.1 -
        (run current nativeEdgeIndex).contact.physicalState output.1 ≠ 0
  outputCausalSplit :
    (run current nativeEdgeIndex).nextContact.physicalState output.1 -
          (run current nativeEdgeIndex).contact.physicalState output.1 =
        wholeRestartCausalTangentGain
              current nativeEdgeIndex output.1 •
            wholeRestartCrossingUnforcedTangentRow
              current nativeEdgeIndex output.1 +
          (∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              current nativeEdgeIndex output.1 first)
  fullPairLedger_eq_forcedTrace :
    wholeRestartEndpointFullPairMacroTraceLedger
          current step.elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      linearResidualTrace wholeRestartEndpointFullPairMacroKeep
        (wholeRestartEndpointFullPairMacroPending
          current step.elapsedBounded accumulationRead)
  fullPairLedger_writtenInnovation :
    ∀ first : IntegerWavevector,
      (wholeRestartEndpointFullPairMacroTraceLedger
            current step.elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate
              accumulationRead)).2
            nativeEdgeIndex output.1 first -
          wholeRestartCausalTangentGain
                current nativeEdgeIndex output.1 •
            wholeRestartContactPairOccurrenceTable
              current nativeEdgeIndex output.1 first =
        wholeRestartPairDuhamelInnovationOccurrence
          current nativeEdgeIndex output.1 first
  fullPairLedger_causalSplit :
    (run current nativeEdgeIndex).nextContact.physicalState output.1 -
          (run current nativeEdgeIndex).contact.physicalState output.1 =
        wholeRestartCausalTangentGain
              current nativeEdgeIndex output.1 •
            wholeRestartCrossingUnforcedTangentRow
              current nativeEdgeIndex output.1 +
          tsum (fun first : IntegerWavevector =>
            (wholeRestartEndpointFullPairMacroTraceLedger
                  current step.elapsedBounded
                  (wholeRestartEndpointComponentMacroUpdate
                    accumulationRead)).2
                  nativeEdgeIndex output.1 first -
              wholeRestartCausalTangentGain
                    current nativeEdgeIndex output.1 •
                wholeRestartContactPairOccurrenceTable
                  current nativeEdgeIndex output.1 first)
  complementRegistration_injective :
    Function.Injective
      (wholeRestartActualOutputEdgeRegistration
        current nativeEdgeIndex output.1)
  complementJointSilent_false :
    ¬ wholeRestartActualOutputCausalJointSilent
      current nativeEdgeIndex output.1
  nativeExhaustion :
    ((∃ tangentNonzero :
          wholeRestartCrossingUnforcedTangentRow
            current nativeEdgeIndex ≠ 0,
        ∃ localTime : ℝ,
          0 < localTime ∧
            localTime <
              (run current nativeEdgeIndex).nextContact.time.1 ∧
            localTime *
                  (wholeRestartCrossingContinuousUnforcedTangentDensity
                    current nativeEdgeIndex tangentNonzero 0 / 2) ≤
                ∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    current nativeEdgeIndex tangentNonzero time ∧
              0 <
                ∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    current nativeEdgeIndex tangentNonzero time ∧
              (∫ time in (0 : ℝ)..localTime,
                  wholeRestartCrossingContinuousUnforcedTangentDensity
                    current nativeEdgeIndex tangentNonzero time) ≤
                ‖(run current
                    nativeEdgeIndex).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
              current nativeEdgeIndex output.1 first ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                current nativeEdgeIndex output.1 first ≠ 0 ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run current nativeEdgeIndex).nextContact.time.1,
              wholeRestartPairOccurrenceTrace
                current nativeEdgeIndex output.1 first time ≠ 0) ∧
          (wholeRestartVelocityTriadHeatCommutatorTrace
                current nativeEdgeIndex first (output.1 - first) = 0 ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run current nativeEdgeIndex).nextContact.time.1,
              actualWholeVelocityBilinearEnergyOccurrence
                  (run current nativeEdgeIndex).nextContact.prefixReceipt
                  first (output.1 - first) time ≠ 0 ∧
                actualWholeContinuousVelocityPairVector
                  (run current nativeEdgeIndex).nextContact.prefixReceipt
                  first (output.1 - first) time ≠ 0 ∧
                (wholeRestartNextVelocityPairOccurrence
                      current nativeEdgeIndex first (output.1 - first) ≠ 0 ∨
                  (linearResidualTrace
                      wholeRestartSplicedVelocityPairOccurrenceTailKeep
                      (wholeRestartSplicedVelocityPairOccurrenceTail
                        current nativeEdgeIndex time 0) 0)
                        first (output.1 - first) ≠ 0) ∧
                run current (nativeEdgeIndex + 1) =
                  (run current nativeEdgeIndex).next))

/-- One actual endpoint macro step writes its unforced physical successor and
internally exhausts the atom written in that identical frame.

The zero/positive split is source-owned.  In the positive branch, every
requested written coordinate has a later written pair whose exact native gap
contains a source-selected edge; the complement/no-silent and
tangent/pair/commutator consumers operate on that same edge. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_writtenComplementNoSilent_nativeWholeWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointFullPairMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        (0 < step.physicalStageKineticEnergyAtom ∧
          ∀ requestedWrittenIndex : ℕ,
            Nonempty
              (WrittenKineticComplementNativeRedirect
                step requestedWrittenIndex))) := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  rcases endpointReceipt.kineticReceipt.defect_disposition with
    defectPositive | defectZero
  · have atomPositive :
      0 < step.physicalStageKineticEnergyAtom := by
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectPositive
    obtain ⟨_physicalWrite, written⟩ :=
      physicalStageKineticEnergyAtom_pos_generates_cofinal_writtenKineticOutputSquareCausalWrite
        step atomPositive
    refine
      ⟨congrArg Prod.fst
          (GeneratedWholeRestartEndpointMacroStep.fullPairMacroFrame_update
            step),
        Or.inr ⟨atomPositive, ?_⟩⟩
    intro requestedWrittenIndex
    obtain
        ⟨writtenEarlier, writtenLater, segmentStart, segmentSteps,
          nativeEdgeIndex, requestedLe, writtenEarlierLtWrittenLater,
          segmentStartEq, segmentFinishEq, segmentStepsPositive,
          writtenSeparation, _pathLower, segmentStartLeNativeEdge,
          nativeEdgeLtSegmentFinish, _outputSquareLower, _edgeLedger,
          outputExists, outputDisposition⟩ :=
      written requestedWrittenIndex
    obtain ⟨output, outputCoefficientNonzero⟩ := outputExists
    obtain
        ⟨outputNonzero, outputIncrementNonzero, outputCausalSplit,
          tangentOrPair⟩ :=
      outputDisposition output outputCoefficientNonzero
    have registrationInjective :=
      wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
        current nativeEdgeIndex output.1 outputIncrementNonzero
    have noJointSilence :=
      wholeRestartActualOutputIncrement_ne_zero_excludes_causalJointSilent
        current nativeEdgeIndex output.1 outputNonzero
        outputIncrementNonzero
    have ledgerEqForcedTrace :
        wholeRestartEndpointFullPairMacroTraceLedger
              current step.elapsedBounded
              (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
          linearResidualTrace wholeRestartEndpointFullPairMacroKeep
            (wholeRestartEndpointFullPairMacroPending
              current step.elapsedBounded accumulationRead) := by
      rw [wholeRestartEndpointFullPairMacro_trace_eq_responsibility]
      rfl
    have writtenInnovation :
        ∀ first : IntegerWavevector,
          (wholeRestartEndpointFullPairMacroTraceLedger
                current step.elapsedBounded
                (wholeRestartEndpointComponentMacroUpdate
                  accumulationRead)).2
                nativeEdgeIndex output.1 first -
              wholeRestartCausalTangentGain
                    current nativeEdgeIndex output.1 •
                wholeRestartContactPairOccurrenceTable
                  current nativeEdgeIndex output.1 first =
            wholeRestartPairDuhamelInnovationOccurrence
              current nativeEdgeIndex output.1 first := by
      intro first
      rw [wholeRestartEndpointFullPairMacro_writtenPair]
      rfl
    have writtenCausalSplit :
        (run current nativeEdgeIndex).nextContact.physicalState output.1 -
              (run current nativeEdgeIndex).contact.physicalState output.1 =
            wholeRestartCausalTangentGain
                  current nativeEdgeIndex output.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current nativeEdgeIndex output.1 +
              tsum (fun input : IntegerWavevector =>
                (wholeRestartEndpointFullPairMacroTraceLedger
                      current step.elapsedBounded
                      (wholeRestartEndpointComponentMacroUpdate
                        accumulationRead)).2
                      nativeEdgeIndex output.1 input -
                  wholeRestartCausalTangentGain
                        current nativeEdgeIndex output.1 •
                    wholeRestartContactPairOccurrenceTable
                      current nativeEdgeIndex output.1 input) := by
      rw [outputCausalSplit]
      congr 1
      apply tsum_congr
      intro first
      exact (writtenInnovation first).symm
    have nativeExhaustion :
        ((∃ tangentNonzero :
              wholeRestartCrossingUnforcedTangentRow
                current nativeEdgeIndex ≠ 0,
            ∃ localTime : ℝ,
              0 < localTime ∧
                localTime <
                  (run current nativeEdgeIndex).nextContact.time.1 ∧
                localTime *
                      (wholeRestartCrossingContinuousUnforcedTangentDensity
                        current nativeEdgeIndex tangentNonzero 0 / 2) ≤
                    ∫ time in (0 : ℝ)..localTime,
                      wholeRestartCrossingContinuousUnforcedTangentDensity
                        current nativeEdgeIndex tangentNonzero time ∧
                  0 <
                    ∫ time in (0 : ℝ)..localTime,
                      wholeRestartCrossingContinuousUnforcedTangentDensity
                        current nativeEdgeIndex tangentNonzero time ∧
                  (∫ time in (0 : ℝ)..localTime,
                      wholeRestartCrossingContinuousUnforcedTangentDensity
                        current nativeEdgeIndex tangentNonzero time) ≤
                    ‖(run current
                        nativeEdgeIndex).nextContact.prefixReceipt.wholeTangent‖ ^ 2) ∨
          ∃ first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
                  current nativeEdgeIndex output.1 first ≠ 0 ∧
              (wholeRestartNextPairOccurrence
                    current nativeEdgeIndex output.1 first ≠ 0 ∨
                ∃ time :
                    Icc (0 : ℝ)
                      (run current nativeEdgeIndex).nextContact.time.1,
                  wholeRestartPairOccurrenceTrace
                    current nativeEdgeIndex output.1 first time ≠ 0) ∧
              (wholeRestartVelocityTriadHeatCommutatorTrace
                    current nativeEdgeIndex first (output.1 - first) = 0 ∨
                ∃ time :
                    Icc (0 : ℝ)
                      (run current nativeEdgeIndex).nextContact.time.1,
                  actualWholeVelocityBilinearEnergyOccurrence
                      (run current nativeEdgeIndex).nextContact.prefixReceipt
                      first (output.1 - first) time ≠ 0 ∧
                    actualWholeContinuousVelocityPairVector
                      (run current nativeEdgeIndex).nextContact.prefixReceipt
                      first (output.1 - first) time ≠ 0 ∧
                    (wholeRestartNextVelocityPairOccurrence
                          current nativeEdgeIndex first
                            (output.1 - first) ≠ 0 ∨
                      (linearResidualTrace
                          wholeRestartSplicedVelocityPairOccurrenceTailKeep
                          (wholeRestartSplicedVelocityPairOccurrenceTail
                            current nativeEdgeIndex time 0) 0)
                            first (output.1 - first) ≠ 0) ∧
                    run current (nativeEdgeIndex + 1) =
                      (run current nativeEdgeIndex).next)) := by
      rcases tangentOrPair with tangentOutputNonzero | pair
      · left
        have tangentNonzero :
            wholeRestartCrossingUnforcedTangentRow
              current nativeEdgeIndex ≠ 0 := by
          intro tangentZero
          exact tangentOutputNonzero
            (congrFun tangentZero output.1)
        exact
          ⟨tangentNonzero,
            wholeRestartCrossingUnforcedTangent_positiveTimePayment
              current nativeEdgeIndex tangentNonzero⟩
      · right
        rcases pair with
          ⟨first, innovationNonzero, pairResponsibility⟩
        obtain ⟨_pairResponsibility, heatExhaustion⟩ :=
          wholeRestartPairDuhamelInnovationOccurrence_ne_zero_generates_heatCommutator_nativeExhaustion
            current nativeEdgeIndex output.1 first innovationNonzero
        exact
          ⟨first, innovationNonzero, pairResponsibility, heatExhaustion⟩
    exact
      ⟨{ writtenEarlier := writtenEarlier
         writtenLater := writtenLater
         segmentStart := segmentStart
         segmentSteps := segmentSteps
         nativeEdgeIndex := nativeEdgeIndex
         requested_le_writtenEarlier := requestedLe
         writtenEarlier_lt_writtenLater :=
           writtenEarlierLtWrittenLater
         segmentStart_eq := segmentStartEq
         segmentFinish_eq := segmentFinishEq
         segmentSteps_pos := segmentStepsPositive
         writtenKineticSeparation := writtenSeparation
         segmentStart_le_nativeEdgeIndex := segmentStartLeNativeEdge
         nativeEdgeIndex_lt_segmentFinish := nativeEdgeLtSegmentFinish
         nativeEdge_is_actual := rfl
         nativeEdge_time_pos :=
           (run current nativeEdgeIndex).nextContact.time_pos
         output := output
         outputVelocityCoefficient_ne_zero := outputCoefficientNonzero
         output_ne_zero := outputNonzero
         outputIncrement_ne_zero := outputIncrementNonzero
         outputCausalSplit := outputCausalSplit
         fullPairLedger_eq_forcedTrace := ledgerEqForcedTrace
         fullPairLedger_writtenInnovation := writtenInnovation
         fullPairLedger_causalSplit := writtenCausalSplit
         complementRegistration_injective := registrationInjective
         complementJointSilent_false := noJointSilence
         nativeExhaustion := nativeExhaustion }⟩
  · refine ⟨?_, Or.inl ?_⟩
    · exact congrArg Prod.fst
        (GeneratedWholeRestartEndpointMacroStep.fullPairMacroFrame_update
          step)
    · rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectZero.1

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomWrittenComplementNativeWholeWrite
end NavierStokes
end SaturationMonoid

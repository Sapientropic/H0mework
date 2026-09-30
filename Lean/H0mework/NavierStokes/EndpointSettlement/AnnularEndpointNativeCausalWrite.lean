import H0mework.NavierStokes.EndpointSettlement.EndpointWholeCarrierWriteBack
import H0mework.NavierStokes.EndpointWork.NativeCausalRedirect
import H0mework.NavierStokes.EndpointWork.ComplementNoSilentWrite

/-!
# Whole-annular scale transport or native causal write

The reduced-core annular projection already has a premise-free adjacent
no-silent split: it survives in the next actual physical state, or the
projected whole-state gap is nonzero.  This module consumes the second branch
before the endpoint quotient.

A nonzero projected gap makes the two actual scale endpoints distinct.
The finite interval between them therefore contains a changed literal native
edge.  The existing same-edge causal compiler then selects a nonzero Fourier
output and writes a tangent responsibility or one concrete pair innovation
into its next/trace disposition.

The public theorem also retains the identical endpoint event's unforced
physical successor and complete aligned/pair/physical trace ledger.  The
caller supplies no gap, changed edge, output, pair, branch, nonzero witness,
target state, continuation, or faithfulness certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomComplementNoSilentWrite
open ResidualProjection
open AffineRelaxation

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- One source-generated changed native edge inside an adjacent reduced-core
scale interval, with its exact Fourier increment and tangent/pair causal
disposition retained as one dependent receipt. -/
structure WholeRestartReducedCoreAdjacentNativeCausalWrite
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) where
  nativeEdgeIndex : ℕ
  node_le_edge :
    scale.absoluteOccurrence node ≤ nativeEdgeIndex
  edge_lt_next :
    nativeEdgeIndex < scale.absoluteOccurrence (node + 1)
  native_update :
    run initial (nativeEdgeIndex + 1) =
      (run initial nativeEdgeIndex).next
  output : IntegerWavevector
  output_ne_zero : output ≠ 0
  increment_ne_zero :
    (run initial nativeEdgeIndex).nextContact.physicalState output -
        (run initial nativeEdgeIndex).contact.physicalState output ≠ 0
  causal_split :
    (run initial nativeEdgeIndex).nextContact.physicalState output -
          (run initial nativeEdgeIndex).contact.physicalState output =
        wholeRestartCausalTangentGain initial nativeEdgeIndex output •
            wholeRestartCrossingUnforcedTangentRow
              initial nativeEdgeIndex output +
          (∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              initial nativeEdgeIndex output first)
  causal_responsibility :
    wholeRestartCrossingUnforcedTangentRow
          initial nativeEdgeIndex output ≠ 0 ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
              initial nativeEdgeIndex output first ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                initial nativeEdgeIndex output first ≠ 0 ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run initial nativeEdgeIndex).nextContact.time.1,
              wholeRestartPairOccurrenceTrace
                initial nativeEdgeIndex output first time ≠ 0)

/-- Least-core growth forces every adjacent reduced-core scale interval to
contain a changed literal native edge.  The same actual edge selects its
nonzero Fourier increment and exact tangent/pair causal responsibility.

Unlike the annular-observer alternative below, this conclusion has no
survival branch: equality of the whole physical endpoints is already
incompatible with the source-owned least-radius recursion. -/
theorem
    wholeRestartEndpointMacroStep_reducedCore_generates_adjacentNativeCausalWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (macroStep : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointFullPairPhysicalMacroFrame
        current macroStep.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        (wholeRestartEndpointFullPairMacroPending
            current macroStep.elapsedBounded accumulationRead,
          wholeRestartPhysicalVorticityTail current 0 0)) ∧
      ∀ (scale : WholeRestartReducedCoreScaleLineage current) (node : ℕ),
        Nonempty
          (WholeRestartReducedCoreAdjacentNativeCausalWrite scale node) := by
  refine
    ⟨wholeRestartEndpointFullPairPhysicalMacroFrame_update macroStep, ?_⟩
  intro scale node
  have endpointNe := scale.adjacentPhysicalState_ne node
  have occurrenceLt :
      scale.absoluteOccurrence node <
        scale.absoluteOccurrence (node + 1) :=
    scale.absoluteOccurrence_strict (Nat.lt_succ_self node)
  obtain ⟨nativeEdgeIndex, nodeLeEdge, edgeLtNext, adjacentNe⟩ :=
    exists_adjacent_native_change_of_endpoint_change
      (fun index =>
        (run current index).contact.physicalState)
      occurrenceLt endpointNe
  have nativeStateNe :
      (run current nativeEdgeIndex).nextContact.physicalState ≠
        (run current nativeEdgeIndex).contact.physicalState := by
    simpa only [run_succ, GeneratedWholeRestartCurrent.next] using
      adjacentNe.symm
  obtain ⟨output, outputNonzero, incrementNonzero, causalSplit,
      causalResponsibility⟩ :=
    nativePhysicalChange_generates_causalResponsibility
      current nativeEdgeIndex nativeStateNe
  exact
    ⟨{ nativeEdgeIndex := nativeEdgeIndex
       node_le_edge := nodeLeEdge
       edge_lt_next := edgeLtNext
       native_update := run_succ current nativeEdgeIndex
       output := output
       output_ne_zero := outputNonzero
       increment_ne_zero := incrementNonzero
       causal_split := causalSplit
       causal_responsibility := causalResponsibility }⟩

/-- One actual endpoint step retains its complete product write and, for
every generated reduced-core node, internally exhausts the annular adjacent
gap:

* the whole annular projection survives in the next actual scale state; or
* the same scale interval contains a changed native edge whose exact causal
  tangent/pair responsibility is generated on that edge.

The scale and node are universally quantified in the conclusion rather than
stored in the endpoint source. -/
theorem
    wholeRestartEndpointMacroStep_annularWhole_survives_or_nativeCausalWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (macroStep : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointFullPairPhysicalMacroFrame
        current macroStep.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        (wholeRestartEndpointFullPairMacroPending
            current macroStep.elapsedBounded accumulationRead,
          wholeRestartPhysicalVorticityTail current 0 0)) ∧
      ∀ (scale : WholeRestartReducedCoreScaleLineage current) (node : ℕ),
        complexSharpSupportProjection
              (scale.annularModes node)
              (run current
                (scale.absoluteOccurrence
                  (node + 1))).contact.physicalState ≠ 0 ∨
          ∃ nativeEdgeIndex : ℕ,
            scale.absoluteOccurrence node ≤ nativeEdgeIndex ∧
              nativeEdgeIndex <
                scale.absoluteOccurrence (node + 1) ∧
              run current (nativeEdgeIndex + 1) =
                (run current nativeEdgeIndex).next ∧
              ∃ output : IntegerWavevector,
                output ≠ 0 ∧
                  (run current
                        nativeEdgeIndex).nextContact.physicalState output -
                      (run current
                        nativeEdgeIndex).contact.physicalState output ≠ 0 ∧
                  (run current
                          nativeEdgeIndex).nextContact.physicalState output -
                        (run current
                          nativeEdgeIndex).contact.physicalState output =
                      wholeRestartCausalTangentGain
                            current nativeEdgeIndex output •
                          wholeRestartCrossingUnforcedTangentRow
                            current nativeEdgeIndex output +
                        (∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current nativeEdgeIndex output first) ∧
                  Function.Injective
                    (wholeRestartActualOutputEdgeRegistration
                      current nativeEdgeIndex output) ∧
                  ¬ wholeRestartActualOutputCausalJointSilent
                      current nativeEdgeIndex output ∧
                  (((∃ tangentNonzero :
                        wholeRestartCrossingUnforcedTangentRow
                          current nativeEdgeIndex ≠ 0,
                      ∃ localTime : ℝ,
                        0 < localTime ∧
                          localTime <
                            (run current
                              nativeEdgeIndex).nextContact.time.1 ∧
                          localTime *
                                (wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current nativeEdgeIndex tangentNonzero 0 /
                                  2) ≤
                              ∫ time in (0 : ℝ)..localTime,
                                wholeRestartCrossingContinuousUnforcedTangentDensity
                                  current nativeEdgeIndex tangentNonzero
                                    time ∧
                          0 <
                            ∫ time in (0 : ℝ)..localTime,
                              wholeRestartCrossingContinuousUnforcedTangentDensity
                                current nativeEdgeIndex tangentNonzero time ∧
                          (∫ time in (0 : ℝ)..localTime,
                              wholeRestartCrossingContinuousUnforcedTangentDensity
                                current nativeEdgeIndex tangentNonzero time) ≤
                            ‖(run current
                              nativeEdgeIndex).nextContact.prefixReceipt.wholeTangent‖ ^
                              2)) ∨
                    ∃ first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                            current nativeEdgeIndex output first ≠ 0 ∧
                        (wholeRestartNextPairOccurrence
                              current nativeEdgeIndex output first ≠ 0 ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current
                                  nativeEdgeIndex).nextContact.time.1,
                            wholeRestartPairOccurrenceTrace
                              current nativeEdgeIndex output first time ≠
                                0) ∧
                        (wholeRestartVelocityTriadHeatCommutatorTrace
                              current nativeEdgeIndex first
                                (output - first) = 0 ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current
                                  nativeEdgeIndex).nextContact.time.1,
                            actualWholeVelocityBilinearEnergyOccurrence
                                  (run current
                                    nativeEdgeIndex).nextContact.prefixReceipt
                                  first (output - first) time ≠ 0 ∧
                              actualWholeContinuousVelocityPairVector
                                  (run current
                                    nativeEdgeIndex).nextContact.prefixReceipt
                                  first (output - first) time ≠ 0 ∧
                              (wholeRestartNextVelocityPairOccurrence
                                    current nativeEdgeIndex first
                                      (output - first) ≠ 0 ∨
                                (linearResidualTrace
                                    wholeRestartSplicedVelocityPairOccurrenceTailKeep
                                    (wholeRestartSplicedVelocityPairOccurrenceTail
                                      current nativeEdgeIndex time 0) 0)
                                      first (output - first) ≠ 0) ∧
                              run current (nativeEdgeIndex + 1) =
                                (run current nativeEdgeIndex).next)) := by
  refine
    ⟨wholeRestartEndpointFullPairPhysicalMacroFrame_update macroStep, ?_⟩
  intro scale node
  rcases
      (scale.annularWhole_nextScaleNoSilentWrite node).2 with
    nextProjectionNonzero | projectedGapNonzero
  · exact Or.inl nextProjectionNonzero
  · right
    have gapNonzero :
        scale.annularPhysicalGapTrace node ≠ 0 := by
      intro gapZero
      apply projectedGapNonzero
      rw [gapZero]
      ext output coordinate
      simp [complexSharpSupportProjection_apply]
    have endpointNe :
        (run current
              (scale.absoluteOccurrence node)).contact.physicalState ≠
          (run current
              (scale.absoluteOccurrence
                (node + 1))).contact.physicalState := by
      intro endpointEq
      apply gapNonzero
      have split :=
        scale.annularPhysical_nextScale_split node
      have gapEq :
          scale.annularPhysicalGapTrace node =
            (run current
                (scale.absoluteOccurrence node)).contact.physicalState -
              (run current
                (scale.absoluteOccurrence
                  (node + 1))).contact.physicalState := by
        rw [split]
        abel
      rw [gapEq, endpointEq, sub_self]
    have occurrenceLt :
        scale.absoluteOccurrence node <
          scale.absoluteOccurrence (node + 1) :=
      scale.absoluteOccurrence_strict (Nat.lt_succ_self node)
    obtain ⟨nativeEdgeIndex, nodeLeEdge, edgeLtNext, adjacentNe⟩ :=
      exists_adjacent_native_change_of_endpoint_change
        (fun index =>
          (run current index).contact.physicalState)
        occurrenceLt endpointNe
    have nativeStateNe :
        (run current nativeEdgeIndex).nextContact.physicalState ≠
          (run current nativeEdgeIndex).contact.physicalState := by
      simpa only [run_succ, GeneratedWholeRestartCurrent.next] using
        adjacentNe.symm
    obtain
        ⟨output, outputNonzero, incrementNonzero, causalSplit,
          _causalResponsibility⟩ :=
      nativePhysicalChange_generates_causalResponsibility
        current nativeEdgeIndex nativeStateNe
    have registrationInjective :=
      wholeRestartActualOutputEdgeRegistration_injective_of_increment_ne_zero
        current nativeEdgeIndex output incrementNonzero
    have noJointSilence :=
      wholeRestartActualOutputIncrement_ne_zero_excludes_causalJointSilent
        current nativeEdgeIndex output outputNonzero incrementNonzero
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
                    nativeEdgeIndex).nextContact.prefixReceipt.wholeTangent‖ ^
                    2) ∨
          ∃ first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
                  current nativeEdgeIndex output first ≠ 0 ∧
              (wholeRestartNextPairOccurrence
                    current nativeEdgeIndex output first ≠ 0 ∨
                ∃ time :
                    Icc (0 : ℝ)
                      (run current nativeEdgeIndex).nextContact.time.1,
                  wholeRestartPairOccurrenceTrace
                    current nativeEdgeIndex output first time ≠ 0) ∧
              (wholeRestartVelocityTriadHeatCommutatorTrace
                    current nativeEdgeIndex first (output - first) = 0 ∨
                ∃ time :
                    Icc (0 : ℝ)
                      (run current nativeEdgeIndex).nextContact.time.1,
                  actualWholeVelocityBilinearEnergyOccurrence
                        (run current
                          nativeEdgeIndex).nextContact.prefixReceipt
                        first (output - first) time ≠ 0 ∧
                    actualWholeContinuousVelocityPairVector
                        (run current
                          nativeEdgeIndex).nextContact.prefixReceipt
                        first (output - first) time ≠ 0 ∧
                    (wholeRestartNextVelocityPairOccurrence
                          current nativeEdgeIndex first
                            (output - first) ≠ 0 ∨
                      (linearResidualTrace
                          wholeRestartSplicedVelocityPairOccurrenceTailKeep
                          (wholeRestartSplicedVelocityPairOccurrenceTail
                            current nativeEdgeIndex time 0) 0)
                            first (output - first) ≠ 0) ∧
                    run current (nativeEdgeIndex + 1) =
                      (run current nativeEdgeIndex).next)) := by
      rcases
          wholeRestartActualOutput_not_causalJointSilent_generates_tangent_or_pairInnovation
            current nativeEdgeIndex output noJointSilence with
        tangentOutputNonzero | pair
      · left
        have tangentNonzero :
            wholeRestartCrossingUnforcedTangentRow
              current nativeEdgeIndex ≠ 0 := by
          intro tangentZero
          exact tangentOutputNonzero
            (congrFun tangentZero output)
        exact
          ⟨tangentNonzero,
            wholeRestartCrossingUnforcedTangent_positiveTimePayment
              current nativeEdgeIndex tangentNonzero⟩
      · right
        rcases pair with ⟨first, innovationNonzero⟩
        obtain ⟨pairResponsibility, heatExhaustion⟩ :=
          wholeRestartPairDuhamelInnovationOccurrence_ne_zero_generates_heatCommutator_nativeExhaustion
            current nativeEdgeIndex output first innovationNonzero
        exact
          ⟨first, innovationNonzero, pairResponsibility, heatExhaustion⟩
    exact
      ⟨nativeEdgeIndex, nodeLeEdge, edgeLtNext,
        run_succ current nativeEdgeIndex, output, outputNonzero,
        incrementNonzero, causalSplit, registrationInjective,
        noJointSilence, nativeExhaustion⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

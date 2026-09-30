import H0mework.NavierStokes.EndpointWork.CofinalPhysicalSeparation
import H0mework.NavierStokes.EndpointTransport.PairDuhamelMacroWrite

/-!
# Positive endpoint kinetic atom in the existing causal whole write

The endpoint causal macro already writes the aligned kinetic residual tail,
the complete pair-Duhamel tail, and the source-generated unforced physical
successor in one frame.  This module keeps that carrier and proves that a
positive kinetic atom is quantitatively active inside its written kinetic
coordinate.

After every written coordinate, two later written kinetic residuals are
separated by more than half the atom.  They are the kinetic states of two
literal selected currents on the same old native run.  The exact finite gap
between them therefore contains a quantitatively nonzero physical velocity
edge whose full Fourier output square and componentwise tangent/pair
next-or-trace settlement are generated before quotient.

No parallel memory carrier, target path, output, pair, cutoff, time
partition, branch, faithfulness law, terminal certificate, or uniform
quantum is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAlignedCausalWrite

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomNativeCausalRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite

noncomputable section

/-- The aligned kinetic residual remains weakly null after the physical
velocity refinement used by the endpoint whole carrier. -/
theorem wholeRestartEndpointAlignedKineticResidual_weak_tendsto_zero
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime current)))
    (test : WholeRestartKineticEndpointState) :
    Tendsto
      (fun index =>
        inner ℂ
          (wholeRestartEndpointAlignedKineticResidual
            current elapsedBounded index) test)
      atTop (nhds 0) := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current elapsedBounded).family.endpointReceipt
  let receipt :=
    endpointReceipt.kineticReceipt.toGeneratedWholeRestartKineticWeakEndpoint
  have base :=
    wholeRestartKineticEndpointResidual_weak_tendsto_zero receipt test
  have refined :=
    base.comp endpointReceipt.velocitySubsubsequence_strictMono.tendsto_atTop
  simpa only [wholeRestartEndpointAlignedKineticResidual,
    wholeRestartEndpointKineticRefinementIndex, endpointReceipt, receipt,
    Function.comp_def] using refined

/-- Subtracting two coordinates of the written aligned kinetic carrier
cancels the common endpoint and recovers exactly the physical velocity
distance between the two source-selected actual currents. -/
theorem
    wholeRestartEndpointAlignedKineticResidual_sub_norm_sq_eq_selectedVelocity
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime current)))
    (earlier later : ℕ) :
    ‖wholeRestartEndpointAlignedKineticResidual
          current elapsedBounded later -
        wholeRestartEndpointAlignedKineticResidual
          current elapsedBounded earlier‖ ^ 2 =
      ‖wholeRestartContactVelocityState current
            (wholeRestartEndpointSelectedOccurrenceIndex
              current elapsedBounded later) -
          wholeRestartContactVelocityState current
            (wholeRestartEndpointSelectedOccurrenceIndex
              current elapsedBounded earlier)‖ ^ 2 := by
  let endpointReceipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current elapsedBounded).family.endpointReceipt
  have residualDifference :
      wholeRestartEndpointAlignedKineticResidual
            current elapsedBounded later -
          wholeRestartEndpointAlignedKineticResidual
            current elapsedBounded earlier =
        wholeRestartContactKineticState current
            (wholeRestartEndpointSelectedOccurrenceIndex
              current elapsedBounded later) -
          wholeRestartContactKineticState current
            (wholeRestartEndpointSelectedOccurrenceIndex
              current elapsedBounded earlier) := by
    unfold wholeRestartEndpointAlignedKineticResidual
      wholeRestartEndpointKineticRefinementIndex
      wholeRestartEndpointSelectedOccurrenceIndex
      wholeRestartKineticEndpointResidual
    dsimp only [endpointReceipt]
    abel
  rw [residualDifference]
  symm
  exact
    wholeRestartContactVelocityState_sub_norm_sq_eq_kinetic
      current
      (wholeRestartEndpointSelectedOccurrenceIndex
        current elapsedBounded later)
      (wholeRestartEndpointSelectedOccurrenceIndex
        current elapsedBounded earlier)

/-- A positive atom is quantitatively active in the existing endpoint whole
write.  The endpoint event writes its already generated unforced physical
successor, while every requested written kinetic coordinate has a later
written pair whose exact old-run gap contains a positive physical output
square.  Every nonzero output occurrence on the selected edge enters its
same-edge tangent/pair next-or-trace disposition. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_writtenKineticOutputSquareCausalWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      ∀ requestedWrittenIndex : ℕ,
        ∃ writtenEarlier writtenLater start steps index : ℕ,
          requestedWrittenIndex ≤ writtenEarlier ∧
            writtenEarlier < writtenLater ∧
            start =
              wholeRestartEndpointSelectedOccurrenceIndex
                current step.elapsedBounded writtenEarlier ∧
            start + steps =
              wholeRestartEndpointSelectedOccurrenceIndex
                current step.elapsedBounded writtenLater ∧
            0 < steps ∧
            step.physicalStageKineticEnergyAtom / 2 <
              ‖((wholeRestartEndpointCausalMacroTraceLedger
                    current step.elapsedBounded
                    (wholeRestartEndpointComponentMacroUpdate
                      accumulationRead)).1 writtenLater).2 -
                ((wholeRestartEndpointCausalMacroTraceLedger
                    current step.elapsedBounded
                    (wholeRestartEndpointComponentMacroUpdate
                      accumulationRead)).1 writtenEarlier).2‖ ^ 2 ∧
            step.physicalStageKineticEnergyAtom / 2 <
              (steps : ℝ) *
                ∑ offset ∈ Finset.range steps,
                  ‖wholeRestartContactVelocityState
                        current (start + offset + 1) -
                      wholeRestartContactVelocityState
                        current (start + offset)‖ ^ 2 ∧
            start ≤ index ∧
            index < start + steps ∧
            step.physicalStageKineticEnergyAtom /
                  (2 * (steps : ℝ) ^ 2) <
                ∑' wave :
                    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
                  ‖puncturedWholeVelocityEuclideanCoefficient
                    ((run current index).nextContact.physicalState -
                      (run current index).contact.physicalState) wave‖ ^ 2 ∧
            ‖wholeRestartContactVelocityState current (index + 1) -
                wholeRestartContactVelocityState current index‖ ^ 2 =
              ∑' wave :
                  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
                ‖puncturedWholeVelocityEuclideanCoefficient
                  ((run current index).nextContact.physicalState -
                    (run current index).contact.physicalState) wave‖ ^ 2 ∧
            (∃ wave :
                ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
              puncturedWholeVelocityEuclideanCoefficient
                ((run current index).nextContact.physicalState -
                  (run current index).contact.physicalState) wave ≠ 0) ∧
            ∀ wave :
                ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
              puncturedWholeVelocityEuclideanCoefficient
                    ((run current index).nextContact.physicalState -
                      (run current index).contact.physicalState) wave ≠ 0 →
                wave.1 ≠ 0 ∧
                  (run current index).nextContact.physicalState wave.1 -
                      (run current index).contact.physicalState wave.1 ≠ 0 ∧
                  (run current index).nextContact.physicalState wave.1 -
                        (run current index).contact.physicalState wave.1 =
                      wholeRestartCausalTangentGain
                            current index wave.1 •
                          wholeRestartCrossingUnforcedTangentRow
                            current index wave.1 +
                        (∑' first : IntegerWavevector,
                          wholeRestartPairDuhamelInnovationOccurrence
                            current index wave.1 first) ∧
                  (wholeRestartCrossingUnforcedTangentRow
                        current index wave.1 ≠ 0 ∨
                    ∃ first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                            current index wave.1 first ≠ 0 ∧
                        (wholeRestartNextPairOccurrence
                              current index wave.1 first ≠ 0 ∨
                          ∃ time :
                              Icc (0 : ℝ)
                                (run current index).nextContact.time.1,
                            wholeRestartPairOccurrenceTrace
                              current index wave.1 first time ≠ 0)) := by
  constructor
  · cases step with
    | advance elapsedBounded =>
        exact
          (wholeRestartEndpointCausalMacroFrame_physical_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
  · intro requestedWrittenIndex
    have weakTendstoZero :
        ∀ test : WholeRestartKineticEndpointState,
          Tendsto
            (fun writtenIndex =>
              inner ℂ
                (wholeRestartEndpointAlignedKineticResidual
                  current step.elapsedBounded writtenIndex) test)
            atTop (nhds 0) :=
      wholeRestartEndpointAlignedKineticResidual_weak_tendsto_zero
        current step.elapsedBounded
    have normSqTendsto :
        Tendsto
          (fun writtenIndex =>
            ‖wholeRestartEndpointAlignedKineticResidual
              current step.elapsedBounded writtenIndex‖ ^ 2)
          atTop (nhds step.physicalStageKineticEnergyAtom) :=
      step.alignedKineticResidual_norm_sq_tendsto_energyAtom
    obtain
        ⟨writtenEarlier, writtenLater, requestedLe,
          writtenEarlierLtLater, alignedSeparation⟩ :=
      weaklyNull_normSq_tendsto_positive_generates_cofinal_separation
        (wholeRestartEndpointAlignedKineticResidual
          current step.elapsedBounded)
        step.physicalStageKineticEnergyAtom atomPositive
        weakTendstoZero normSqTendsto requestedWrittenIndex
    let start :=
      wholeRestartEndpointSelectedOccurrenceIndex
        current step.elapsedBounded writtenEarlier
    let finish :=
      wholeRestartEndpointSelectedOccurrenceIndex
        current step.elapsedBounded writtenLater
    have startLtFinish : start < finish := by
      let endpointReceipt :=
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt
      exact
        endpointReceipt.subsequence_strictMono writtenEarlierLtLater
    let steps := finish - start
    have stepsPositive : 0 < steps := by
      dsimp only [steps]
      omega
    have finishEq : finish = start + steps := by
      dsimp only [steps]
      omega
    have writtenSeparation :
        step.physicalStageKineticEnergyAtom / 2 <
          ‖((wholeRestartEndpointCausalMacroTraceLedger
                current step.elapsedBounded
                (wholeRestartEndpointComponentMacroUpdate
                  accumulationRead)).1 writtenLater).2 -
            ((wholeRestartEndpointCausalMacroTraceLedger
                current step.elapsedBounded
                (wholeRestartEndpointComponentMacroUpdate
                  accumulationRead)).1 writtenEarlier).2‖ ^ 2 := by
      simpa [wholeRestartEndpointCausalMacroTraceLedger,
        wholeRestartEndpointComponentMacroUpdate,
        wholeRestartEndpointAlignedResponsibilityTail,
        wholeRestartEndpointAlignedResponsibility] using alignedSeparation
    have physicalSeparation :
        step.physicalStageKineticEnergyAtom / 2 <
          ‖wholeRestartContactVelocityState current finish -
              wholeRestartContactVelocityState current start‖ ^ 2 := by
      rw [←
        wholeRestartEndpointAlignedKineticResidual_sub_norm_sq_eq_selectedVelocity
          current step.elapsedBounded writtenEarlier writtenLater]
      exact alignedSeparation
    have pathBound :=
      norm_adjacent_path_sq_le_count_mul_sum_sq
        (wholeRestartContactVelocityState current) start steps
    rw [← finishEq] at pathBound
    have pathLower :
        step.physicalStageKineticEnergyAtom / 2 <
          (steps : ℝ) *
            ∑ offset ∈ Finset.range steps,
              ‖wholeRestartContactVelocityState
                    current (start + offset + 1) -
                  wholeRestartContactVelocityState
                    current (start + offset)‖ ^ 2 :=
      physicalSeparation.trans_le pathBound
    obtain ⟨offset, offsetMem, edgeLarge⟩ :=
      exists_native_edge_above_diluted_path_quantum
        (fun offset =>
          ‖wholeRestartContactVelocityState
                current (start + offset + 1) -
              wholeRestartContactVelocityState
                current (start + offset)‖ ^ 2)
        stepsPositive pathLower
    let index := start + offset
    have offsetLt : offset < steps :=
      Finset.mem_range.mp offsetMem
    have startLeIndex : start ≤ index :=
      Nat.le_add_right start offset
    have indexLtEnd : index < start + steps :=
      Nat.add_lt_add_left offsetLt start
    have edgeLargeAtIndex :
        step.physicalStageKineticEnergyAtom /
              (2 * (steps : ℝ) ^ 2) <
            ‖wholeRestartContactVelocityState current (index + 1) -
                wholeRestartContactVelocityState current index‖ ^ 2 := by
      simpa [index, Nat.add_assoc] using edgeLarge
    have edgeLedger :=
      nativeVelocityIncrement_norm_sq_eq_tsum current index
    have outputSquareLower :
        step.physicalStageKineticEnergyAtom /
              (2 * (steps : ℝ) ^ 2) <
            ∑' wave :
                ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
              ‖puncturedWholeVelocityEuclideanCoefficient
                ((run current index).nextContact.physicalState -
                  (run current index).contact.physicalState) wave‖ ^ 2 := by
      rw [← edgeLedger]
      exact edgeLargeAtIndex
    have stepsRealPositive : 0 < (steps : ℝ) := by
      exact_mod_cast stepsPositive
    have dilutedQuantumPositive :
        0 <
          step.physicalStageKineticEnergyAtom /
            (2 * (steps : ℝ) ^ 2) := by
      exact div_pos atomPositive
        (mul_pos (by norm_num) (sq_pos_of_pos stepsRealPositive))
    have outputExists :
        ∃ wave :
            ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
          puncturedWholeVelocityEuclideanCoefficient
            ((run current index).nextContact.physicalState -
              (run current index).contact.physicalState) wave ≠ 0 := by
      by_contra noOutput
      simp only [not_exists, not_not] at noOutput
      have outputSquareZero :
          (∑' wave :
              ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
            ‖puncturedWholeVelocityEuclideanCoefficient
              ((run current index).nextContact.physicalState -
                (run current index).contact.physicalState) wave‖ ^ 2) = 0 := by
        simp [noOutput]
      rw [outputSquareZero] at outputSquareLower
      linarith
    refine
      ⟨writtenEarlier, writtenLater, start, steps, index,
        requestedLe, writtenEarlierLtLater, rfl, ?_,
        stepsPositive, writtenSeparation, pathLower,
        startLeIndex, indexLtEnd, outputSquareLower,
        edgeLedger, outputExists, ?_⟩
    · exact finishEq.symm
    · intro wave coefficientNonzero
      exact
        nativeVelocityCoefficient_ne_zero_generates_causalResponsibility
          current index wave coefficientNonzero

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAlignedCausalWrite
end NavierStokes
end SaturationMonoid

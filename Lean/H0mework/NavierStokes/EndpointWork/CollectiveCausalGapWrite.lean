import H0mework.NavierStokes.EndpointWork.AlignedCausalWrite

/-!
# Collective causal velocity write of a positive endpoint kinetic atom

The actual old-run native edges already carry an exact causal
tangent/pair-Duhamel decomposition.  This module aggregates those physical
velocity writes before taking a norm.  The finite sum telescopes exactly to
the two source-selected endpoint velocities, so a positive endpoint kinetic
atom generates a cofinally late collective causal write whose square norm is
larger than half the atom.

Every summand and every Fourier row comes from the same actual source path.
No path, endpoint pair, cutoff, branch, cancellation certificate, target
state, or quantitative dilution is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite

open scoped BigOperators

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCofinalPhysicalSeparation

noncomputable section

/-! ## One actual native physical write -/

/-- The complete physical-velocity write on one actual old-run native edge.
The edge is fixed by the source recursion; this definition does not select a
new path or observer. -/
def wholeRestartNativeCausalVelocityWrite
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState
    ((run current index).nextContact.physicalState -
      (run current index).contact.physicalState)

/-- The one-edge write is exactly the adjacent difference on the actual
physical velocity path. -/
theorem wholeRestartNativeCausalVelocityWrite_eq_adjacent
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartNativeCausalVelocityWrite current index =
      wholeRestartContactVelocityState current (index + 1) -
        wholeRestartContactVelocityState current index := by
  unfold wholeRestartNativeCausalVelocityWrite
    wholeRestartContactVelocityState
  rw [run_succ, puncturedWholeVelocityEuclideanState_sub]
  change
    puncturedWholeVelocityEuclideanState
          (run current index).nextContact.physicalState -
        puncturedWholeVelocityEuclideanState
          (run current index).contact.physicalState =
      puncturedWholeVelocityEuclideanState
          (run current index).nextContact.physicalState -
        puncturedWholeVelocityEuclideanState
          (run current index).contact.physicalState
  rfl

/-- Each nonzero Fourier row of the same native physical write is the
Biot--Savart readout of the exact causal tangent plus the complete
pre-quotient pair innovation. -/
theorem
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartNativeCausalVelocityWrite current index wave =
      euclideanCoordinateRow
        (biotSavartVelocityCoefficient wave.1
          (wholeRestartCausalTangentGain current index wave.1 •
              wholeRestartCrossingUnforcedTangentRow
                current index wave.1 +
            ∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)) := by
  unfold wholeRestartNativeCausalVelocityWrite
  rw [puncturedWholeVelocityEuclideanState_apply]
  unfold puncturedWholeVelocityEuclideanCoefficient
  change
    euclideanCoordinateRow
        (biotSavartVelocityCoefficient wave.1
          ((run current index).nextContact.physicalState wave.1 -
            (run current index).contact.physicalState wave.1)) =
      _
  rw [nextContact_sub_contact_eq_causalTangent_add_pairInnovation
    current index wave.1 wave.2]

/-! ## Collective pre-quotient aggregation -/

/-- The finite collective physical write of the source-owned native path.
Cancellation is retained inside the physical Hilbert carrier until after all
actual edge writes have been added. -/
def wholeRestartCollectiveCausalVelocityWrite
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) : WholeRestartVelocityEndpointState :=
  ∑ offset ∈ Finset.range steps,
    wholeRestartNativeCausalVelocityWrite current (start + offset)

/-- The collective write telescopes exactly to the physical endpoint gap of
the same actual finite path. -/
theorem wholeRestartCollectiveCausalVelocityWrite_eq_gap
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    wholeRestartCollectiveCausalVelocityWrite current start steps =
      wholeRestartContactVelocityState current (start + steps) -
        wholeRestartContactVelocityState current start := by
  unfold wholeRestartCollectiveCausalVelocityWrite
  simp_rw [wholeRestartNativeCausalVelocityWrite_eq_adjacent]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Finset.sum_range_sub
      (fun offset : ℕ =>
        wholeRestartContactVelocityState current (start + offset))
      steps

/-- The collective write retains the exact causal tangent/pair compiler on
every Fourier row before the physical norm or any finite quotient is read. -/
theorem
    wholeRestartCollectiveCausalVelocityWrite_apply_eq_sum_causalTangent_add_pairInnovation
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartCollectiveCausalVelocityWrite current start steps wave =
      ∑ offset ∈ Finset.range steps,
        euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain
                  current (start + offset) wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current (start + offset) wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current (start + offset) wave.1 first)) := by
  unfold wholeRestartCollectiveCausalVelocityWrite
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro offset offsetMem
  exact
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation
      current (start + offset) wave

/-! ## Source-generated positive collective gap -/

/-- A positive endpoint kinetic atom generates, after every requested old-run
index, an actual finite collective causal write larger than half the atom.
The source selects both endpoints; the equality and row compiler keep all
cancellation inside the same physical carrier. -/
theorem
    physicalStageKineticEnergyAtom_pos_generates_cofinal_collectiveCausalGapWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next)
    (atomPositive : 0 < step.physicalStageKineticEnergyAtom)
    (requestedStart : ℕ) :
    ∃ start steps : ℕ,
      requestedStart ≤ start ∧
        0 < steps ∧
        wholeRestartCollectiveCausalVelocityWrite current start steps =
          wholeRestartContactVelocityState current (start + steps) -
            wholeRestartContactVelocityState current start ∧
        step.physicalStageKineticEnergyAtom / 2 <
          ‖wholeRestartCollectiveCausalVelocityWrite
              current start steps‖ ^ 2 ∧
        ∀ wave : NonzeroIntegerWavevector,
          wholeRestartCollectiveCausalVelocityWrite
                current start steps wave =
            ∑ offset ∈ Finset.range steps,
              euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        current (start + offset) wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        current (start + offset) wave.1 +
                    ∑' first : IntegerWavevector,
                      wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)) := by
  obtain
      ⟨earlier, later, requestedLe, earlierLtLater, separation⟩ :=
    physicalStageKineticEnergyAtom_pos_generates_cofinal_physicalSeparation
      step atomPositive requestedStart
  let steps := later - earlier
  have stepsPositive : 0 < steps := by
    dsimp only [steps]
    omega
  have laterEq : later = earlier + steps := by
    dsimp only [steps]
    omega
  refine
    ⟨earlier, steps, requestedLe, stepsPositive,
      wholeRestartCollectiveCausalVelocityWrite_eq_gap
        current earlier steps, ?_, ?_⟩
  · rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap, ← laterEq]
    exact separation
  · intro wave
    exact
      wholeRestartCollectiveCausalVelocityWrite_apply_eq_sum_causalTangent_add_pairInnovation
        current earlier steps wave

/-- One actual endpoint macro step writes its source-generated unforced
physical successor and internally exhausts its kinetic atom: either the atom
is zero, or every requested old-run index has a later collective causal
velocity write carrying more than half the atom. -/
theorem
    wholeRestartEndpointMacroStep_generates_zero_or_collectiveCausalGap_nativeWholeWrite
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (wholeRestartEndpointCausalMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        next ∧
      (step.physicalStageKineticEnergyAtom = 0 ∨
        ∀ requestedStart : ℕ,
          ∃ start steps : ℕ,
            requestedStart ≤ start ∧
              0 < steps ∧
              wholeRestartCollectiveCausalVelocityWrite
                    current start steps =
                wholeRestartContactVelocityState
                    current (start + steps) -
                  wholeRestartContactVelocityState current start ∧
              step.physicalStageKineticEnergyAtom / 2 <
                ‖wholeRestartCollectiveCausalVelocityWrite
                    current start steps‖ ^ 2 ∧
              ∀ wave : NonzeroIntegerWavevector,
                wholeRestartCollectiveCausalVelocityWrite
                      current start steps wave =
                  ∑ offset ∈ Finset.range steps,
                    euclideanCoordinateRow
                      (biotSavartVelocityCoefficient wave.1
                        (wholeRestartCausalTangentGain
                              current (start + offset) wave.1 •
                            wholeRestartCrossingUnforcedTangentRow
                              current (start + offset) wave.1 +
                          ∑' first : IntegerWavevector,
                            wholeRestartPairDuhamelInnovationOccurrence
                              current (start + offset) wave.1 first))) := by
  constructor
  · cases step with
    | advance elapsedBounded =>
        exact
          (wholeRestartEndpointCausalMacroFrame_physical_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
  · let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded).family.endpointReceipt
    rcases endpointReceipt.kineticReceipt.defect_disposition with
      defectPositive | defectZero
    · right
      have atomPositive : 0 < step.physicalStageKineticEnergyAtom := by
        rw [step.physicalStageKineticEnergyAtom_eq_defect]
        exact defectPositive
      exact
        physicalStageKineticEnergyAtom_pos_generates_cofinal_collectiveCausalGapWrite
          step atomPositive
    · left
      rw [step.physicalStageKineticEnergyAtom_eq_defect]
      exact defectZero.1

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
end NavierStokes
end SaturationMonoid

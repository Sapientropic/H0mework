import H0mework.NavierStokes.EndpointSettlement.AnnularEndpointNativeCausalWrite
import H0mework.NavierStokes.EndpointWork.AnchoredMixedWork

/-!
# Whole-block causal action on adjacent reduced-core scales

Adjacent source-generated reduced-core occurrences are distinct on the
complete physical vorticity carrier.  Faithfulness of the transverse
Biot--Savart carrier transports that distinction to the complete physical
velocity state.  Consequently the entire actual native block between the two
occurrences has:

* a nonzero collective physical velocity write;
* a positive sum of literal native write squares;
* an exact quadratic kinetic boundary and its complete output×pair compiler;
* the existing same-block tangent/pair native causal receipt.

All sums remain on the authoritative whole restart run.  No coordinate,
cutoff, path, branch, nonzero witness, target state, or continuation
certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- The complete physical velocity observer separates adjacent generated
reduced-core contacts.  This is whole-carrier faithfulness, not a selected
Fourier-coordinate argument. -/
theorem
    WholeRestartReducedCoreScaleLineage.adjacentVelocityState_ne
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence node) ≠
      wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence (node + 1)) := by
  intro velocityEq
  apply scale.adjacentPhysicalState_ne node
  exact
    puncturedWholeVelocityEuclideanState_eq_imp_eq_of_zero_transverse
      (run initial
        (scale.absoluteOccurrence node)).contact.physicalState
      (run initial
        (scale.absoluteOccurrence (node + 1))).contact.physicalState
      (run initial
        (scale.absoluteOccurrence node)).contact.physicalState_zero
      (run initial
        (scale.absoluteOccurrence (node + 1))).contact.physicalState_zero
      (run initial
        (scale.absoluteOccurrence node)).contact.transverse
      (run initial
        (scale.absoluteOccurrence (node + 1))).contact.transverse
      velocityEq

/-- Complete square action of every literal native physical velocity write
inside one adjacent reduced-core scale block. -/
def WholeRestartReducedCoreScaleLineage.wholeBlockNativeVelocitySquare
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range (scale.nextScaleGap node),
    ‖wholeRestartNativeCausalVelocityWrite
      initial (scale.absoluteOccurrence node + offset)‖ ^ 2

/-- Incoming-velocity work of the same complete native block. -/
def WholeRestartReducedCoreScaleLineage.wholeBlockIncomingVelocityWork
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range (scale.nextScaleGap node),
    RCLike.re (inner ℂ
      (wholeRestartContactVelocityState
        initial (scale.absoluteOccurrence node + offset))
      (wholeRestartNativeCausalVelocityWrite
        initial (scale.absoluteOccurrence node + offset)))

/-- Complete pre-quotient tangent/output×pair quadratic boundary of the same
adjacent scale block. -/
def WholeRestartReducedCoreScaleLineage.wholeBlockComponentKineticBoundary
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range (scale.nextScaleGap node),
    (2 *
        (∑' wave : NonzeroIntegerWavevector,
          (RCLike.re (inner ℂ
              (wholeRestartContactVelocityState
                initial (scale.absoluteOccurrence node + offset) wave)
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        initial
                        (scale.absoluteOccurrence node + offset) wave.1 •
                      wholeRestartCrossingUnforcedTangentRow
                        initial
                        (scale.absoluteOccurrence node + offset) wave.1)))) +
            ∑' first : IntegerWavevector,
              RCLike.re (inner ℂ
                (wholeRestartContactVelocityState
                  initial (scale.absoluteOccurrence node + offset) wave)
                (euclideanCoordinateRow
                  (biotSavartVelocityCoefficient wave.1
                    (wholeRestartPairDuhamelInnovationOccurrence
                      initial
                      (scale.absoluteOccurrence node + offset)
                      wave.1 first)))))) +
      ‖wholeRestartNativeCausalVelocityWrite
        initial (scale.absoluteOccurrence node + offset)‖ ^ 2)

/-- The entire actual block writes exactly the adjacent reduced-core physical
velocity gap. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockCollectiveVelocityWrite_eq_gap
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    wholeRestartCollectiveCausalVelocityWrite
        initial (scale.absoluteOccurrence node) (scale.nextScaleGap node) =
      wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence (node + 1)) -
        wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence node) := by
  rw [wholeRestartCollectiveCausalVelocityWrite_eq_gap,
    scale.absoluteOccurrence_add_nextScaleGap node]

/-- The source-generated adjacent scale block has a nonzero collective
physical velocity write. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockCollectiveVelocityWrite_ne_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    wholeRestartCollectiveCausalVelocityWrite
        initial (scale.absoluteOccurrence node) (scale.nextScaleGap node) ≠
      0 := by
  rw [scale.wholeBlockCollectiveVelocityWrite_eq_gap node]
  exact sub_ne_zero.mpr (scale.adjacentVelocityState_ne node).symm

/-- At least one literal native write in every adjacent scale block is
nonzero, so the complete source-owned write-square action is positive. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockNativeVelocitySquare_pos
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    0 < scale.wholeBlockNativeVelocitySquare node := by
  have collectiveNonzero :=
    scale.wholeBlockCollectiveVelocityWrite_ne_zero node
  have existsWriteNonzero :
      ∃ offset ∈ Finset.range (scale.nextScaleGap node),
        wholeRestartNativeCausalVelocityWrite
            initial (scale.absoluteOccurrence node + offset) ≠ 0 := by
    by_contra noWrite
    push Not at noWrite
    apply collectiveNonzero
    unfold wholeRestartCollectiveCausalVelocityWrite
    exact Finset.sum_eq_zero noWrite
  unfold WholeRestartReducedCoreScaleLineage.wholeBlockNativeVelocitySquare
  apply Finset.sum_pos'
  · intro offset _offsetMem
    exact sq_nonneg _
  · obtain ⟨offset, offsetMem, writeNonzero⟩ := existsWriteNonzero
    refine ⟨offset, offsetMem, ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr writeNonzero)

/-- The exact quadratic boundary of the whole adjacent scale block, with
the native write squares kept as an explicit source-owned action. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockKineticBoundary_telescope
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    2 * scale.wholeBlockIncomingVelocityWork node +
        scale.wholeBlockNativeVelocitySquare node =
      ‖wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence (node + 1))‖ ^ 2 -
        ‖wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence node)‖ ^ 2 := by
  rw [WholeRestartReducedCoreScaleLineage.wholeBlockIncomingVelocityWork,
    WholeRestartReducedCoreScaleLineage.wholeBlockNativeVelocitySquare,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  simpa only [scale.absoluteOccurrence_add_nextScaleGap node] using
    wholeRestartFiniteCausalKineticBoundary_telescope
      initial (scale.absoluteOccurrence node) (scale.nextScaleGap node)

/-- Actual unforced kinetic descent pays the complete native write-square
action by negative incoming-velocity work on the same block. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockNativeVelocitySquare_le_work
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    scale.wholeBlockNativeVelocitySquare node ≤
      -2 * scale.wholeBlockIncomingVelocityWork node := by
  have boundaryNonpositive :=
    wholeRestartFiniteCausalKineticBoundary_nonpos
      initial (scale.absoluteOccurrence node) (scale.nextScaleGap node)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at boundaryNonpositive
  change
    2 * scale.wholeBlockIncomingVelocityWork node +
        scale.wholeBlockNativeVelocitySquare node ≤ 0
    at boundaryNonpositive
  linarith

/-- Positive whole-block write action forces strictly negative total
incoming-velocity work on the same actual block. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockIncomingVelocityWork_neg
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    scale.wholeBlockIncomingVelocityWork node < 0 := by
  have squarePositive := scale.wholeBlockNativeVelocitySquare_pos node
  have squareLeWork := scale.wholeBlockNativeVelocitySquare_le_work node
  linarith

/-- The complete tangent/output×pair expansion is exactly the same physical
kinetic boundary of the adjacent source-generated scale block. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockComponentKineticBoundary_telescope
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    scale.wholeBlockComponentKineticBoundary node =
      ‖wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence (node + 1))‖ ^ 2 -
        ‖wholeRestartContactVelocityState
          initial (scale.absoluteOccurrence node)‖ ^ 2 := by
  unfold WholeRestartReducedCoreScaleLineage.wholeBlockComponentKineticBoundary
  simpa only [scale.absoluteOccurrence_add_nextScaleGap node] using
    wholeRestartFiniteCausalComponentKineticBoundary_telescope
      initial (scale.absoluteOccurrence node) (scale.nextScaleGap node)

/-- The same complete output×pair boundary is nonpositive by actual unforced
kinetic descent. -/
theorem
    WholeRestartReducedCoreScaleLineage.wholeBlockComponentKineticBoundary_nonpos
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (scale : WholeRestartReducedCoreScaleLineage initial)
    (node : ℕ) :
    scale.wholeBlockComponentKineticBoundary node ≤ 0 := by
  unfold WholeRestartReducedCoreScaleLineage.wholeBlockComponentKineticBoundary
  exact
    wholeRestartFiniteCausalComponentKineticBoundary_nonpos
      initial (scale.absoluteOccurrence node) (scale.nextScaleGap node)

/-- One actual endpoint macro step writes its complete product successor and,
for every source-generated reduced-core node, exposes the entire intervening
native block as one nonzero whole-carrier causal action.  The physical
vorticity split, velocity gap, positive native square action, kinetic payment,
complete output×pair boundary, and one literal causal edge all retain the same
authoritative whole-restart provenance. -/
theorem
    wholeRestartEndpointMacroStep_reducedCore_generates_wholeBlockCausalAction
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
        0 < scale.nextScaleGap node ∧
          (run current
              (scale.absoluteOccurrence node)).contact.physicalState =
            (run current
                (scale.absoluteOccurrence
                  (node + 1))).contact.physicalState +
              scale.annularPhysicalGapTrace node ∧
          scale.annularPhysicalGapTrace node ≠ 0 ∧
          wholeRestartCollectiveCausalVelocityWrite
              current (scale.absoluteOccurrence node)
                (scale.nextScaleGap node) =
            wholeRestartContactVelocityState
                current (scale.absoluteOccurrence (node + 1)) -
              wholeRestartContactVelocityState
                current (scale.absoluteOccurrence node) ∧
          wholeRestartCollectiveCausalVelocityWrite
                current (scale.absoluteOccurrence node)
                  (scale.nextScaleGap node) ≠ 0 ∧
          0 < scale.wholeBlockNativeVelocitySquare node ∧
          2 * scale.wholeBlockIncomingVelocityWork node +
                scale.wholeBlockNativeVelocitySquare node =
            ‖wholeRestartContactVelocityState
                current (scale.absoluteOccurrence (node + 1))‖ ^ 2 -
              ‖wholeRestartContactVelocityState
                current (scale.absoluteOccurrence node)‖ ^ 2 ∧
          scale.wholeBlockNativeVelocitySquare node ≤
            -2 * scale.wholeBlockIncomingVelocityWork node ∧
          scale.wholeBlockComponentKineticBoundary node =
            ‖wholeRestartContactVelocityState
                current (scale.absoluteOccurrence (node + 1))‖ ^ 2 -
              ‖wholeRestartContactVelocityState
                current (scale.absoluteOccurrence node)‖ ^ 2 ∧
          scale.wholeBlockComponentKineticBoundary node ≤ 0 ∧
          Nonempty
            (WholeRestartReducedCoreAdjacentNativeCausalWrite scale node) := by
  obtain ⟨frame, causalWrite⟩ :=
    wholeRestartEndpointMacroStep_reducedCore_generates_adjacentNativeCausalWrite
      macroStep
  refine ⟨frame, ?_⟩
  intro scale node
  exact
    ⟨scale.nextScaleGap_pos node,
      scale.annularPhysical_nextScale_split node,
      scale.annularPhysicalGapTrace_ne_zero node,
      scale.wholeBlockCollectiveVelocityWrite_eq_gap node,
      scale.wholeBlockCollectiveVelocityWrite_ne_zero node,
      scale.wholeBlockNativeVelocitySquare_pos node,
      scale.wholeBlockKineticBoundary_telescope node,
      scale.wholeBlockNativeVelocitySquare_le_work node,
      scale.wholeBlockComponentKineticBoundary_telescope node,
      scale.wholeBlockComponentKineticBoundary_nonpos node,
      causalWrite scale node⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

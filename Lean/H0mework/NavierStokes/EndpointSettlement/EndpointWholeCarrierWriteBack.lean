import H0mework.NavierStokes.EndpointSettlement.AnnularPhysicalScaleFeedback
import H0mework.NavierStokes.EndpointWork.SourceAnchorNativePairMacroWriteBack

/-!
# Reduced-core whole carriers written by the actual endpoint event

The endpoint macro already writes the complete aligned responsibility and
the old run's full pre-aggregation pair-Duhamel tail.  The reduced-core
lineage now also has an effective residual process on the authoritative
whole physical-state tail.  This module forms their conservative product at
the endpoint event itself.

The resulting frame has one physical projection: the source-generated
unforced endpoint successor.  Its trace ledger simultaneously retains the
complete aligned, pair, and whole physical tails of the old run.  Therefore
every source-generated reduced-core scale node, its adjacent physical split,
its pair-table split, and its positive whole-annular no-silent alternative
are present before the endpoint quotient.

No scale path, node, mode, branch, endpoint target, continuation, nonzero
witness, or faithfulness certificate is stored in the endpoint source.
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomSourceAnchorNativePairMacroWriteBack
open AffineRelaxation
open ResidualProjection

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-! ## Conservative endpoint product process -/

/-- Versioned endpoint responsibility retaining the old aligned/full-pair
carrier and the authoritative whole physical-state tail. -/
abbrev WholeRestartEndpointFullPairPhysicalResponsibility :=
  WholeRestartEndpointFullPairResponsibility ×
    WholeRestartPhysicalVorticityTail

/-- Before the endpoint write all three complete old-run carriers are
pending. -/
def wholeRestartEndpointFullPairPhysicalMacroPending
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointFullPairPhysicalResponsibility
  | accumulationRead =>
      (wholeRestartEndpointFullPairMacroPending
          initial elapsedBounded accumulationRead,
        wholeRestartPhysicalVorticityTail initial 0 0)
  | endpointWritten => 0

/-- The identical endpoint event writes all three complete carriers into one
trace ledger. -/
def wholeRestartEndpointFullPairPhysicalMacroTraceLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointFullPairPhysicalResponsibility
  | accumulationRead => 0
  | endpointWritten =>
      (wholeRestartEndpointFullPairMacroTraceLedger
          initial elapsedBounded endpointWritten,
        wholeRestartPhysicalVorticityTail initial 0 0)

/-- The endpoint event consumes the complete product responsibility. -/
def wholeRestartEndpointFullPairPhysicalMacroKeep :
    WholeRestartEndpointFullPairPhysicalResponsibility →ₗ[ℂ]
      WholeRestartEndpointFullPairPhysicalResponsibility :=
  0

/-- Effective residual process of the same-event endpoint product write. -/
def generatedWholeRestartEndpointFullPairPhysicalMacroEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess ℂ
      WholeRestartEndpointFullPairPhysicalResponsibility
      WholeRestartEndpointComponentMacroPhase where
  target := 0
  keep := wholeRestartEndpointFullPairPhysicalMacroKeep
  residual :=
    wholeRestartEndpointFullPairPhysicalMacroPending
      initial elapsedBounded
  update := wholeRestartEndpointComponentMacroUpdate
  residual_transport_law := by
    intro phase
    cases phase <;> rfl

/-- Forgetting the new physical coordinate recovers the old full-pair
pending carrier and trace ledger definitionally. -/
theorem wholeRestartEndpointFullPairPhysicalMacro_conservative
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (phase : WholeRestartEndpointComponentMacroPhase) :
    (wholeRestartEndpointFullPairPhysicalMacroPending
        initial elapsedBounded phase).1 =
        wholeRestartEndpointFullPairMacroPending
          initial elapsedBounded phase ∧
      (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
          initial elapsedBounded phase).1 =
        wholeRestartEndpointFullPairMacroTraceLedger
          initial elapsedBounded phase := by
  cases phase <;> constructor <;> rfl

/-- The unique endpoint trace is the complete aligned/full-pair/physical
responsibility pending before the write. -/
theorem
    wholeRestartEndpointFullPairPhysicalMacro_trace_eq_responsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    linearResidualTrace
        wholeRestartEndpointFullPairPhysicalMacroKeep
        (wholeRestartEndpointFullPairPhysicalMacroPending
          initial elapsedBounded accumulationRead) =
      (wholeRestartEndpointFullPairMacroPending
          initial elapsedBounded accumulationRead,
        wholeRestartPhysicalVorticityTail initial 0 0) := by
  simp [linearResidualTrace,
    wholeRestartEndpointFullPairPhysicalMacroKeep,
    wholeRestartEndpointFullPairPhysicalMacroPending]

/-- Exact same-event write-back of the complete product carrier. -/
theorem wholeRestartEndpointFullPairPhysicalMacro_ledger_writeBack
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointFullPairPhysicalMacroTraceLedger
        initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      wholeRestartEndpointFullPairPhysicalMacroTraceLedger
          initial elapsedBounded accumulationRead +
        linearResidualTrace
          wholeRestartEndpointFullPairPhysicalMacroKeep
          (wholeRestartEndpointFullPairPhysicalMacroPending
            initial elapsedBounded accumulationRead) := by
  simp [wholeRestartEndpointFullPairPhysicalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointFullPairPhysicalMacro_trace_eq_responsibility,
    wholeRestartEndpointFullPairMacroPending,
    wholeRestartEndpointFullPairMacroTraceLedger]

/-! ## Exact old-run readout before the endpoint quotient -/

/-- Every old-run whole physical state is literally present in the
endpoint-written product ledger. -/
theorem wholeRestartEndpointFullPairPhysicalMacro_writtenPhysicalState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
        initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
          index =
      (run initial index).contact.physicalState := by
  change
    (run initial (0 + 0 + index)).contact.physicalState =
      (run initial index).contact.physicalState
  have indexEq : 0 + 0 + index = index := by
    omega
  rw [indexEq]

/-- Every old-run complete pair table is literally present in the same
endpoint-written product ledger. -/
theorem wholeRestartEndpointFullPairPhysicalMacro_writtenPairTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
        initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1.2
          index =
      wholeRestartPairDuhamelTable initial index := by
  simp [wholeRestartEndpointFullPairPhysicalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointFullPairMacroTraceLedger,
    wholeRestartPairDuhamelTail,
    wholeRestartPairDuhamelPathTable]

/-! ## The actual unforced endpoint frame -/

/-- The product frame keeps one physical projection and two residual
coordinates: pending responsibility and written trace. -/
def wholeRestartEndpointFullPairPhysicalMacroFrame
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (phase : WholeRestartEndpointComponentMacroPhase) :
    GeneratedWholeRestartCurrent ν ×
      (WholeRestartEndpointFullPairPhysicalResponsibility ×
        WholeRestartEndpointFullPairPhysicalResponsibility) :=
  (wholeRestartEndpointComponentMacroPhysicalCurrent
      initial elapsedBounded phase,
    wholeRestartEndpointFullPairPhysicalMacroPending
      initial elapsedBounded phase,
    wholeRestartEndpointFullPairPhysicalMacroTraceLedger
      initial elapsedBounded phase)

/-- One actual endpoint edge writes the source-generated unforced successor
and all three complete old-run carriers in one frame equation. -/
theorem wholeRestartEndpointFullPairPhysicalMacroFrame_update
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointFullPairPhysicalMacroFrame
        current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        (wholeRestartEndpointFullPairMacroPending
            current step.elapsedBounded accumulationRead,
          wholeRestartPhysicalVorticityTail current 0 0)) := by
  cases step with
  | advance elapsedBounded =>
      apply Prod.ext
      · exact
          (wholeRestartEndpointComponentMacroPhysicalCurrent_update
              elapsedBounded).trans
            (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
              current elapsedBounded)
      · rfl

/-- The physical coordinate of the same product write is genuinely the
existing unforced state at positive absolute time past the accumulation
endpoint. -/
theorem wholeRestartEndpointFullPairPhysicalMacroFrame_unforcedPastEndpoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartVelocityAccumulationTime initial <
        (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
          initial elapsedBounded).1 ∧
      let next :=
        (wholeRestartEndpointFullPairPhysicalMacroFrame
          initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1
      0 < next.duration ∧
        next.receipt.wholePath
            ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
          next.initialState := by
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  exact
    ⟨continuation.selectedAbsoluteTime_gt_accumulation,
      continuation.next_duration_pos,
      continuation.next_receipt_initial⟩

/-! ## Reduced-core scale fusion inside the endpoint ledger -/

/-- Every generated reduced-core node is retained in the endpoint product
before quotient.  Its whole physical and pair states are literal ledger
coordinates; both adjacent residual splits still commute there, and the
positive whole annular responsibility survives in the next carrier or in
the unique projected gap. -/
theorem
    wholeRestartEndpointFullPairPhysicalMacro_writes_everyReducedCoreScaleNode
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ (scale : WholeRestartReducedCoreScaleLineage initial) (step : ℕ),
      (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
          initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
            (scale.absoluteOccurrence step) =
          (run initial
            (scale.absoluteOccurrence step)).contact.physicalState ∧
      (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
          initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1.2
            (scale.absoluteOccurrence step) =
          wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence step) ∧
      (run initial
          (scale.absoluteOccurrence step)).contact.physicalState =
        (run initial
          (scale.absoluteOccurrence (step + 1))).contact.physicalState +
            scale.annularPhysicalGapTrace step ∧
      wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence step) =
        wholeRestartPairDuhamelTable
            initial (scale.absoluteOccurrence (step + 1)) +
          scale.sourcePairDuhamelGapTrace step ∧
      0 < scale.annularCoefficientMass step ∧
      complexSharpSupportProjection
            (scale.annularModes step)
            (run initial
              (scale.absoluteOccurrence step)).contact.physicalState ≠ 0 ∧
      (complexSharpSupportProjection
            (scale.annularModes step)
            (run initial
              (scale.absoluteOccurrence (step + 1))).contact.physicalState ≠ 0 ∨
        complexSharpSupportProjection
            (scale.annularModes step)
            (scale.annularPhysicalGapTrace step) ≠ 0) := by
  intro scale step
  have annularNoSilent :=
    scale.annularWhole_nextScaleNoSilentWrite step
  exact
    ⟨wholeRestartEndpointFullPairPhysicalMacro_writtenPhysicalState
        initial elapsedBounded (scale.absoluteOccurrence step),
      wholeRestartEndpointFullPairPhysicalMacro_writtenPairTable
        initial elapsedBounded (scale.absoluteOccurrence step),
      scale.annularPhysical_nextScale_split step,
      scale.pairDuhamel_nextScale_gapTrace_split step,
      scale.annularCoefficientMass_pos step,
      annularNoSilent.1,
      annularNoSilent.2⟩

/-- The actual endpoint edge and all generated reduced-core node
responsibilities are written by one source-facing theorem.  The scale
lineage remains universally quantified in the conclusion rather than stored
in the endpoint source. -/
theorem wholeRestartEndpointMacroStep_writes_fullPairPhysicalReducedCore
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointFullPairPhysicalMacroFrame
        current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        (wholeRestartEndpointFullPairMacroPending
            current step.elapsedBounded accumulationRead,
          wholeRestartPhysicalVorticityTail current 0 0)) ∧
      ∀ (scale : WholeRestartReducedCoreScaleLineage current) (node : ℕ),
        (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
            current step.elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
              (scale.absoluteOccurrence node) =
            (run current
              (scale.absoluteOccurrence node)).contact.physicalState ∧
        (wholeRestartEndpointFullPairPhysicalMacroTraceLedger
            current step.elapsedBounded
            (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1.2
              (scale.absoluteOccurrence node) =
            wholeRestartPairDuhamelTable
              current (scale.absoluteOccurrence node) ∧
        (run current
            (scale.absoluteOccurrence node)).contact.physicalState =
          (run current
            (scale.absoluteOccurrence (node + 1))).contact.physicalState +
              scale.annularPhysicalGapTrace node ∧
        wholeRestartPairDuhamelTable
              current (scale.absoluteOccurrence node) =
          wholeRestartPairDuhamelTable
              current (scale.absoluteOccurrence (node + 1)) +
            scale.sourcePairDuhamelGapTrace node ∧
        0 < scale.annularCoefficientMass node ∧
        complexSharpSupportProjection
              (scale.annularModes node)
              (run current
                (scale.absoluteOccurrence node)).contact.physicalState ≠ 0 ∧
        (complexSharpSupportProjection
              (scale.annularModes node)
              (run current
                (scale.absoluteOccurrence
                  (node + 1))).contact.physicalState ≠ 0 ∨
          complexSharpSupportProjection
              (scale.annularModes node)
              (scale.annularPhysicalGapTrace node) ≠ 0) := by
  exact
    ⟨wholeRestartEndpointFullPairPhysicalMacroFrame_update step,
      wholeRestartEndpointFullPairPhysicalMacro_writes_everyReducedCoreScaleNode
        current step.elapsedBounded⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

import H0mework.NavierStokes.VelocityEndpoint.AlignedResponsibilityProcess

/-!
# Same-event endpoint macro write for component and kinetic responsibility

The source-owned endpoint macro already writes the complete pre-quotient
component-occurrence stream and an actual whole unforced current beyond the
accumulation endpoint.  The kinetic endpoint residual has now been aligned
with those exact occurrences.  This module performs the common macro write:

```text
read  = aligned component occurrence × kinetic residual stream
write = existing endpoint phase and existing absolute unforced current
trace = the complete aligned stream written to the endpoint ledger.
```

Thus a positive kinetic defect is retained in the kinetic coordinate of the
same generated macro trace while every component coordinate keeps its old
native zero/next/trace disposition.  No branch, cutoff, defect witness,
target path, continuation witness or faithfulness certificate is supplied.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## One common source-owned macro residual -/

/-- Before the endpoint write, the complete aligned stream is pending; after
the write, no aligned responsibility remains in the pending coordinate. -/
def wholeRestartEndpointAlignedMacroPending
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointAlignedResponsibilityTail
  | accumulationRead =>
      wholeRestartEndpointAlignedResponsibilityTail
        initial elapsedBounded 0
  | endpointWritten => 0

/-- The identical endpoint event writes the entire aligned stream, without
an intervening Fourier, pair or scalar quotient. -/
def wholeRestartEndpointAlignedMacroTraceLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointAlignedResponsibilityTail
  | accumulationRead => 0
  | endpointWritten =>
      wholeRestartEndpointAlignedResponsibilityTail
        initial elapsedBounded 0

/-- The endpoint macro consumes the whole pending stream because that same
stream is written exactly into the trace ledger. -/
def wholeRestartEndpointAlignedMacroKeep :
    WholeRestartEndpointAlignedResponsibilityTail →ₗ[ℂ]
      WholeRestartEndpointAlignedResponsibilityTail :=
  0

/-- Effective residual process of the common endpoint macro event. -/
def generatedWholeRestartEndpointAlignedMacroEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess ℂ
      WholeRestartEndpointAlignedResponsibilityTail
      WholeRestartEndpointComponentMacroPhase where
  target := 0
  keep := wholeRestartEndpointAlignedMacroKeep
  residual := wholeRestartEndpointAlignedMacroPending
    initial elapsedBounded
  update := wholeRestartEndpointComponentMacroUpdate
  residual_transport_law := by
    intro phase
    cases phase <;> rfl

/-- The endpoint contact reads the aligned stream and writes the existing
endpoint phase in one reflexive source event. -/
def generatedWholeRestartEndpointAlignedMacroQuery
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ReflexiveQuery WholeRestartEndpointComponentMacroPhase
      WholeRestartEndpointAlignedResponsibilityTail where
  read := wholeRestartEndpointAlignedMacroPending initial elapsedBounded
  write := wholeRestartEndpointComponentMacroUpdate

@[simp] theorem generatedWholeRestartEndpointAlignedMacroQuery_run
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (generatedWholeRestartEndpointAlignedMacroQuery
        initial elapsedBounded).run accumulationRead =
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        endpointWritten) := by
  rfl

/-- The uniquely forced macro trace is the complete aligned stream. -/
theorem wholeRestartEndpointAlignedMacro_trace_eq_stream
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    linearResidualTrace wholeRestartEndpointAlignedMacroKeep
        (wholeRestartEndpointAlignedMacroPending
          initial elapsedBounded accumulationRead) =
      wholeRestartEndpointAlignedResponsibilityTail
        initial elapsedBounded 0 := by
  simp [linearResidualTrace, wholeRestartEndpointAlignedMacroKeep,
    wholeRestartEndpointAlignedMacroPending]

/-- Exact endpoint write-back of both responsibility coordinates. -/
theorem wholeRestartEndpointAlignedMacro_ledger_writeBack
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
          accumulationRead +
        linearResidualTrace wholeRestartEndpointAlignedMacroKeep
          (wholeRestartEndpointAlignedMacroPending
            initial elapsedBounded accumulationRead) := by
  simp [wholeRestartEndpointAlignedMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointAlignedMacro_trace_eq_stream]

/-- Pending plus written responsibility is exactly conserved by the macro
update on the whole aligned carrier. -/
theorem wholeRestartEndpointAlignedMacro_noSilentLoss
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroPending
          initial elapsedBounded accumulationRead +
        wholeRestartEndpointAlignedMacroTraceLedger
          initial elapsedBounded accumulationRead =
      wholeRestartEndpointAlignedMacroPending initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) +
        wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) := by
  simp [wholeRestartEndpointAlignedMacroPending,
    wholeRestartEndpointAlignedMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate]

/-! ## Exact coordinates of the written whole carrier -/

/-- Every written component coordinate is literally the old pre-quotient
occurrence at the same source-selected actual current. -/
theorem wholeRestartEndpointAlignedMacro_writtenComponent
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) index).1 =
      wholeRestartEndpointComponentOccurrenceStream initial
        (wholeRestartEndpointSelectedOccurrenceIndex
          initial elapsedBounded index) := by
  simp [wholeRestartEndpointAlignedMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointAlignedResponsibilityTail,
    wholeRestartEndpointAlignedResponsibility,
    wholeRestartEndpointComponentTraceLedger]

/-- Every written kinetic coordinate is the complete residual read from the
identical selected actual current. -/
theorem wholeRestartEndpointAlignedMacro_writtenKinetic
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) index).2 =
      wholeRestartEndpointAlignedKineticResidual
        initial elapsedBounded index := by
  simp [wholeRestartEndpointAlignedMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointAlignedResponsibilityTail,
    wholeRestartEndpointAlignedResponsibility]

/-- The written component occurrence retains the native source exhaustion:
faithful zero, a nonzero next keep, or its uniquely forced trace. -/
theorem
    wholeRestartEndpointAlignedMacro_writtenComponent_zero_or_nativeNext_or_trace
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    let selected := wholeRestartEndpointSelectedOccurrenceIndex
      initial elapsedBounded index
    (wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) index).1.1 = 0 ∨
      wholeRestartComponentGluingResidualRow initial (selected + 1) ≠ 0 ∨
        (wholeRestartEndpointAlignedMacroTraceLedger initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) index).1.2 ≠ 0 := by
  dsimp only
  simpa only [wholeRestartEndpointAlignedMacro_writtenComponent] using
    wholeRestartEndpointSelectedOccurrence_zero_or_nativeNext_or_trace
      elapsedBounded index

/-! ## Physical projection of the identical macro event -/

/-- The common endpoint frame contains the existing physical macro current,
the aligned pending stream and its exact trace ledger. -/
def wholeRestartEndpointAlignedMacroFrame
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (phase : WholeRestartEndpointComponentMacroPhase) :
    GeneratedWholeRestartCurrent ν ×
      (WholeRestartEndpointAlignedResponsibilityTail ×
        WholeRestartEndpointAlignedResponsibilityTail) :=
  (wholeRestartEndpointComponentMacroPhysicalCurrent
      initial elapsedBounded phase,
    wholeRestartEndpointAlignedMacroPending
      initial elapsedBounded phase,
    wholeRestartEndpointAlignedMacroTraceLedger
      initial elapsedBounded phase)

/-- One source-owned equation writes the existing absolute unforced next
current and the full aligned responsibility stream. -/
theorem wholeRestartEndpointAlignedMacroFrame_update
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointAlignedMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
          initial elapsedBounded,
        0,
        wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0) := by
  rfl

/-- Its physical projection is exactly the pre-existing source-generated
whole unforced endpoint successor. -/
theorem wholeRestartEndpointAlignedMacroFrame_physical_update
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (wholeRestartEndpointAlignedMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
      sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded := by
  rfl

/-- The receipt of the physical projection starts at its own actual unforced
initial state; no responsibility coordinate is injected as forcing. -/
theorem wholeRestartEndpointAlignedMacroFrame_receipt_initial
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let next :=
      (wholeRestartEndpointAlignedMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1
    next.receipt.wholePath
        ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
      next.initialState := by
  exact
    wholeRestartEndpointComponentMacroPhysicalCurrent_receipt_initial
      elapsedBounded

/-! ## Positive defect survives in the native endpoint trace -/

/-- Pointwise identification of the kinetic coordinate written by the macro
trace with the already aligned actual residual. -/
theorem wholeRestartEndpointAlignedMacro_kineticTrace_apply
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (linearResidualTrace wholeRestartEndpointAlignedMacroKeep
        (wholeRestartEndpointAlignedMacroPending
          initial elapsedBounded accumulationRead) index).2 =
      wholeRestartEndpointAlignedKineticResidual
        initial elapsedBounded index := by
  rw [wholeRestartEndpointAlignedMacro_trace_eq_stream]
  simp [wholeRestartEndpointAlignedResponsibilityTail,
    wholeRestartEndpointAlignedResponsibility]

/-- The kinetic coordinate of the actual macro trace has exact limiting
square mass equal to the internally generated endpoint defect. -/
theorem wholeRestartEndpointAlignedMacro_kineticTrace_norm_sq_tendsto_defect
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let endpointReceipt :=
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).family.endpointReceipt
    Tendsto
      (fun index =>
        ‖(linearResidualTrace wholeRestartEndpointAlignedMacroKeep
            (wholeRestartEndpointAlignedMacroPending
              initial elapsedBounded accumulationRead) index).2‖ ^ 2)
      atTop
      (nhds
        (wholeRestartKineticWeakEndpointDefect initial
          endpointReceipt.kineticReceipt.endpoint)) := by
  dsimp only
  simpa only [wholeRestartEndpointAlignedMacro_kineticTrace_apply] using
    wholeRestartEndpointAlignedKineticResidual_norm_sq_tendsto_defect
      elapsedBounded

/-- Every fixed finite Fourier observation of that same macro-trace
coordinate tends to zero.  Positive defect therefore remains a concrete
whole-carrier kernel escape after the endpoint write, not a detached scalar. -/
theorem
    wholeRestartEndpointAlignedMacro_kineticTrace_finiteProjection_tendsto_zero
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (modes : Finset NonzeroIntegerWavevector) :
    Tendsto
      (fun index =>
        wholeRestartKineticFiniteProjection modes
          ((linearResidualTrace wholeRestartEndpointAlignedMacroKeep
            (wholeRestartEndpointAlignedMacroPending
              initial elapsedBounded accumulationRead) index).2))
      atTop (nhds 0) := by
  simpa only [wholeRestartEndpointAlignedMacro_kineticTrace_apply] using
    wholeRestartEndpointAlignedKineticResidual_finiteProjection_tendsto_zero
      elapsedBounded modes

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
end NavierStokes
end SaturationMonoid

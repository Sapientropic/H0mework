import H0mework.NavierStokes.Fourier.GeneratedUnforcedScaleTimeReceipt
import H0mework.NavierStokes.ShellSources.InfiniteLineageHilbertCompletion

/-!
# Deferred target ledger for the unforced validation process

`GeneratedUnforcedScaleTimeReceipt` is a target-validation process: every
validation event generates an actual positive-time unforced Galerkin receipt,
and a successful old source shell row is read as a derivative observation of
that same event.  The integer-shell grammar remains the authoritative source
producer; this module does not introduce another source scheduler.

It equips the validation process with the whole residual carrier

```text
symbolic = physical + shell-ledger
debt     = shell-ledger
recollection(symbolic,debt) = symbolic - debt = physical.
```

The debt is therefore not a certificate and is never settled by a primitive
jump.  It is the target ledger already written by the validation event.  A
shell event adds its generated row to both symbolic memory and debt,
while the recollected update is exactly the actual physical endpoint trace.
A quiet event writes no debt and still advances by an actual physical trace.

The old grammar is not reconstructed here: its already generated receipt is
carried by the same `UnforcedObservation` and does not choose a second
physical update.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt

noncomputable section

/-! ## Whole live/debt carrier of the target validation -/

/-- The actual physical coefficient carrier of the current PDE state. -/
def materializedCarrier
    (current : UnforcedScaleTimeCurrent) :
    IntegerShellCoefficientCarrier :=
  generatedCoefficientCarrier current.physicalSource

/-- The source-owned deferred debt is exactly the existing shell ledger. -/
def materializationDebt
    (current : UnforcedScaleTimeCurrent) :
    IntegerShellCoefficientCarrier :=
  current.shellTraceLedger

/--
Symbolic memory consists of the actual physical carrier plus the generated
shell ledger.  It is a readout, not a second raw source.
-/
def symbolicCarrier
    (current : UnforcedScaleTimeCurrent) :
    IntegerShellCoefficientCarrier :=
  materializedCarrier current + materializationDebt current

/-- The two-coordinate carrier retaining symbolic memory and debt. -/
def deferredWholeCarrier
    (current : UnforcedScaleTimeCurrent) :
    IntegerShellCoefficientCarrier × IntegerShellCoefficientCarrier :=
  (symbolicCarrier current, materializationDebt current)

/-- Recollect physical responsibility by subtracting debt from symbolic memory. -/
def deferredRecollection :
    (IntegerShellCoefficientCarrier × IntegerShellCoefficientCarrier) →+
      IntegerShellCoefficientCarrier where
  toFun state := state.1 - state.2
  map_zero' := by simp
  map_add' left right := by
    simp
    abel

@[simp] theorem deferredRecollection_apply
    (state :
      IntegerShellCoefficientCarrier × IntegerShellCoefficientCarrier) :
    deferredRecollection state = state.1 - state.2 :=
  rfl

/-- Debt is the uniquely forced complement of physical inside symbolic. -/
theorem materializationDebt_eq_symbolic_sub_materialized
    (current : UnforcedScaleTimeCurrent) :
    materializationDebt current =
      symbolicCarrier current - materializedCarrier current := by
  unfold symbolicCarrier
  abel

/-- Whole-carrier recollection is exactly the actual physical carrier. -/
theorem deferredRecollection_wholeCarrier
    (current : UnforcedScaleTimeCurrent) :
    deferredRecollection (deferredWholeCarrier current) =
      materializedCarrier current := by
  simp [deferredWholeCarrier, symbolicCarrier]

@[simp] theorem materializationDebt_ofSource
    (source : RawVorticityFourierSource) :
    materializationDebt (UnforcedScaleTimeCurrent.ofSource source) = 0 :=
  rfl

/-- Hilbert-space state compiled from the recollected whole carrier. -/
def recollectedPhysicalState
    (current : UnforcedScaleTimeCurrent) :
    ComplexVorticityHilbertState :=
  coefficientCarrierComplexState
    (deferredRecollection (deferredWholeCarrier current))

/-- Recollection returns the actual raw physical source on the whole state. -/
theorem recollectedPhysicalState_eq_generatedPhysicalSource
    (current : UnforcedScaleTimeCurrent) :
    recollectedPhysicalState current =
      generatedComplexVorticityState current.physicalSource
        (generatedSupport current.physicalSource) := by
  rw [recollectedPhysicalState,
    deferredRecollection_wholeCarrier,
    materializedCarrier,
    coefficientCarrierComplexState_generatedCoefficientCarrier]

/-! ## The old grammar as a same-event observation projection -/

/-- Current-state readout into the old scale--time carrier. -/
def legacyCurrentReadout
    (current : UnforcedScaleTimeCurrent) :
    ScaleTimeCurrent where
  source := current.physicalSource
  elapsed := current.elapsed

/--
Forget the physical receipt while retaining its same-event legacy readout.
The quiet receipt already has exactly the old time-observation type.
-/
def legacyObservationReadout
    {ν : Viscosity} :
    UnforcedObservation ν →
      ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse.Observation ν
  | .shell legacyReceipt _ =>
      .shell legacyReceipt
  | .quiet source physicalReceipt =>
      .time source physicalReceipt

/--
Successful actual event: the old shell receipt is literally the observation
projection of the same reflexive read/write occurrence.
-/
theorem legacyObservationReadout_run_of_some
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource)
    (generated :
      generatedIntegerShellRespond current.physicalSource =
        some response) :
    legacyObservationReadout
        (ReflexiveQuery.run
          (unforcedScaleTimeReflexiveQuery ν) current).1 =
      .shell
        (receiptOfResponse
          current.physicalSource response generated) := by
  rw [unforcedScaleTimeReflexiveQuery_run_of_some
    ν current response generated]
  rfl

/--
Quiet actual event: the old time receipt is literally the observation
projection of the same reflexive occurrence.
-/
theorem legacyObservationReadout_run_of_none
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (stopped :
      generatedIntegerShellRespond current.physicalSource = none) :
    legacyObservationReadout
        (ReflexiveQuery.run
          (unforcedScaleTimeReflexiveQuery ν) current).1 =
      .time current.physicalSource
        (generatedTimeAdvanceReceipt
          current.physicalSource ν.coeff) := by
  rw [unforcedScaleTimeReflexiveQuery_run_of_none
    ν current stopped]
  rfl

/-! ## Exact one-event live/debt transport -/

namespace DeferredStep

/-- Target-ledger trace written by one validation event. -/
def materializationTrace
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : UnforcedNativeStep ν current next) :
    IntegerShellCoefficientCarrier :=
  match step with
  | .shell response _ =>
      generatedIntegerShellTrace
        current.physicalSource response.2.shellSq
  | .quiet _ => 0

/-- Actual physical coefficient trace written by the receipt endpoint. -/
def physicalCarrierTrace
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (_step : UnforcedNativeStep ν current next) :
    IntegerShellCoefficientCarrier :=
  materializedCarrier next - materializedCarrier current

/-- Every actual edge writes its generated trace to debt, with no silent loss. -/
theorem materializationDebt_next
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : UnforcedNativeStep ν current next) :
    materializationDebt next =
      materializationDebt current + materializationTrace step := by
  cases step with
  | shell response generated =>
      rfl
  | quiet stopped =>
      simp [materializationDebt, materializationTrace]

/--
The complete live/debt edge difference is the actual physical trace plus the
ledger trace in symbolic memory, together with that same ledger trace in debt.
-/
theorem wholeCarrier_sub
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : UnforcedNativeStep ν current next) :
    deferredWholeCarrier next - deferredWholeCarrier current =
      (physicalCarrierTrace step + materializationTrace step,
        materializationTrace step) := by
  apply Prod.ext
  · change
      symbolicCarrier next - symbolicCarrier current =
        physicalCarrierTrace step + materializationTrace step
    rw [symbolicCarrier, symbolicCarrier,
      materializationDebt_next step]
    unfold physicalCarrierTrace
    abel
  · change
      materializationDebt next - materializationDebt current =
        materializationTrace step
    rw [materializationDebt_next step]
    abel

/--
Whole-carrier commuting square: recollection kills only the internal shell
memory transfer and preserves exactly the actual physical endpoint trace.
-/
theorem recollection_wholeCarrier_sub
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : UnforcedNativeStep ν current next) :
    deferredRecollection
        (deferredWholeCarrier next - deferredWholeCarrier current) =
      physicalCarrierTrace step := by
  rw [wholeCarrier_sub step]
  simp [deferredRecollection]

/-- A successful shell event has a nonzero source-generated debt trace. -/
theorem shell_materializationTrace_ne_zero
    {ν : Viscosity}
    {current : UnforcedScaleTimeCurrent}
    (response :
      Response GeneratedIntegerShellStep current.physicalSource)
    (generated :
      generatedIntegerShellRespond current.physicalSource =
        some response) :
    materializationTrace
        (UnforcedNativeStep.shell
          (ν := ν) response generated) ≠
      0 := by
  simpa [materializationTrace,
    generatedIntegerShellReceiptTrace, receiptOfResponse,
    GeneratedIntegerShellReceipt.selectedShellSq] using
    coefficientTrace_ne_zero
      (receiptOfResponse
        current.physicalSource response generated)

@[simp] theorem quiet_materializationTrace
    {ν : Viscosity}
    {current : UnforcedScaleTimeCurrent}
    (stopped :
      generatedIntegerShellRespond current.physicalSource = none) :
    materializationTrace
        (UnforcedNativeStep.quiet
          (ν := ν) stopped) = 0 :=
  rfl

end DeferredStep

/-! ## Branchwise actual-PDE endpoint laws on the recollected carrier -/

/--
In the shell-observation branch, the recollected next state is the endpoint
of the target-side expanded-support unforced receipt.
-/
theorem recollectedPhysicalState_unforcedShellTarget
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    recollectedPhysicalState
        (unforcedShellTarget ν current response) =
      (shellPhysicalTimeReceipt
        current.physicalSource response ν).endpoint := by
  rw [recollectedPhysicalState_eq_generatedPhysicalSource]
  exact unforcedShellTarget_physicalState ν current response

/--
In the quiet branch, the recollected next state is still an actual unforced
receipt endpoint.
-/
theorem recollectedPhysicalState_unforcedQuietTarget
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    recollectedPhysicalState (unforcedQuietTarget ν current) =
      (generatedTimeAdvanceReceipt
        current.physicalSource ν.coeff).endpoint := by
  rw [recollectedPhysicalState_eq_generatedPhysicalSource]
  exact unforcedQuietTarget_physicalState ν current

/--
The shell receipt begins at the old recollected physical state, so the ledger
write introduces no impulse.
-/
theorem shellPhysicalTimeReceipt_initial_eq_recollectedPhysicalState
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.physicalSource) :
    (shellPhysicalTimeReceipt
        current.physicalSource response ν).trajectory 0 =
      recollectedPhysicalState current := by
  rw [shellPhysicalTimeReceipt_initial_eq_currentPhysicalState,
    recollectedPhysicalState_eq_generatedPhysicalSource]

end

end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
end NavierStokes
end SaturationMonoid

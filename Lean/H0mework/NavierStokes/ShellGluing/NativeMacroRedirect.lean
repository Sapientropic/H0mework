import H0mework.NavierStokes.Completion.AdjacentRoundTimeSectionGluing
import H0mework.NavierStokes.ScaleControl.TimeDeferredMaterialization

/-!
# Native macro redirect of the generated shell gluing residual

The old complete-round producer remains authoritative for the maximal
integer-shell path and its exact cumulative trace.  Its legacy macro target
writes that trace literally into the physical source before starting the
positive-time receipt.  Consequently adjacent legacy time sections have the
concrete gluing residual computed in
`GeneratedCompleteAdjacentRoundTimeSectionGluing`.

This module gives that already generated residual a versioned native macro
target on the existing whole residual carrier:

```text
old complete-round response
  read:  exact maximal shell path and cumulative q
  write: q to the symbolic/ledger coordinates
       + actual complete-support unforced endpoint to physicalSource.
```

Thus the old `q` producer is unchanged, while recollection removes only the
internal `(q,q)` transfer.  The physical projection starts at the previous
physical state and ends at the endpoint of one actual unforced Galerkin
receipt.  No branch, path, target, nonzero witness, trajectory, or coverage
certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open ThreeDimensionalVorticityCoefficientGeneratedCompleteScaleTimeRoundRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteAdjacentRoundTimeSectionGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt

noncomputable section

/-! ## Exact lift of the old complete-round response -/

/--
The physical receipt of every redirected macro starts at the old physical
state on its canonical conservative complete support.
-/
def redirectedMacroPhysicalReceipt
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    GeneratedTimeAdvanceReceipt
      (completeOmittedPhysicalLiftSource current.physicalSource)
      ν.coeff :=
  completeOmittedPhysicalTimeReceipt current.physicalSource ν

/--
Versioned target of one old complete-round response.  The old round controls
only the generated ledger trace.  The physical target is controlled solely
by the actual unforced receipt from the old physical state.
-/
def redirectedCompleteRoundTarget
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (oldResponse :
      Response (CompleteRoundStep ν) (legacyCurrentReadout current)) :
    UnforcedScaleTimeCurrent where
  physicalSource :=
    (redirectedMacroPhysicalReceipt ν current).nextSource
  shellTraceLedger :=
    current.shellTraceLedger +
      generatedIntegerShellCumulativeTrace
        oldResponse.2.round.shellRun.arrival
  elapsed :=
    current.elapsed +
      (redirectedMacroPhysicalReceipt ν current).duration

/--
One native redirected macro edge retains the exact old response and its
source-generation equation.  It changes no old producer declaration.
-/
inductive NativeRedirectedCompleteRoundStep
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    UnforcedScaleTimeCurrent → Type
  | advance
      (oldResponse :
        Response (CompleteRoundStep ν) (legacyCurrentReadout current))
      (generated :
        generatedCompleteRoundRespond
            ν (legacyCurrentReadout current) =
          some oldResponse) :
      NativeRedirectedCompleteRoundStep ν current
        (redirectedCompleteRoundTarget ν current oldResponse)

namespace NativeRedirectedCompleteRoundStep

/-- The literal old complete-round response retained by the native edge. -/
def oldResponse
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    Response (CompleteRoundStep ν) (legacyCurrentReadout current) :=
  match step with
  | .advance response _ => response

/-- The exact old maximal round retained by the native edge. -/
def round
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    GeneratedFiniteRound ν (legacyCurrentReadout current) :=
  step.oldResponse.2.round

/-- Complete source-generated coefficient trace redirected by this edge. -/
def shellTrace
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    IntegerShellCoefficientCarrier :=
  generatedIntegerShellCumulativeTrace step.round.shellRun.arrival

/-- Actual physical coefficient trace of the same native edge. -/
def physicalTrace
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (_step : NativeRedirectedCompleteRoundStep ν current next) :
    IntegerShellCoefficientCarrier :=
  materializedCarrier next - materializedCarrier current

/-- Exact provenance equation of the retained old response. -/
theorem oldResponse_generated
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    generatedCompleteRoundRespond
        ν (legacyCurrentReadout current) =
      some step.oldResponse := by
  cases step with
  | advance response generated =>
      exact generated

/-- The target ledger appends exactly the old round's cumulative trace. -/
theorem shellTraceLedger_next
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    next.shellTraceLedger =
      current.shellTraceLedger + step.shellTrace := by
  cases step
  rfl

/-- Difference form of the native no-silent ledger write. -/
theorem shellTraceLedger_sub
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    next.shellTraceLedger - current.shellTraceLedger =
      step.shellTrace := by
  rw [step.shellTraceLedger_next]
  abel

/-- Elapsed time advances by exactly the actual unforced receipt duration. -/
theorem elapsed_next
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    next.elapsed =
      current.elapsed +
        (redirectedMacroPhysicalReceipt ν current).duration := by
  cases step
  rfl

/-- The physical target is exactly the actual unforced receipt endpoint source. -/
theorem physicalSource_next
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    next.physicalSource =
      (redirectedMacroPhysicalReceipt ν current).nextSource := by
  cases step
  rfl

/--
Exact whole-carrier update.  The old shell residual is written once into
symbolic memory and once into its complementary ledger coordinate.
-/
theorem wholeCarrier_sub
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    deferredWholeCarrier next - deferredWholeCarrier current =
      (step.physicalTrace + step.shellTrace, step.shellTrace) := by
  apply Prod.ext
  · change
      symbolicCarrier next - symbolicCarrier current =
        step.physicalTrace + step.shellTrace
    rw [symbolicCarrier, symbolicCarrier,
      materializationDebt, materializationDebt,
      step.shellTraceLedger_next]
    unfold physicalTrace materializedCarrier
    abel
  · change
      materializationDebt next - materializationDebt current =
        step.shellTrace
    rw [materializationDebt, materializationDebt,
      step.shellTraceLedger_next]
    abel

/--
The whole-carrier square commutes: recollection cancels the internal shell
redirect and preserves exactly the actual physical endpoint trace.
-/
theorem recollection_wholeCarrier_sub
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    deferredRecollection
        (deferredWholeCarrier next - deferredWholeCarrier current) =
      step.physicalTrace := by
  rw [step.wholeCarrier_sub]
  simp [deferredRecollection]

/--
The physical projection of the redirected macro is one genuine unforced
Galerkin receipt from the old physical state.  The old shell trace never
appears as an impulse in this projection.
-/
theorem physicalProjection_unforced_commutes
    {ν : Viscosity}
    {current next : UnforcedScaleTimeCurrent}
    (step : NativeRedirectedCompleteRoundStep ν current next) :
    let receipt := redirectedMacroPhysicalReceipt ν current
    receipt.trajectory 0 = recollectedPhysicalState current ∧
      (∀ time ∈ Set.Icc (0 : ℝ) receipt.duration,
        HasDerivAt receipt.trajectory
          (finiteStateVorticityGenerator
            (generatedSupport
              (completeOmittedPhysicalLiftSource
                current.physicalSource))
            ν.coeff
            (receipt.trajectory time))
          time) ∧
      recollectedPhysicalState next = receipt.endpoint := by
  cases step with
  | advance oldResponse generated =>
      let receipt :=
        redirectedMacroPhysicalReceipt ν current
      have initial :
          receipt.trajectory 0 =
            recollectedPhysicalState current := by
        calc
          receipt.trajectory 0 =
              generatedCompleteNonlinearInitialState
                current.physicalSource := by
            exact
              completeOmittedPhysicalTimeReceipt_initial
                current.physicalSource ν
          _ =
              generatedComplexVorticityState
                current.physicalSource
                (generatedSupport current.physicalSource) := by
            exact
              generatedCompleteNonlinearInitialState_eq_currentPhysicalState
                current.physicalSource
          _ = recollectedPhysicalState current := by
            exact
              (recollectedPhysicalState_eq_generatedPhysicalSource
                current).symm
      have endpoint :
          recollectedPhysicalState
              (redirectedCompleteRoundTarget
                ν current oldResponse) =
            receipt.endpoint := by
        rw [recollectedPhysicalState_eq_generatedPhysicalSource]
        exact receipt.nextSource_generatedState
      exact
        ⟨initial,
          fun time timeMem => (receipt.physical time timeMem).1,
          endpoint⟩

end NativeRedirectedCompleteRoundStep

/-! ## Source-owned partial responder and conservativity -/

/--
Lift the exact old complete-round responder.  `none` is retained literally
and therefore still denotes a genuine old infinite shell lineage.
-/
noncomputable def generatedRedirectedCompleteRoundRespond
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    Option
      (Response (NativeRedirectedCompleteRoundStep ν) current) :=
  match generated :
      generatedCompleteRoundRespond
        ν (legacyCurrentReadout current) with
  | some oldResponse =>
      some
        ⟨redirectedCompleteRoundTarget ν current oldResponse,
          NativeRedirectedCompleteRoundStep.advance
            oldResponse generated⟩
  | none => none

theorem generatedRedirectedCompleteRoundRespond_of_some
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (oldResponse :
      Response (CompleteRoundStep ν) (legacyCurrentReadout current))
    (generated :
      generatedCompleteRoundRespond
          ν (legacyCurrentReadout current) =
        some oldResponse) :
    generatedRedirectedCompleteRoundRespond ν current =
      some
        ⟨redirectedCompleteRoundTarget ν current oldResponse,
          NativeRedirectedCompleteRoundStep.advance
            oldResponse generated⟩ := by
  unfold generatedRedirectedCompleteRoundRespond
  split
  · rename_i oldResponse' generated'
    have responseEq : oldResponse' = oldResponse :=
      Option.some.inj (generated'.symm.trans generated)
    subst oldResponse'
    have generatedEq : generated' = generated :=
      Subsingleton.elim _ _
    cases generatedEq
    rfl
  · rename_i stopped
    cases stopped.symm.trans generated

theorem generatedRedirectedCompleteRoundRespond_of_none
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (stopped :
      generatedCompleteRoundRespond
          ν (legacyCurrentReadout current) =
        none) :
    generatedRedirectedCompleteRoundRespond ν current = none := by
  unfold generatedRedirectedCompleteRoundRespond
  split
  · rename_i _oldResponse generated
    cases generated.symm.trans stopped
  · rfl

/-- Forgetting the versioned target recovers the literal old responder. -/
theorem generatedRedirectedCompleteRoundRespond_old_conservative
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent) :
    Option.map
        (fun response => response.2.oldResponse)
        (generatedRedirectedCompleteRoundRespond ν current) =
      generatedCompleteRoundRespond
        ν (legacyCurrentReadout current) := by
  unfold generatedRedirectedCompleteRoundRespond
  split
  · rename_i oldResponse generated
    change
      some oldResponse =
        generatedCompleteRoundRespond
          ν (legacyCurrentReadout current)
    exact generated.symm
  · rename_i stopped
    change
      none =
        generatedCompleteRoundRespond
          ν (legacyCurrentReadout current)
    exact stopped.symm

/-! ## The legacy adjacent gluing defect is the native redirected trace -/

/-- Embed an old scale-time current with empty internal shell memory. -/
def redirectCurrentOfScaleTime
    (current : ScaleTimeCurrent) :
    UnforcedScaleTimeCurrent where
  physicalSource := current.source
  shellTraceLedger := 0
  elapsed := current.elapsed

@[simp] theorem legacyCurrentReadout_redirectCurrentOfScaleTime
    (current : ScaleTimeCurrent) :
    legacyCurrentReadout (redirectCurrentOfScaleTime current) =
      current := by
  cases current
  rfl

/--
The concrete non-compatible seam of two adjacent legacy time sections is
not discarded.  The exact next old response is lifted to a native macro
update, and the image of its ledger difference is precisely that seam.

The theorem generates the response; its mouth contains no response, branch,
path, target, nonzero, or compatibility premise.
-/
theorem adjacentTimeSectionGluingResidual_redirects_to_nativeMacroUpdate
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    ∃ response :
        Response (NativeRedirectedCompleteRoundStep ν)
          (redirectCurrentOfScaleTime
            (lineage.current (index + 1))),
      generatedRedirectedCompleteRoundRespond
          ν
          (redirectCurrentOfScaleTime
            (lineage.current (index + 1))) =
        some response ∧
      coefficientCarrierComplexState
          (response.1.shellTraceLedger -
            (redirectCurrentOfScaleTime
              (lineage.current (index + 1))).shellTraceLedger) =
        (lineage.timeReceipt (index + 1)).trajectory 0 -
          (lineage.timeReceipt index).trajectory
            (lineage.timeReceipt index).duration ∧
      (let receipt :=
          redirectedMacroPhysicalReceipt
            ν
            (redirectCurrentOfScaleTime
              (lineage.current (index + 1)));
        receipt.trajectory 0 =
            recollectedPhysicalState
              (redirectCurrentOfScaleTime
                (lineage.current (index + 1))) ∧
          recollectedPhysicalState response.1 =
            receipt.endpoint) := by
  let current :=
    redirectCurrentOfScaleTime
      (lineage.current (index + 1))
  let oldResponse :
      Response (CompleteRoundStep ν)
        (legacyCurrentReadout current) :=
    ⟨lineage.current ((index + 1) + 1),
      lineage.step (index + 1)⟩
  have oldGenerated :
      generatedCompleteRoundRespond
          ν (legacyCurrentReadout current) =
        some oldResponse := by
    simpa [current, oldResponse, legacyCurrentReadout,
      redirectCurrentOfScaleTime] using
      lineage.generated (index + 1)
  let response :
      Response (NativeRedirectedCompleteRoundStep ν) current :=
    ⟨redirectedCompleteRoundTarget ν current oldResponse,
      NativeRedirectedCompleteRoundStep.advance
        oldResponse oldGenerated⟩
  refine ⟨response, ?_, ?_, ?_⟩
  · exact
      generatedRedirectedCompleteRoundRespond_of_some
        ν current oldResponse oldGenerated
  · have ledgerWrite :
        response.1.shellTraceLedger -
            current.shellTraceLedger =
          generatedIntegerShellCumulativeTrace
            (lineage.round (index + 1)).shellRun.arrival := by
      change
        (current.shellTraceLedger +
              generatedIntegerShellCumulativeTrace
                (lineage.round (index + 1)).shellRun.arrival) -
            current.shellTraceLedger =
          generatedIntegerShellCumulativeTrace
            (lineage.round (index + 1)).shellRun.arrival
      abel
    rw [ledgerWrite]
    change
      generatedIntegerShellPathStateTrace
          (lineage.round (index + 1)).shellRun.arrival =
        _
    exact
      (adjacentTimeSectionGluingResidual_eq_nextShellTrace
        lineage index).symm
  · have physical :=
      NativeRedirectedCompleteRoundStep.physicalProjection_unforced_commutes
        response.2
    exact ⟨physical.1, physical.2.2⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect
end NavierStokes
end SaturationMonoid

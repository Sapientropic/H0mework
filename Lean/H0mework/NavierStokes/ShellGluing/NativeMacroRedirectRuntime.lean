import H0mework.NavierStokes.ShellGluing.NativeMacroRedirect

/-!
# Recursive runtime of native shell-residual macro redirects

The one-edge redirect is itself a source-owned responder, so it can be
iterated without a caller-selected horizon.  Starting from one literal
whole-residual current, the runtime generates exactly one of:

* a finite redirected macro path ending where the old shell producer has a
  genuine infinite lineage; or
* an infinite lineage of redirected macro updates.

On the infinite branch every adjacent physical receipt glues exactly: the
next receipt starts at the preceding receipt endpoint.  Meanwhile every old
complete-round shell trace remains in the whole residual carrier and
telescopes over arbitrary finite prefixes.  Thus recursive source generation
and unforced physical projection coexist on the same actual lineage.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime

open scoped BigOperators

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger
open ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open ThreeDimensionalVorticityCoefficientGeneratedCompleteScaleTimeRoundRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization
open
  ThreeDimensionalVorticityCoefficientGeneratedUnforcedScaleTimeReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirect

noncomputable section

/-! ## Maximal runtime disposition -/

/-- A finite redirected path ending at a genuine old infinite shell lineage. -/
structure GeneratedRedirectedCompleteRoundTerminalRun
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent) : Type where
  terminal : UnforcedScaleTimeCurrent
  arrival :
    NativeReachable seed
      (generatedRedirectedCompleteRoundRespond ν) terminal
  stopped :
    generatedRedirectedCompleteRoundRespond ν terminal = none

/-- Stopping the redirected responder retains the literal old stop. -/
theorem oldResponder_stopped_of_redirected_stopped
    (ν : Viscosity)
    (current : UnforcedScaleTimeCurrent)
    (stopped :
      generatedRedirectedCompleteRoundRespond ν current = none) :
    generatedCompleteRoundRespond
        ν
        (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
          current) =
      none := by
  have conservative :=
    generatedRedirectedCompleteRoundRespond_old_conservative
      ν current
  rw [stopped] at conservative
  simpa using conservative.symm

/-- The exact old infinite shell lineage exposed by a stopped redirected run. -/
noncomputable def
    GeneratedRedirectedCompleteRoundTerminalRun.infiniteShell
    {ν : Viscosity}
    {seed : UnforcedScaleTimeCurrent}
    (run : GeneratedRedirectedCompleteRoundTerminalRun ν seed) :
    GeneratedCompleteInfiniteShellAt
      (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
        run.terminal) :=
  generatedCompleteRoundRespond_infiniteShell
    ν
    (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
      run.terminal)
    (oldResponder_stopped_of_redirected_stopped
      ν run.terminal run.stopped)

private theorem exists_forcedRedirectedResponse
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : UnforcedScaleTimeCurrent,
        NativeReachable seed
          (generatedRedirectedCompleteRoundRespond ν) current) :
    ∃ response :
        Response (NativeRedirectedCompleteRoundStep ν) node.1,
      generatedRedirectedCompleteRoundRespond ν node.1 =
        some response := by
  cases generated :
      generatedRedirectedCompleteRoundRespond ν node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedRedirectedResponse
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : UnforcedScaleTimeCurrent,
        NativeReachable seed
          (generatedRedirectedCompleteRoundRespond ν) current) :
    Response (NativeRedirectedCompleteRoundStep ν) node.1 :=
  Classical.choose
    (exists_forcedRedirectedResponse
      ν seed noTerminal node)

private theorem forcedRedirectedResponse_generated
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : UnforcedScaleTimeCurrent,
        NativeReachable seed
          (generatedRedirectedCompleteRoundRespond ν) current) :
    generatedRedirectedCompleteRoundRespond ν node.1 =
      some
        (forcedRedirectedResponse
          ν seed noTerminal node) :=
  Classical.choose_spec
    (exists_forcedRedirectedResponse
      ν seed noTerminal node)

private noncomputable def infiniteRedirectedReachableRun
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed)) :
    ℕ →
      Σ current : UnforcedScaleTimeCurrent,
        NativeReachable seed
          (generatedRedirectedCompleteRoundRespond ν) current
  | 0 =>
      ⟨seed, NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteRedirectedReachableRun
          ν seed noTerminal index
      let response :=
        forcedRedirectedResponse
          ν seed noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedRedirectedResponse_generated
            ν seed noTerminal node)⟩

/-- Infinite source-owned lineage of native shell-residual macro redirects. -/
structure GeneratedRedirectedCompleteRoundInfiniteLineage
    (ν : Viscosity) : Type where
  current : ℕ → UnforcedScaleTimeCurrent
  step :
    ∀ index : ℕ,
      NativeRedirectedCompleteRoundStep ν
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedRedirectedCompleteRoundRespond ν (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def
    infiniteRedirectedLineageOfNoTerminal
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed)) :
    GeneratedRedirectedCompleteRoundInfiniteLineage ν where
  current index :=
    (infiniteRedirectedReachableRun
      ν seed noTerminal index).1
  step index :=
    (forcedRedirectedResponse
      ν seed noTerminal
      (infiniteRedirectedReachableRun
        ν seed noTerminal index)).2
  generated index :=
    forcedRedirectedResponse_generated
      ν seed noTerminal
      (infiniteRedirectedReachableRun
        ν seed noTerminal index)

@[simp] theorem
    infiniteRedirectedLineageOfNoTerminal_current_zero
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed)) :
    (infiniteRedirectedLineageOfNoTerminal
      ν seed noTerminal).current 0 =
      seed :=
  rfl

/--
The literal seed generates either a finite redirect prefix followed by a
genuine infinite old shell lineage, or an infinite native macro lineage.
-/
inductive GeneratedRedirectedCompleteRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent) : Type
  | shellInfinite
      (run : GeneratedRedirectedCompleteRoundTerminalRun ν seed)
      (infiniteShell :
        GeneratedCompleteInfiniteShellAt
          (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
            run.terminal))
  | macroInfinite
      (lineage :
        GeneratedRedirectedCompleteRoundInfiniteLineage ν)
      (startsAtSeed : lineage.current 0 = seed)

noncomputable def generatedRedirectedCompleteRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : UnforcedScaleTimeCurrent) :
    GeneratedRedirectedCompleteRoundRuntimeDisposition ν seed := by
  by_cases terminalExists :
      Nonempty
        (GeneratedRedirectedCompleteRoundTerminalRun ν seed)
  · let run := Classical.choice terminalExists
    exact .shellInfinite run run.infiniteShell
  · exact
      .macroInfinite
        (infiniteRedirectedLineageOfNoTerminal
          ν seed terminalExists)
        (infiniteRedirectedLineageOfNoTerminal_current_zero
          ν seed terminalExists)

/-! ## Exact laws of the infinite native macro lineage -/

namespace GeneratedRedirectedCompleteRoundInfiniteLineage

def round
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedFiniteRound ν
      (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
        (lineage.current index)) :=
  (lineage.step index).round

def physicalReceipt
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedTimeAdvanceReceipt
      (completeOmittedPhysicalLiftSource
        (lineage.current index).physicalSource)
      ν.coeff :=
  redirectedMacroPhysicalReceipt ν (lineage.current index)

/-- Every recursive edge retains the exact old complete-round response. -/
theorem oldResponse_generated
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    generatedCompleteRoundRespond
        ν
        (ThreeDimensionalVorticityCoefficientGeneratedScaleTimeDeferredMaterialization.legacyCurrentReadout
          (lineage.current index)) =
      some (lineage.step index).oldResponse :=
  (lineage.step index).oldResponse_generated

/-- The complete old shell trace is natively written at every macro edge. -/
theorem shellTraceLedger_succ
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (lineage.current (index + 1)).shellTraceLedger =
      (lineage.current index).shellTraceLedger +
        (lineage.step index).shellTrace :=
  (lineage.step index).shellTraceLedger_next

/-- One-edge whole residual transport on the recursive actual lineage. -/
theorem wholeCarrier_succ_sub
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    deferredWholeCarrier (lineage.current (index + 1)) -
        deferredWholeCarrier (lineage.current index) =
      ((lineage.step index).physicalTrace +
          (lineage.step index).shellTrace,
        (lineage.step index).shellTrace) :=
  (lineage.step index).wholeCarrier_sub

/--
Adjacent physical sections now glue exactly.  The shell residual is retained
in the whole carrier rather than inserted as an impulse between them.
-/
theorem adjacentPhysicalReceipts_glue
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    (lineage.physicalReceipt (index + 1)).trajectory 0 =
      (lineage.physicalReceipt index).trajectory
        (lineage.physicalReceipt index).duration := by
  have nextPhysical :=
    (lineage.step (index + 1)).physicalProjection_unforced_commutes
  have previousPhysical :=
    (lineage.step index).physicalProjection_unforced_commutes
  calc
    (lineage.physicalReceipt (index + 1)).trajectory 0 =
        recollectedPhysicalState
          (lineage.current (index + 1)) :=
      nextPhysical.1
    _ = (lineage.physicalReceipt index).endpoint :=
      previousPhysical.2.2
    _ =
        (lineage.physicalReceipt index).trajectory
          (lineage.physicalReceipt index).duration :=
      rfl

/-! ## Internally generated zero/positive shell responsibility -/

private theorem cumulativeTrace_eq_zero_of_occurrence_eq_zero
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (occurrenceZero : arrival.occurrence = 0) :
    generatedIntegerShellCumulativeTrace arrival = 0 := by
  cases arrival with
  | initial =>
      rfl
  | @step prior arrival response generated =>
      simp [NativeReachable.occurrence] at occurrenceZero

private theorem cumulativeTrace_ne_zero_of_occurrence_pos
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (occurrencePos : 0 < arrival.occurrence) :
    generatedIntegerShellCumulativeTrace arrival ≠ 0 := by
  intro traceZero
  have write :=
    generatedIntegerShellReachable_endpointState_sub_seed_eq_trace
      arrival
  rw [generatedIntegerShellPathStateTrace, traceZero] at write
  simp at write
  exact
    (generatedIntegerShellReachable_endpointState_ne_seed
      arrival occurrencePos)
      (sub_eq_zero.mp write)

/--
Each actual macro edge internally decides whether its old shell round is
silent or carries a genuinely nonzero complete-carrier trace.
-/
inductive GeneratedShellRedirectActivity
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) : Type
  | quiet
      (shellLengthZero : (lineage.round index).shellLength = 0)
      (traceZero : (lineage.step index).shellTrace = 0)
  | active
      (shellLengthPos : 0 < (lineage.round index).shellLength)
      (traceNonzero : (lineage.step index).shellTrace ≠ 0)

/--
No caller chooses activity or supplies nonvanishing.  Both are generated
from the exact old path retained by the native macro edge.
-/
noncomputable def shellRedirectActivity
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (index : ℕ) :
    GeneratedShellRedirectActivity lineage index := by
  by_cases shellLengthZero :
      (lineage.round index).shellLength = 0
  · exact
      .quiet shellLengthZero <| by
        unfold NativeRedirectedCompleteRoundStep.shellTrace
        apply cumulativeTrace_eq_zero_of_occurrence_eq_zero
        exact shellLengthZero
  · have shellLengthPos :
        0 < (lineage.round index).shellLength :=
      Nat.pos_of_ne_zero shellLengthZero
    exact
      .active shellLengthPos <| by
        unfold NativeRedirectedCompleteRoundStep.shellTrace
        apply cumulativeTrace_ne_zero_of_occurrence_pos
        exact shellLengthPos

/-- Vector sum of physical coefficient traces over one generated prefix. -/
def physicalTraceSum
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    IntegerShellCoefficientCarrier :=
  ∑ index ∈ Finset.range length,
    (lineage.step index).physicalTrace

/-- Vector sum of retained old shell traces over one generated prefix. -/
def shellTraceSum
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    IntegerShellCoefficientCarrier :=
  ∑ index ∈ Finset.range length,
    (lineage.step index).shellTrace

/--
Exact arbitrary-prefix whole-carrier transport.  No generated shell
responsibility is quotiented before it is written.
-/
theorem prefixWholeCarrier_sub
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν) :
    ∀ length : ℕ,
      deferredWholeCarrier (lineage.current length) -
          deferredWholeCarrier (lineage.current 0) =
        (lineage.physicalTraceSum length +
            lineage.shellTraceSum length,
          lineage.shellTraceSum length)
  | 0 => by
      apply Prod.ext <;>
        simp [physicalTraceSum, shellTraceSum]
  | length + 1 => by
      rw [show
        deferredWholeCarrier (lineage.current (length + 1)) -
            deferredWholeCarrier (lineage.current 0) =
          (deferredWholeCarrier (lineage.current (length + 1)) -
              deferredWholeCarrier (lineage.current length)) +
            (deferredWholeCarrier (lineage.current length) -
              deferredWholeCarrier (lineage.current 0)) by
            abel,
        lineage.wholeCarrier_succ_sub length,
        lineage.prefixWholeCarrier_sub length]
      simp [physicalTraceSum, shellTraceSum,
        Finset.sum_range_succ]
      constructor <;> abel

/--
After any generated prefix, physical recollection keeps only the accumulated
actual unforced endpoint traces.
-/
theorem prefixRecollection_wholeCarrier_sub
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (length : ℕ) :
    deferredRecollection
        (deferredWholeCarrier (lineage.current length) -
          deferredWholeCarrier (lineage.current 0)) =
      lineage.physicalTraceSum length := by
  rw [lineage.prefixWholeCarrier_sub length]
  simp [deferredRecollection]

end GeneratedRedirectedCompleteRoundInfiniteLineage

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
end NavierStokes
end SaturationMonoid

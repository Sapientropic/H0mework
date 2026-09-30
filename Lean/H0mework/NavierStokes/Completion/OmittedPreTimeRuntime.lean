import H0mework.NavierStokes.Completion.OmittedWholeCarrierCompiler

/-!
# Maximal source runtime before the next physical-time event

The versioned complete-support responder has three native events:

```text
shell | support | time.
```

This module follows the two zero-time structural events maximally.  From one
literal current the source generates exactly one of:

* a finite proof-relevant path of shell/support writes whose terminal next
  event is the actual positive-time write;
* an infinite proof-relevant shell/support lineage.

Support installation cannot repeat immediately, but later shell writes can
generate new nonlinear support demands.  The maximal runtime therefore
follows the actual responder rather than assuming a fixed number of support
rounds.  No horizon, path, branch, terminal, target, nonzero fact, or
termination certificate is accepted at the producer mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeRuntime

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedNativeSuccessor
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Structural native response -/

/-- One zero-physical-time native write before the next time event. -/
inductive PreTimeStep
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent → Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.source)
      (generated :
        generatedIntegerShellRespond current.source =
          some response) :
      PreTimeStep ν current (shellTarget current response)
  | support
      (outerStopped :
        generatedIntegerShellRespond current.source = none)
      (missingNonempty :
        (generatedMissingNonlinearModes current.source).Nonempty) :
      PreTimeStep ν current (completeSupportTarget current)

namespace PreTimeStep

/-- Embed a structural step in the authoritative complete scale/time graph. -/
def fullStep
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : PreTimeStep ν current next) :
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse.NativeStep
      ν current next :=
  match step with
  | .shell response generated =>
      .shell response generated
  | .support outerStopped missingNonempty =>
      .support outerStopped missingNonempty

/-- Structural writes consume no physical elapsed time. -/
theorem target_elapsed
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : PreTimeStep ν current next) :
    next.elapsed = current.elapsed := by
  cases step <;> rfl

end PreTimeStep

/--
Optional structural response.  `none` means exactly that the authoritative
complete responder's next event is physical time.
-/
noncomputable def generatedPreTimeRespond
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    Option (Response (PreTimeStep ν) current) :=
  match outer :
      generatedIntegerShellRespond current.source with
  | some response =>
      some
        ⟨shellTarget current response,
          PreTimeStep.shell response outer⟩
  | none =>
      if missingNonempty :
          (generatedMissingNonlinearModes current.source).Nonempty
      then
        some
          ⟨completeSupportTarget current,
            PreTimeStep.support outer missingNonempty⟩
      else
        none

theorem generatedPreTimeRespond_of_some
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source)
    (generated :
      generatedIntegerShellRespond current.source =
        some response) :
    generatedPreTimeRespond ν current =
      some
        ⟨shellTarget current response,
          PreTimeStep.shell response generated⟩ := by
  unfold generatedPreTimeRespond
  split
  · rename_i response' generated'
    have responseEq : response' = response :=
      Option.some.inj (generated'.symm.trans generated)
    subst response'
    have generatedEq : generated' = generated :=
      Subsingleton.elim _ _
    cases generatedEq
    rfl
  · rename_i stopped
    cases stopped.symm.trans generated

theorem generatedPreTimeRespond_of_none_missing
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingNonempty :
      (generatedMissingNonlinearModes current.source).Nonempty) :
    generatedPreTimeRespond ν current =
      some
        ⟨completeSupportTarget current,
          PreTimeStep.support outerStopped missingNonempty⟩ := by
  unfold generatedPreTimeRespond
  split
  · rename_i _response generated
    cases generated.symm.trans outerStopped
  · rename_i generated
    have generatedEq : generated = outerStopped :=
      Subsingleton.elim _ _
    cases generatedEq
    simp only [dif_pos missingNonempty]

theorem generatedPreTimeRespond_of_none_closed
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingEmpty :
      generatedMissingNonlinearModes current.source = ∅) :
    generatedPreTimeRespond ν current = none := by
  unfold generatedPreTimeRespond
  split
  · rename_i _response generated
    cases generated.symm.trans outerStopped
  · rename_i generated
    have generatedEq : generated = outerStopped :=
      Subsingleton.elim _ _
    cases generatedEq
    have notNonempty :
        ¬(generatedMissingNonlinearModes current.source).Nonempty := by
      rw [missingEmpty]
      exact Finset.not_nonempty_empty
    simp only [dif_neg notNonempty]

theorem generatedPreTimeRespond_eq_none_iff
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    generatedPreTimeRespond ν current = none ↔
      generatedIntegerShellRespond current.source = none ∧
        generatedMissingNonlinearModes current.source = ∅ := by
  rcases
      Option.eq_none_or_eq_some
        (generatedIntegerShellRespond current.source) with
    outerStopped | ⟨response, generated⟩
  · by_cases missingNonempty :
        (generatedMissingNonlinearModes current.source).Nonempty
    · rw [generatedPreTimeRespond_of_none_missing
        ν current outerStopped missingNonempty]
      have missingNe :
          generatedMissingNonlinearModes current.source ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp missingNonempty
      simp [outerStopped, missingNe]
    · have missingEmpty :
          generatedMissingNonlinearModes current.source = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp missingNonempty
      rw [generatedPreTimeRespond_of_none_closed
        ν current outerStopped missingEmpty]
      simp [outerStopped, missingEmpty]
  · rw [generatedPreTimeRespond_of_some
      ν current response generated]
    simp [generated]

/--
Every successful structural response is literally the same edge and target
as the authoritative complete responder.
-/
theorem generatedPreTimeRespond_some_fullResponse
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response : Response (PreTimeStep ν) current)
    (generated :
      generatedPreTimeRespond ν current = some response) :
    generatedCompleteScaleTimeRespond ν current =
      ⟨response.1, response.2.fullStep⟩ := by
  unfold generatedPreTimeRespond at generated
  split at generated
  · rename_i shellResponse outer
    simp only [Option.some.injEq] at generated
    cases generated
    exact
      generatedCompleteScaleTimeRespond_of_some
        ν current shellResponse outer
  · rename_i outer
    split at generated
    · rename_i missingNonempty
      simp only [Option.some.injEq] at generated
      cases generated
      exact
        generatedCompleteScaleTimeRespond_of_none_missing
          ν current outer missingNonempty
    · simp at generated

/-- A stopped structural response exposes the exact generated time event. -/
theorem generatedPreTimeRespond_none_fullTimeResponse
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (stopped : generatedPreTimeRespond ν current = none) :
    generatedCompleteScaleTimeRespond ν current =
      ⟨timeTarget ν current,
        ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse.NativeStep.time
          ((generatedPreTimeRespond_eq_none_iff
            ν current).mp stopped).1
          ((generatedPreTimeRespond_eq_none_iff
            ν current).mp stopped).2⟩ := by
  exact
    generatedCompleteScaleTimeRespond_of_none_closed
      ν current
      ((generatedPreTimeRespond_eq_none_iff
        ν current).mp stopped).1
      ((generatedPreTimeRespond_eq_none_iff
        ν current).mp stopped).2

/--
Executing an actual support edge closes the structural responder.  The next
authoritative event is time; no second support or newly manufactured shell
edge can intervene.
-/
theorem generatedPreTimeRespond_completeSupportTarget_eq_none
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none) :
    generatedPreTimeRespond
        ν (completeSupportTarget current) =
      none := by
  exact
    generatedPreTimeRespond_of_none_closed
      ν (completeSupportTarget current)
      (generatedIntegerShellRespond_completeLift_eq_none_of_none
        current.source outerStopped)
      (completeSupportTarget_missingNonlinearModes current)

/-- Exact least structural reachability. -/
abbrev GeneratedPreTimeReachable
    (ν : Viscosity)
    (seed current : ScaleTimeCurrent) :=
  NativeReachable seed (generatedPreTimeRespond ν) current

/-! ## Finite terminal or infinite structural lineage -/

/-- A finite maximal structural run ending immediately before physical time. -/
structure GeneratedPreTimeTerminalRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type where
  terminal : ScaleTimeCurrent
  arrival : GeneratedPreTimeReachable ν seed terminal
  stopped : generatedPreTimeRespond ν terminal = none

namespace GeneratedPreTimeTerminalRun

theorem outerStopped
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedPreTimeTerminalRun ν seed) :
    generatedIntegerShellRespond run.terminal.source = none :=
  ((generatedPreTimeRespond_eq_none_iff
    ν run.terminal).mp run.stopped).1

theorem missingClosed
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedPreTimeTerminalRun ν seed) :
    generatedMissingNonlinearModes run.terminal.source = ∅ :=
  ((generatedPreTimeRespond_eq_none_iff
    ν run.terminal).mp run.stopped).2

/-- The exact authoritative next event at a finite terminal is physical time. -/
theorem fullTimeResponse
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedPreTimeTerminalRun ν seed) :
    generatedCompleteScaleTimeRespond ν run.terminal =
      ⟨timeTarget ν run.terminal,
        ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse.NativeStep.time
          run.outerStopped run.missingClosed⟩ :=
  generatedCompleteScaleTimeRespond_of_none_closed
    ν run.terminal run.outerStopped run.missingClosed

end GeneratedPreTimeTerminalRun

/-- Infinite literal lineage of zero-time structural writes. -/
structure GeneratedPreTimeInfiniteLineage
    (ν : Viscosity) : Type where
  current : ℕ → ScaleTimeCurrent
  step :
    ∀ index : ℕ,
      PreTimeStep ν (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedPreTimeRespond ν (current index) =
        some ⟨current (index + 1), step index⟩

namespace GeneratedPreTimeInfiniteLineage

/-- Elapsed physical time is constant along an infinite structural lineage. -/
theorem elapsed_succ
    {ν : Viscosity}
    (lineage : GeneratedPreTimeInfiniteLineage ν)
    (index : ℕ) :
    (lineage.current (index + 1)).elapsed =
      (lineage.current index).elapsed :=
  (lineage.step index).target_elapsed

theorem elapsed_eq_initial
    {ν : Viscosity}
    (lineage : GeneratedPreTimeInfiniteLineage ν)
    (index : ℕ) :
    (lineage.current index).elapsed =
      (lineage.current 0).elapsed := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [lineage.elapsed_succ index, inductionHypothesis]

end GeneratedPreTimeInfiniteLineage

/-! ## Maximal source-generated runtime -/

private theorem exists_forcedPreTimeResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        GeneratedPreTimeReachable ν seed current) :
    ∃ response : Response (PreTimeStep ν) node.1,
      generatedPreTimeRespond ν node.1 = some response := by
  cases generated :
      generatedPreTimeRespond ν node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedPreTimeResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        GeneratedPreTimeReachable ν seed current) :
    Response (PreTimeStep ν) node.1 :=
  Classical.choose
    (exists_forcedPreTimeResponse
      ν seed noTerminal node)

private theorem forcedPreTimeResponse_generated
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        GeneratedPreTimeReachable ν seed current) :
    generatedPreTimeRespond ν node.1 =
      some
        (forcedPreTimeResponse
          ν seed noTerminal node) :=
  Classical.choose_spec
    (exists_forcedPreTimeResponse
      ν seed noTerminal node)

private noncomputable def infinitePreTimeReachableRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed)) :
    ℕ →
      Σ current : ScaleTimeCurrent,
        GeneratedPreTimeReachable ν seed current
  | 0 =>
      ⟨seed, NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infinitePreTimeReachableRun
          ν seed noTerminal index
      let response :=
        forcedPreTimeResponse
          ν seed noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedPreTimeResponse_generated
            ν seed noTerminal node)⟩

private noncomputable def infinitePreTimeLineageOfNoTerminal
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed)) :
    GeneratedPreTimeInfiniteLineage ν where
  current index :=
    (infinitePreTimeReachableRun
      ν seed noTerminal index).1
  step index :=
    (forcedPreTimeResponse
      ν seed noTerminal
      (infinitePreTimeReachableRun
        ν seed noTerminal index)).2
  generated index :=
    forcedPreTimeResponse_generated
      ν seed noTerminal
      (infinitePreTimeReachableRun
        ν seed noTerminal index)

@[simp] theorem infinitePreTimeLineageOfNoTerminal_current_zero
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedPreTimeTerminalRun ν seed)) :
    (infinitePreTimeLineageOfNoTerminal
      ν seed noTerminal).current 0 =
      seed :=
  rfl

/-- Exhaustive source-generated pre-time runtime. -/
inductive GeneratedPreTimeRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type
  | terminal
      (run : GeneratedPreTimeTerminalRun ν seed)
  | infinite
      (lineage : GeneratedPreTimeInfiniteLineage ν)
      (startsAtSeed : lineage.current 0 = seed)

/--
Follow the actual shell/support responder maximally.  The case split is
internal; the theorem mouth contains only viscosity and the literal seed.
-/
noncomputable def generatedPreTimeRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) :
    GeneratedPreTimeRuntimeDisposition ν seed := by
  by_cases terminalExists :
      Nonempty (GeneratedPreTimeTerminalRun ν seed)
  · exact .terminal (Classical.choice terminalExists)
  · exact
      .infinite
        (infinitePreTimeLineageOfNoTerminal
          ν seed terminalExists)
        (infinitePreTimeLineageOfNoTerminal_current_zero
          ν seed terminalExists)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedPreTimeRuntime
end NavierStokes
end SaturationMonoid

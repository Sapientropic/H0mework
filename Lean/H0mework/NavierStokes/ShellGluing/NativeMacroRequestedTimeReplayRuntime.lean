import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplaySource

/-!
# Maximal source-owned runtime on an arbitrary requested interval

The requested-time residual responder is iterated without a caller-selected
horizon, target support, branch, or path.  It either reaches an actual stage
whose whole residual vanishes on the full requested interval, or generates
an infinite lineage of strict support refinements.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource

noncomputable section

/-- A finite source-generated requested-time run stopped by residual closure. -/
structure GeneratedRequestedTimeReplayTerminalRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) where
  terminal :
    GeneratedRequestedTimeReplayStage lineage requestedTime
  arrival :
    NativeReachable
      (initialRequestedTimeReplayStage
        lineage initialSubcritical requestedTime requestedTimePos)
      (generatedRequestedTimeReplayRespond
        lineage initialSubcritical requestedTime requestedTimePos)
      terminal
  stopped :
    generatedRequestedTimeReplayRespond
        lineage initialSubcritical requestedTime requestedTimePos
        terminal =
      none

/--
The finite terminal receipt carries the exact whole requested-time
punctured residual equation.
-/
theorem GeneratedRequestedTimeReplayTerminalRun.puncturedResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayTerminalRun
        lineage initialSubcritical requestedTime requestedTimePos) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      ∀ wave : IntegerWavevector,
        wave ≠ 0 →
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
            run.terminal time wave = 0 :=
  (generatedRequestedTimeReplayRespond_eq_none_iff_puncturedResidual_zero
    lineage initialSubcritical requestedTime requestedTimePos
    run.terminal).mp run.stopped

private theorem exists_forcedRequestedTimeReplayResponse
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayStage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)
          (generatedRequestedTimeReplayRespond
            lineage initialSubcritical requestedTime requestedTimePos)
          current) :
    ∃ response :
        Response
          (NativeRequestedTimeReplayStep
            lineage initialSubcritical requestedTime requestedTimePos)
          node.1,
      generatedRequestedTimeReplayRespond
          lineage initialSubcritical requestedTime requestedTimePos
          node.1 =
        some response := by
  cases generated :
      generatedRequestedTimeReplayRespond
        lineage initialSubcritical requestedTime requestedTimePos
        node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedRequestedTimeReplayResponse
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayStage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)
          (generatedRequestedTimeReplayRespond
            lineage initialSubcritical requestedTime requestedTimePos)
          current) :
    Response
      (NativeRequestedTimeReplayStep
        lineage initialSubcritical requestedTime requestedTimePos)
      node.1 :=
  Classical.choose <|
    exists_forcedRequestedTimeReplayResponse
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal node

private theorem forcedRequestedTimeReplayResponse_generated
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayStage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)
          (generatedRequestedTimeReplayRespond
            lineage initialSubcritical requestedTime requestedTimePos)
          current) :
    generatedRequestedTimeReplayRespond
        lineage initialSubcritical requestedTime requestedTimePos
        node.1 =
      some
        (forcedRequestedTimeReplayResponse
          lineage initialSubcritical requestedTime requestedTimePos
          noTerminal node) :=
  Classical.choose_spec <|
    exists_forcedRequestedTimeReplayResponse
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal node

private noncomputable def infiniteRequestedTimeReplayReachableRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)) :
    ℕ →
      Σ current :
          GeneratedRequestedTimeReplayStage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)
          (generatedRequestedTimeReplayRespond
            lineage initialSubcritical requestedTime requestedTimePos)
          current
  | 0 =>
      ⟨initialRequestedTimeReplayStage
          lineage initialSubcritical requestedTime requestedTimePos,
        NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteRequestedTimeReplayReachableRun
          lineage initialSubcritical requestedTime requestedTimePos
          noTerminal index
      let response :=
        forcedRequestedTimeReplayResponse
          lineage initialSubcritical requestedTime requestedTimePos
          noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedRequestedTimeReplayResponse_generated
            lineage initialSubcritical requestedTime requestedTimePos
            noTerminal node)⟩

/--
A genuine infinite requested-time replay.  Every successor retains the exact
source-generated native residual edge.
-/
structure GeneratedRequestedTimeReplayInfiniteLineage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) where
  current :
    ℕ → GeneratedRequestedTimeReplayStage lineage requestedTime
  step :
    ∀ index : ℕ,
      NativeRequestedTimeReplayStep
        lineage initialSubcritical requestedTime requestedTimePos
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedRequestedTimeReplayRespond
          lineage initialSubcritical requestedTime requestedTimePos
          (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def
    infiniteRequestedTimeReplayLineageOfNoTerminal
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)) :
    GeneratedRequestedTimeReplayInfiniteLineage
      lineage initialSubcritical requestedTime requestedTimePos where
  current index :=
    (infiniteRequestedTimeReplayReachableRun
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal index).1
  step index :=
    (forcedRequestedTimeReplayResponse
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal
      (infiniteRequestedTimeReplayReachableRun
        lineage initialSubcritical requestedTime requestedTimePos
        noTerminal index)).2
  generated index :=
    forcedRequestedTimeReplayResponse_generated
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal
      (infiniteRequestedTimeReplayReachableRun
        lineage initialSubcritical requestedTime requestedTimePos
        noTerminal index)

@[simp] theorem
    infiniteRequestedTimeReplayLineageOfNoTerminal_current_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)) :
    (infiniteRequestedTimeReplayLineageOfNoTerminal
      lineage initialSubcritical requestedTime requestedTimePos
      noTerminal).current 0 =
        initialRequestedTimeReplayStage
          lineage initialSubcritical requestedTime requestedTimePos :=
  rfl

namespace GeneratedRequestedTimeReplayInfiniteLineage

/-- Infinite requested-time replay supports grow strictly at every write. -/
theorem modes_strictMono
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) :
    StrictMono (fun index => (replay.current index).modes) := by
  apply strictMono_nat_of_lt_succ
  intro index
  exact (replay.step index).modes_ssubset

/--
Every infinite stage carries a source-generated nonempty raw residual
inventory; signed closure is not substituted for this provenance.
-/
theorem rawMissing_nonempty
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos)
    (index : ℕ) :
    (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
      (replay.current index)).Nonempty := by
  by_contra missingNonempty
  have stopped :
      generatedRequestedTimeReplayRespond
          lineage initialSubcritical requestedTime requestedTimePos
          (replay.current index) =
        none := by
    simp [generatedRequestedTimeReplayRespond,
      missingNonempty]
  rw [replay.generated index] at stopped
  contradiction

end GeneratedRequestedTimeReplayInfiniteLineage

/--
Exhaustive requested-time outcome generated by the maximal source runtime.
-/
inductive GeneratedRequestedTimeReplayDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) : Type
  | terminal
      (run :
        GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)
  | infinite
      (replay :
        GeneratedRequestedTimeReplayInfiniteLineage
          lineage initialSubcritical requestedTime requestedTimePos)
      (startsAtInitial :
        replay.current 0 =
          initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)

/--
Generate the maximal terminal-or-infinite requested-time disposition.  No
branch, path, horizon, target support, nonzero witness, or coverage premise
is supplied by the caller.
-/
noncomputable def generatedRequestedTimeReplayDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayDisposition
      lineage initialSubcritical requestedTime requestedTimePos := by
  by_cases terminalExists :
      Nonempty
        (GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)
  · exact .terminal (Classical.choice terminalExists)
  · exact
      .infinite
        (infiniteRequestedTimeReplayLineageOfNoTerminal
          lineage initialSubcritical requestedTime requestedTimePos
          terminalExists)
        (infiniteRequestedTimeReplayLineageOfNoTerminal_current_zero
          lineage initialSubcritical requestedTime requestedTimePos
          terminalExists)

/--
Unconditional public outcome.  The source itself first decides whether the
initial actual lineage has crossed the half-critical threshold; only the
subcritical branch enters the indexed requested-time runtime.
-/
inductive GeneratedRequestedTimeReplayMaximalDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) : Type
  | halfCritical
      (crossing : lineageHalfCriticalCrossing lineage 0)
  | terminal
      (initialSubcritical :
        ¬ lineageHalfCriticalCrossing lineage 0)
      (run :
        GeneratedRequestedTimeReplayTerminalRun
          lineage initialSubcritical requestedTime requestedTimePos)
  | infinite
      (initialSubcritical :
        ¬ lineageHalfCriticalCrossing lineage 0)
      (replay :
        GeneratedRequestedTimeReplayInfiniteLineage
          lineage initialSubcritical requestedTime requestedTimePos)
      (startsAtInitial :
        replay.current 0 =
          initialRequestedTimeReplayStage
            lineage initialSubcritical requestedTime requestedTimePos)

/--
Generate the unconditional maximal requested-time disposition.  Its mouth
contains only the actual source lineage and the requested positive interval.
-/
noncomputable def generatedRequestedTimeReplayMaximalDisposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayMaximalDisposition
      lineage requestedTime requestedTimePos := by
  by_cases crossing :
      lineageHalfCriticalCrossing lineage 0
  · exact .halfCritical crossing
  · cases
      generatedRequestedTimeReplayDisposition
        lineage crossing requestedTime requestedTimePos with
    | terminal run =>
        exact .terminal crossing run
    | infinite replay startsAtInitial =>
        exact .infinite crossing replay startsAtInitial

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
end NavierStokes
end SaturationMonoid

import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2Source

/-!
# Unconditional maximal requested-time replay runtime

The V2 responder is iterated without an initial critical-smallness branch.
For the actual source lineage and positive requested interval, the runtime
either reaches a stage whose punctured full-time residual vanishes or
generates an infinite lineage of strict source-owned support refinements.

No trajectory, branch, horizon, target support, residual witness, or
coverage certificate occurs in the public producer mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source

noncomputable section

/-- A finite V2 run stopped by full-time residual closure. -/
structure GeneratedRequestedTimeReplayV2TerminalRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) where
  terminal :
    GeneratedRequestedTimeReplayV2Stage lineage requestedTime
  arrival :
    NativeReachable
      (initialRequestedTimeReplayV2Stage
        lineage requestedTime requestedTimePos)
      (generatedRequestedTimeReplayV2Respond
        lineage requestedTime requestedTimePos)
      terminal
  stopped :
    generatedRequestedTimeReplayV2Respond
        lineage requestedTime requestedTimePos terminal =
      none

/-- A finite V2 terminal run carries exact punctured residual closure. -/
theorem GeneratedRequestedTimeReplayV2TerminalRun.puncturedResidual_zero
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (run :
      GeneratedRequestedTimeReplayV2TerminalRun
        lineage requestedTime requestedTimePos) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      ∀ wave : IntegerWavevector,
        wave ≠ 0 →
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
            run.terminal time wave = 0 := by
  exact
    (generatedRequestedTimeReplayV2Respond_eq_none_iff_puncturedResidual_zero
      lineage requestedTime requestedTimePos run.terminal).mp run.stopped

private theorem exists_forcedRequestedTimeReplayV2Response
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayV2Stage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayV2Stage
            lineage requestedTime requestedTimePos)
          (generatedRequestedTimeReplayV2Respond
            lineage requestedTime requestedTimePos)
          current) :
    ∃ response :
        Response
          (NativeRequestedTimeReplayV2Step
            lineage requestedTime requestedTimePos)
          node.1,
      generatedRequestedTimeReplayV2Respond
          lineage requestedTime requestedTimePos node.1 =
        some response := by
  cases generated :
      generatedRequestedTimeReplayV2Respond
        lineage requestedTime requestedTimePos node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedRequestedTimeReplayV2Response
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayV2Stage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayV2Stage
            lineage requestedTime requestedTimePos)
          (generatedRequestedTimeReplayV2Respond
            lineage requestedTime requestedTimePos)
          current) :
    Response
      (NativeRequestedTimeReplayV2Step
        lineage requestedTime requestedTimePos)
      node.1 :=
  Classical.choose <|
    exists_forcedRequestedTimeReplayV2Response
      lineage requestedTime requestedTimePos noTerminal node

private theorem forcedRequestedTimeReplayV2Response_generated
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos))
    (node :
      Σ current :
          GeneratedRequestedTimeReplayV2Stage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayV2Stage
            lineage requestedTime requestedTimePos)
          (generatedRequestedTimeReplayV2Respond
            lineage requestedTime requestedTimePos)
          current) :
    generatedRequestedTimeReplayV2Respond
        lineage requestedTime requestedTimePos node.1 =
      some
        (forcedRequestedTimeReplayV2Response
          lineage requestedTime requestedTimePos noTerminal node) :=
  Classical.choose_spec <|
    exists_forcedRequestedTimeReplayV2Response
      lineage requestedTime requestedTimePos noTerminal node

private noncomputable def infiniteRequestedTimeReplayV2ReachableRun
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos)) :
    ℕ →
      Σ current :
          GeneratedRequestedTimeReplayV2Stage lineage requestedTime,
        NativeReachable
          (initialRequestedTimeReplayV2Stage
            lineage requestedTime requestedTimePos)
          (generatedRequestedTimeReplayV2Respond
            lineage requestedTime requestedTimePos)
          current
  | 0 =>
      ⟨initialRequestedTimeReplayV2Stage
          lineage requestedTime requestedTimePos,
        NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteRequestedTimeReplayV2ReachableRun
          lineage requestedTime requestedTimePos noTerminal index
      let response :=
        forcedRequestedTimeReplayV2Response
          lineage requestedTime requestedTimePos noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedRequestedTimeReplayV2Response_generated
            lineage requestedTime requestedTimePos noTerminal node)⟩

/--
A genuine infinite V2 replay.  Every successor retains its exact native
full-time residual refinement edge.
-/
structure GeneratedRequestedTimeReplayV2InfiniteLineage
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) where
  current :
    ℕ → GeneratedRequestedTimeReplayV2Stage lineage requestedTime
  step :
    ∀ index : ℕ,
      NativeRequestedTimeReplayV2Step
        lineage requestedTime requestedTimePos
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedRequestedTimeReplayV2Respond
          lineage requestedTime requestedTimePos
          (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def
    infiniteRequestedTimeReplayV2LineageOfNoTerminal
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos)) :
    GeneratedRequestedTimeReplayV2InfiniteLineage
      lineage requestedTime requestedTimePos where
  current index :=
    (infiniteRequestedTimeReplayV2ReachableRun
      lineage requestedTime requestedTimePos noTerminal index).1
  step index :=
    (forcedRequestedTimeReplayV2Response
      lineage requestedTime requestedTimePos noTerminal
      (infiniteRequestedTimeReplayV2ReachableRun
        lineage requestedTime requestedTimePos noTerminal index)).2
  generated index :=
    forcedRequestedTimeReplayV2Response_generated
      lineage requestedTime requestedTimePos noTerminal
      (infiniteRequestedTimeReplayV2ReachableRun
        lineage requestedTime requestedTimePos noTerminal index)

@[simp] theorem
    infiniteRequestedTimeReplayV2LineageOfNoTerminal_current_zero
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (noTerminal :
      ¬ Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos)) :
    (infiniteRequestedTimeReplayV2LineageOfNoTerminal
      lineage requestedTime requestedTimePos noTerminal).current 0 =
        initialRequestedTimeReplayV2Stage
          lineage requestedTime requestedTimePos :=
  rfl

namespace GeneratedRequestedTimeReplayV2InfiniteLineage

/-- Infinite V2 supports grow strictly at every native write. -/
theorem modes_strictMono
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage
        lineage requestedTime requestedTimePos) :
    StrictMono (fun index => (replay.current index).modes) := by
  apply strictMono_nat_of_lt_succ
  intro index
  exact (replay.step index).modes_ssubset

/--
Every infinite V2 stage carries a source-generated nonempty raw residual
inventory.
-/
theorem rawMissing_nonempty
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage
        lineage requestedTime requestedTimePos)
    (index : ℕ) :
    (GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
      (replay.current index)).Nonempty := by
  by_contra missingNonempty
  have stopped :
      generatedRequestedTimeReplayV2Respond
          lineage requestedTime requestedTimePos
          (replay.current index) =
        none := by
    simp [generatedRequestedTimeReplayV2Respond,
      missingNonempty]
  rw [replay.generated index] at stopped
  contradiction

/--
At every actual infinite-replay occurrence, the source generates a concrete
old residual row and time where that row is nonzero.  The same native edge
installs the row in the next law surface, where its residual is identically
zero on the whole requested interval; the next trajectory simultaneously
retains the actual unforced Galerkin law and the physical invariants.

Neither the active row, its activation time, the next support, nor the
physical trajectory is supplied by the caller.
-/
theorem generatedResidual_nativeWrite_and_unforcedProjection
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage
        lineage requestedTime requestedTimePos)
    (index : ℕ) :
    ∃ wave : IntegerWavevector,
      wave ≠ 0 ∧
        wave ∈
          GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
            (replay.current index) ∧
        (∃ activationTime ∈ Icc (0 : ℝ) requestedTime,
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
              (replay.current index) activationTime wave ≠
            0) ∧
        (∀ time ∈ Icc (0 : ℝ) requestedTime,
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
              (replay.current (index + 1)) time wave =
            0) ∧
        ∀ time ∈ Icc (0 : ℝ) requestedTime,
          HasDerivAt
              (replay.current (index + 1)).trajectory
              (finiteStateVorticityGenerator
                (replay.current (index + 1)).modes
                ν.coeff
                ((replay.current (index + 1)).trajectory time))
              time ∧
            (∀ output,
              output ∉ (replay.current (index + 1)).modes →
                (replay.current (index + 1)).trajectory time output =
                  0) ∧
            (∀ output,
              complexWavevector output ⬝ᵥ
                  (replay.current (index + 1)).trajectory time output =
                0) ∧
            FiniteStateFourierReality
              ((replay.current (index + 1)).trajectory time) := by
  obtain ⟨wave, waveMem⟩ :=
    replay.rawMissing_nonempty index
  have waveData :=
    (GeneratedRequestedTimeReplayStage.mem_rawWholeSpaceTimeMissingModes_iff
      (replay.current index) wave).mp waveMem
  rcases waveData with
    ⟨_pairOutputMem, waveNe, _waveNotMem,
      activationTime, activationTimeMem, residualNonzero⟩
  refine
    ⟨wave, waveNe, waveMem,
      ⟨activationTime, activationTimeMem, residualNonzero⟩,
      ?_, (replay.current (index + 1)).physical⟩
  intro time timeMem
  exact
    (replay.step index).rawMissing_next_residual_zero
      waveMem timeMem

end GeneratedRequestedTimeReplayV2InfiniteLineage

/-- Exhaustive outcome generated by the unconditional V2 runtime. -/
inductive GeneratedRequestedTimeReplayV2Disposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) : Type
  | terminal
      (run :
        GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos)
  | infinite
      (replay :
        GeneratedRequestedTimeReplayV2InfiniteLineage
          lineage requestedTime requestedTimePos)
      (startsAtInitial :
        replay.current 0 =
          initialRequestedTimeReplayV2Stage
            lineage requestedTime requestedTimePos)

/--
Generate the unconditional terminal-or-infinite V2 disposition.  Its public
mouth contains only the actual lineage and the positive requested interval.
-/
noncomputable def generatedRequestedTimeReplayV2Disposition
    {ν : Viscosity}
    (lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedRequestedTimeReplayV2Disposition
      lineage requestedTime requestedTimePos := by
  by_cases terminalExists :
      Nonempty
        (GeneratedRequestedTimeReplayV2TerminalRun
          lineage requestedTime requestedTimePos)
  · exact .terminal (Classical.choice terminalExists)
  · exact
      .infinite
        (infiniteRequestedTimeReplayV2LineageOfNoTerminal
          lineage requestedTime requestedTimePos terminalExists)
        (infiniteRequestedTimeReplayV2LineageOfNoTerminal_current_zero
          lineage requestedTime requestedTimePos terminalExists)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
end NavierStokes
end SaturationMonoid

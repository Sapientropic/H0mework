import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalStrongCompactness
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWeakClosure

/-!
# Whole weak equation from the source-owned local V2 replay

The residual-driven V2 support lineage now has a strong whole-carrier
subsequence on the source-generated local horizon.  This module consumes
that same subsequence.  Every nonzero Fourier row is either eventually
written into the actual finite law surface or is proved residual-silent at
every stage; hence the strong limit satisfies the unforced whole weak law.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWeakClosure

open scoped ENNReal Topology

open Set
open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalStrongCompactness

noncomputable section

@[simp] theorem localReplayV2SpaceTimePath_eq_wholeTrajectory
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (index : ℕ) :
    localReplayV2SpaceTimePath replay index =
      wholeTrajectorySpaceTimePath
        (sourceOwnedLocalReplayV2Duration lineage)
        (replay.current index).trajectory
        (HasDerivAt.continuousOn fun time timeMem =>
          ((replay.current index).physical time timeMem).1) := by
  rfl

theorem localReplayV2Wave_eventually_mem_comp_strictMono
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (subsequence : ℕ → ℕ)
    (subsequenceMono : StrictMono subsequence)
    (wave : IntegerWavevector)
    (waveGenerated :
      ∃ entry : ℕ, wave ∈ (replay.current entry).modes) :
    ∀ᶠ index : ℕ in atTop,
      wave ∈ (replay.current (subsequence index)).modes := by
  rcases waveGenerated with ⟨entry, waveMem⟩
  have eventuallyInReplay :
      ∀ᶠ index : ℕ in atTop,
        wave ∈ (replay.current index).modes := by
    apply Filter.eventually_atTop.2
    refine ⟨entry, ?_⟩
    intro index entryLe
    exact (replay.modes_strictMono.monotone entryLe) waveMem
  exact subsequenceMono.tendsto_atTop.eventually eventuallyInReplay

/-- A row that never enters the source-generated law surface cannot carry
a hidden whole-PDE residual at any replay stage. -/
theorem localReplayV2Residual_eq_zero_of_never_generated
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (neverGenerated :
      ¬ ∃ entry : ℕ, wave ∈ (replay.current entry).modes)
    (index : ℕ)
    (time : ℝ)
    (timeMem :
      time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
        (replay.current index) time wave = 0 := by
  by_contra residualNonzero
  have waveNotMem : wave ∉ (replay.current index).modes := by
    intro waveMem
    exact neverGenerated ⟨index, waveMem⟩
  have pairMem :
      wave ∈ finiteVorticityPairOutputSupport
        (replay.current index).modes := by
    by_contra pairNotMem
    exact residualNonzero
      (GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual_eq_zero_of_not_mem_pairOutput
        (replay.current index) timeMem pairNotMem)
  have rawMissing :
      wave ∈
        GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
          (replay.current index) :=
    (GeneratedRequestedTimeReplayStage.mem_rawWholeSpaceTimeMissingModes_iff
      (replay.current index) wave).mpr
      ⟨pairMem, waveNonzero, waveNotMem,
        ⟨time, timeMem, residualNonzero⟩⟩
  have nextMem : wave ∈ (replay.current (index + 1)).modes :=
    (replay.step index).rawMissing_subset_next_modes rawMissing
  exact neverGenerated ⟨index + 1, nextMem⟩

structure GeneratedLocalReplayV2WeakClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) where
  stateLimit : SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage)
  stateLimit_mem :
    stateLimit ∈ closure (localReplayV2SpaceTimePathFamily replay)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  state_tendsto :
    Tendsto
      (fun index =>
        localReplayV2SpaceTimePath replay (subsequence index))
      atTop (𝓝 stateLimit)
  puncturedRow_weak :
    ∀ wave : IntegerWavevector,
      wave ≠ 0 →
      ∃ nonlinearLimit :
          NonlinearRowSpaceTimeState
            (sourceOwnedLocalReplayV2Duration lineage),
        Tendsto
            (fun index =>
              wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (replay.current (subsequence index)).trajectory
                (HasDerivAt.continuousOn fun time timeMem =>
                  ((replay.current (subsequence index)).physical
                    time timeMem).1)
                (fun time timeMem =>
                  ((replay.current (subsequence index)).physical
                    time timeMem).2.2.1)
                wave)
            atTop (𝓝 nonlinearLimit) ∧
          ∀ (test testDerivative : ℝ → ℂ),
            ∀ (testHasDeriv :
                ∀ time ∈ Icc (0 : ℝ)
                    (sourceOwnedLocalReplayV2Duration lineage),
                  HasDerivAt test (testDerivative time) time)
              (testDerivativeContinuous :
                ContinuousOn testDerivative
                  (Icc (0 : ℝ)
                    (sourceOwnedLocalReplayV2Duration lineage)))
              (_testZero : test 0 = 0)
              (_testTerminalZero :
                test (sourceOwnedLocalReplayV2Duration lineage) = 0),
            fixedWaveWeakAction
                (sourceOwnedLocalReplayV2Duration lineage)
                ν.coeff wave
                (restrictedScalarL2
                  (sourceOwnedLocalReplayV2Duration lineage) test
                  (fun time timeMem =>
                    (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                (restrictedScalarL2
                  (sourceOwnedLocalReplayV2Duration lineage) testDerivative
                  testDerivativeContinuous)
                (restrictedScalarLInf
                  (sourceOwnedLocalReplayV2Duration lineage) test
                  (fun time timeMem =>
                    (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                stateLimit nonlinearLimit = 0

/-- Generate the punctured whole weak equation from the actual unconditional
V2 replay and its source-owned local budgets. -/
noncomputable def generatedLocalReplayV2WeakClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    GeneratedLocalReplayV2WeakClosure replay := by
  let strongExists :=
    exists_localReplayV2SpaceTime_strong_subsequence replay
  let stateLimit := Classical.choose strongExists
  have stateLimitSpec := Classical.choose_spec strongExists
  have stateLimitMem := stateLimitSpec.1
  let subsequence := Classical.choose stateLimitSpec.2
  have subsequenceSpec := Classical.choose_spec stateLimitSpec.2
  have subsequenceMono := subsequenceSpec.1
  have stateTendsto := subsequenceSpec.2.1
  refine
    { stateLimit := stateLimit
      stateLimit_mem := stateLimitMem
      subsequence := subsequence
      subsequence_strictMono := subsequenceMono
      state_tendsto := stateTendsto
      puncturedRow_weak := ?_ }
  intro wave waveNonzero
  let modes : ℕ → Finset IntegerWavevector := fun index =>
    (replay.current (subsequence index)).modes
  let trajectories : ℕ → ℝ → ComplexVorticityHilbertState := fun index =>
    (replay.current (subsequence index)).trajectory
  let trajectoryContinuous :
      ∀ index,
        ContinuousOn (trajectories index)
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :=
    fun index => HasDerivAt.continuousOn fun time timeMem =>
      ((replay.current (subsequence index)).physical time timeMem).1
  have evolves :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) →
          HasDerivAt (trajectories index)
            (finiteStateVorticityGenerator
              (modes index) ν.coeff (trajectories index time)) time := by
    intro index time timeMem
    exact ((replay.current (subsequence index)).physical time timeMem).1
  have supported :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) →
          ∀ output, output ∉ modes index →
            trajectories index time output = 0 := by
    intro index time timeMem output outputNotMem
    exact ((replay.current (subsequence index)).physical
      time timeMem).2.1 output outputNotMem
  have transverse :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage) →
          WholeStateTransverse (trajectories index time) := by
    intro index time timeMem output
    exact ((replay.current (subsequence index)).physical
      time timeMem).2.2.1 output
  have finiteWeakEventually :
      ∀ᶠ index : ℕ in atTop,
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈ Icc (0 : ℝ)
                  (sourceOwnedLocalReplayV2Duration lineage),
                HasDerivAt test (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ)
                  (sourceOwnedLocalReplayV2Duration lineage)))
            (testZero : test 0 = 0)
            (testTerminalZero :
              test (sourceOwnedLocalReplayV2Duration lineage) = 0),
          fixedWaveWeakAction
              (sourceOwnedLocalReplayV2Duration lineage) ν.coeff wave
              (restrictedScalarL2
                (sourceOwnedLocalReplayV2Duration lineage) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                (sourceOwnedLocalReplayV2Duration lineage) testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                (sourceOwnedLocalReplayV2Duration lineage) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (wholeTrajectorySpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (trajectories index) (trajectoryContinuous index))
              (wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (trajectories index) (trajectoryContinuous index)
                (transverse index) wave) = 0 := by
    by_cases waveGenerated :
        ∃ entry : ℕ, wave ∈ (replay.current entry).modes
    · have waveEventuallyMem :
          ∀ᶠ index : ℕ in atTop, wave ∈ modes index := by
        simpa only [modes] using
          localReplayV2Wave_eventually_mem_comp_strictMono
            replay subsequence subsequenceMono wave waveGenerated
      filter_upwards [waveEventuallyMem] with index waveMem
      intro test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
      simpa [modes, trajectories, trajectoryContinuous] using
        finiteSupportWave_infiniteRow_weak_identity
          (modes index) wave waveMem ν.coeff
          (sourceOwnedLocalReplayV2Duration lineage) durationPos
          (trajectories index)
          (fun time timeMem => evolves index time timeMem)
          (fun time timeMem => supported index time timeMem)
          (transverse index)
          test testDerivative testHasDeriv
          testDerivativeContinuous testZero testTerminalZero
    · apply Filter.Eventually.of_forall
      intro index test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
      have residualZero :
          ∀ time ∈ Icc (0 : ℝ)
              (sourceOwnedLocalReplayV2Duration lineage),
            wholeLatticeVorticityFourierPDEResidualAt
                ν.coeff (trajectories index time)
                (finiteStateVorticityGenerator
                  (modes index) ν.coeff (trajectories index time)) wave = 0 := by
        intro time timeMem
        simpa [modes, trajectories,
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual] using
          localReplayV2Residual_eq_zero_of_never_generated
            replay wave waveNonzero waveGenerated
            (subsequence index) time timeMem
      simpa [modes, trajectories, trajectoryContinuous] using
        finiteSupportWave_infiniteRow_weak_identity_of_wholeResidual_zero
          (modes index) wave ν.coeff
          (sourceOwnedLocalReplayV2Duration lineage) durationPos
          (trajectories index)
          (fun time timeMem => evolves index time timeMem)
          (fun time timeMem => supported index time timeMem)
          (transverse index) residualZero
          test testDerivative testHasDeriv
          testDerivativeContinuous testZero testTerminalZero
  have stateTendstoWhole :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (trajectories index) (trajectoryContinuous index))
        atTop (𝓝 stateLimit) := by
    have pathEq :
        (fun index =>
          wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (trajectories index) (trajectoryContinuous index)) =
          (fun index =>
            localReplayV2SpaceTimePath replay (subsequence index)) := by
      funext index
      exact
        (localReplayV2SpaceTimePath_eq_wholeTrajectory
          replay (subsequence index)).symm
    rw [pathEq]
    exact stateTendsto
  simpa [trajectories, trajectoryContinuous] using
    fixedWave_weakLimit_all_tests_of_wholeTendsto_of_eventually_weak
      ν.coeff (sourceOwnedLocalReplayV2Duration lineage) durationPos
      trajectories trajectoryContinuous transverse
      stateLimit stateTendstoWhole wave finiteWeakEventually

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWeakClosure
end NavierStokes
end SaturationMonoid

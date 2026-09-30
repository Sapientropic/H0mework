import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayRuntime
import H0mework.NavierStokes.ShellGluing.NativeMacroWholeResidualCommonTimeReplayWeakClosure
import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveResidualSilenceWeakCarrier

/-!
# Requested-time punctured-lattice weak closure

An infinite source-generated requested-time replay already supplies the
actual unforced finite Galerkin trajectory on every generated support.  This
module identifies those trajectories with the canonical compactness family
on the exact caller-requested positive interval, then generates one strong
whole-state subsequence and the distributional weak equation at every
nonzero Fourier row.

The compactness limit, subsequence, nonlinear row limits, and the
generated-or-never-generated row split are internal outputs.  The theorem
mouth contains no trajectory, target limit, coverage certificate, cutoff,
critical margin, continuation witness, or response branch.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure

open scoped ENNReal Topology

open Set
open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateGeneratedCriticalPath
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplayWeakClosure
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime

noncomputable section

private theorem requestedHalf_lt_one : (1 / 2 : ℝ) < 1 := by
  norm_num

namespace GeneratedRequestedTimeReplayStage

theorem requestedInitial_supported
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    ∀ wave, wave ∉ stage.modes →
      commonTimeReplayInitialState lineage wave = 0 := by
  intro wave waveNotMem
  exact
    commonTimeReplayInitialState_supported lineage wave
      (fun waveMem =>
        waveNotMem (stage.initialModes_subset waveMem))

theorem requestedInitial_transverse
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (_stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    ∀ wave ∈ _stage.modes,
      complexWavevector wave ⬝ᵥ
          commonTimeReplayInitialState lineage wave =
        0 := by
  intro wave _waveMem
  exact commonTimeReplayInitialState_transverse lineage wave

theorem requestedInitial_reality
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (_stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime) :
    FiniteStateFourierReality
      (commonTimeReplayInitialState lineage) :=
  commonTimeReplayInitialState_reality lineage

/--
Every requested-time stage has the same source-owned half-critical initial
state.  Support refinement adds only initially zero rows.
-/
theorem requestedInitial_halfCritical
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            stage.modes
            (commonTimeReplayInitialState lineage) ≤
      (1 / 2 : ℝ) * ν.coeff ^ 2 *
        (2 * Real.pi) ^ 2 := by
  have baseCritical :
      criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (lineageReceiptModes lineage 0)
              (commonTimeReplayInitialState lineage) ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 *
          (2 * Real.pi) ^ 2 := by
    simpa [lineageHalfCriticalCrossing,
      commonTimeReplayInitialState] using
      le_of_not_gt initialSubcritical
  have enstrophyLe :
      finiteStateVorticityCoefficientEnstrophy
          stage.modes
          (commonTimeReplayInitialState lineage) ≤
        finiteStateVorticityCoefficientEnstrophy
          (lineageReceiptModes lineage 0)
          (commonTimeReplayInitialState lineage) :=
    finiteStateVorticityCoefficientEnstrophy_le_of_supported
      stage.modes (lineageReceiptModes lineage 0)
      (commonTimeReplayInitialState lineage)
      (commonTimeReplayInitialState_supported lineage)
  exact
    (mul_le_mul_of_nonneg_left enstrophyLe
      criticalEnstrophyLatticeConstant_nonneg).trans
      baseCritical

/--
Compile one actual requested-time stage into the existing half-critical
compactness path without replacing either its support or initial state.
-/
def toCriticalScalePath
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    GeneratedCriticalScalePath ν (1 / 2 : ℝ) :=
  generatedCriticalScalePathOfFinitePhysicalState
    stage.modes stage.zero_not_mem stage.waveNeg_mem
    ν (1 / 2 : ℝ)
    (commonTimeReplayInitialState lineage)
    (requestedInitial_supported stage)
    (requestedInitial_transverse stage)
    (requestedInitial_reality stage)
    (requestedInitial_halfCritical stage initialSubcritical)

@[simp] theorem toCriticalScalePath_support
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    generatedSupport
        (toCriticalScalePath stage initialSubcritical).current =
      stage.modes := by
  change
    generatedSupport
        (rawSourceOfFiniteVorticityState stage.modes
          (commonTimeReplayInitialState lineage)) =
      stage.modes
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      stage.modes stage.zero_not_mem stage.waveNeg_mem
      (commonTimeReplayInitialState lineage)

@[simp] theorem toCriticalScalePath_initialState
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0) :
    generatedComplexVorticityState
        (toCriticalScalePath stage initialSubcritical).current
        (generatedSupport
          (toCriticalScalePath stage initialSubcritical).current) =
      commonTimeReplayInitialState lineage := by
  exact
    generatedCriticalScalePathOfFinitePhysicalState_initialState
      stage.modes stage.zero_not_mem stage.waveNeg_mem
      ν (1 / 2 : ℝ)
      (commonTimeReplayInitialState lineage)
      (requestedInitial_supported stage)
      (requestedInitial_transverse stage)
      (requestedInitial_reality stage)
      (requestedInitial_halfCritical stage initialSubcritical)

/--
The canonical compactness trajectory and the actual requested-time
trajectory are the same unforced Galerkin orbit on the exact interval.
-/
theorem trajectory_eq_criticalPathTrajectory
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTimePos : 0 < requestedTime) :
    EqOn stage.trajectory
      ((toCriticalScalePath stage initialSubcritical).commonTimeBudget
        requestedHalf_lt_one requestedTimePos).trajectory
      (Icc 0 requestedTime) := by
  let path := toCriticalScalePath stage initialSubcritical
  let budget :=
    path.commonTimeBudget
      requestedHalf_lt_one requestedTimePos
  apply finiteGalerkinTrajectories_eqOn_Icc_of_same_initial
      stage.modes ν.coeff requestedTime
      stage.trajectory budget.trajectory
  · intro time timeMem
    exact (stage.physical time timeMem).1
  · intro time timeMem
    simpa [path, budget] using
      (budget.physicalProperties time timeMem).1
  · calc
      stage.trajectory 0 =
          commonTimeReplayInitialState lineage :=
        stage.initial
      _ =
          generatedComplexVorticityState path.current
            (generatedSupport path.current) := by
        simpa [path] using
          (toCriticalScalePath_initialState
            stage initialSubcritical).symm
      _ = budget.trajectory 0 :=
        budget.initial.symm

/--
The canonical strong-compactness path is exactly the actual requested-time
trajectory after same-support, same-initial unforced gluing.
-/
theorem criticalSpaceTimePath_eq_replayTrajectory
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTimePos : 0 < requestedTime) :
    generatedCriticalSpaceTimePath
        requestedHalf_lt_one requestedTimePos
        (toCriticalScalePath stage initialSubcritical) =
      wholeTrajectorySpaceTimePath
        requestedTime stage.trajectory
        (HasDerivAt.continuousOn
          (fun time timeMem =>
            (stage.physical time timeMem).1)) := by
  unfold generatedCriticalSpaceTimePath
    generatedWholeBoundedPath generatedWholeTrajectory
    wholeTrajectorySpaceTimePath wholeTrajectoryBoundedPath
  congr 1
  apply BoundedContinuousFunction.ext
  intro time
  exact
    (trajectory_eq_criticalPathTrajectory
      stage initialSubcritical requestedTimePos time.2).symm

end GeneratedRequestedTimeReplayStage

open GeneratedRequestedTimeReplayStage

/-- Compactness path compiled from one actual requested-time replay stage. -/
def requestedTimeReplayCriticalPath
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
    GeneratedCriticalScalePath ν (1 / 2 : ℝ) :=
  toCriticalScalePath
    (replay.current index) initialSubcritical

@[simp] theorem requestedTimeReplayCriticalPath_support
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
    generatedSupport
        (requestedTimeReplayCriticalPath replay index).current =
      (replay.current index).modes :=
  toCriticalScalePath_support
    (replay.current index) initialSubcritical

/-- A generated row remains present along every strict compactness subsequence. -/
theorem generatedRequestedTimeReplayWave_eventually_mem_comp_strictMono
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos)
    (subsequence : ℕ → ℕ)
    (subsequenceMono : StrictMono subsequence)
    (wave : IntegerWavevector)
    (waveGenerated :
      ∃ entry : ℕ,
        wave ∈ (replay.current entry).modes) :
    ∀ᶠ index : ℕ in atTop,
      wave ∈
        generatedSupport
          (requestedTimeReplayCriticalPath replay
            (subsequence index)).current := by
  rcases waveGenerated with ⟨entry, waveMem⟩
  have eventuallyInReplay :
      ∀ᶠ index : ℕ in atTop,
        wave ∈ (replay.current index).modes := by
    apply Filter.eventually_atTop.2
    refine ⟨entry, ?_⟩
    intro index entryLe
    exact
      ((GeneratedRequestedTimeReplayInfiniteLineage.modes_strictMono
        replay).monotone entryLe) waveMem
  simpa only [requestedTimeReplayCriticalPath_support] using
    subsequenceMono.tendsto_atTop.eventually
      eventuallyInReplay

/--
The actual requested-time trajectories generate one strong whole-carrier
subsequence on the exact requested interval.
-/
theorem exists_requestedTimeReplayTrajectory_strong_subsequence
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) :
    ∃ limit : SpaceTimeState requestedTime,
      limit ∈
          closure
            (generatedCriticalSpaceTimePathFamily
              (ν := ν) requestedHalf_lt_one requestedTimePos) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
          (fun index =>
            wholeTrajectorySpaceTimePath
              requestedTime
              (replay.current
                (subsequence index)).trajectory
              (HasDerivAt.continuousOn
                (fun time timeMem =>
                  ((replay.current
                    (subsequence index)).physical
                      time timeMem).1)))
          atTop (𝓝 limit) := by
  obtain
      ⟨limit, limitMem, subsequence, subsequenceMono,
        wholeTendsto, _wholeStrong, _fixedRows,
        _fixedRowsStrong⟩ :=
    generatedCriticalSpaceTimePath_strong_subsequence_with_fixed_wave_rows
      requestedHalf_lt_one requestedTimePos
      (requestedTimeReplayCriticalPath replay)
  refine
    ⟨limit, limitMem, subsequence, subsequenceMono, ?_⟩
  simpa only [
    requestedTimeReplayCriticalPath,
    criticalSpaceTimePath_eq_replayTrajectory] using
      wholeTendsto

/-- A raw residual row is written into the support of the exact next stage. -/
theorem nativeRequestedTimeReplayStep_rawMissing_mem_next
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {current next :
      GeneratedRequestedTimeReplayStage lineage requestedTime}
    (step :
      NativeRequestedTimeReplayStep
        lineage initialSubcritical requestedTime requestedTimePos
        current next)
    {wave : IntegerWavevector}
    (waveMem :
      wave ∈
        GeneratedRequestedTimeReplayStage.rawWholeSpaceTimeMissingModes
          current) :
    wave ∈ next.modes := by
  cases step with
  | expand _missingNonempty =>
      rw [
        GeneratedRequestedTimeReplayStage.wholeSpaceTimeNext_modes,
        GeneratedRequestedTimeReplayStage.wholeSpaceTimeNextModes]
      exact
        Finset.mem_union_right _
          (GeneratedRequestedTimeReplayStage.rawMissing_subset_missing
            current waveMem)

/--
If a nonzero row never enters the generated support, its actual requested
interval whole-PDE residual vanishes at every replay stage.
-/
theorem requestedTimeResidual_eq_zero_of_never_generated
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (neverGenerated :
      ¬ ∃ entry : ℕ,
        wave ∈ (replay.current entry).modes)
    (index : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual
        (replay.current index) time wave =
      0 := by
  by_contra residualNonzero
  have waveNotMem :
      wave ∉ (replay.current index).modes := by
    intro waveMem
    exact neverGenerated ⟨index, waveMem⟩
  have pairMem :
      wave ∈
        finiteVorticityPairOutputSupport
          (replay.current index).modes := by
    by_contra pairNotMem
    exact
      residualNonzero
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
  have nextMem :
      wave ∈ (replay.current (index + 1)).modes :=
    nativeRequestedTimeReplayStep_rawMissing_mem_next
      (replay.step index) rawMissing
  exact neverGenerated ⟨index + 1, nextMem⟩

/--
One internally generated strong whole-state limit and subsequence satisfy
the distributional vorticity equation at every nonzero Fourier row on the
exact requested interval.
-/
structure GeneratedRequestedTimeReplayWeakClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) where
  stateLimit : SpaceTimeState requestedTime
  stateLimit_mem :
    stateLimit ∈
      closure
        (generatedCriticalSpaceTimePathFamily
          (ν := ν) requestedHalf_lt_one requestedTimePos)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  state_tendsto :
    Tendsto
      (fun index =>
        wholeTrajectorySpaceTimePath
          requestedTime
          (replay.current (subsequence index)).trajectory
          (HasDerivAt.continuousOn
            (fun time timeMem =>
              ((replay.current
                (subsequence index)).physical
                  time timeMem).1)))
      atTop (𝓝 stateLimit)
  puncturedRow_weak :
    ∀ wave : IntegerWavevector,
      wave ≠ 0 →
      ∃ nonlinearLimit :
          NonlinearRowSpaceTimeState requestedTime,
        Tendsto
            (fun index =>
              wholeNonlinearRowSpaceTimePath
                requestedTime
                (replay.current
                  (subsequence index)).trajectory
                (fun time timeMem =>
                  (((replay.current
                    (subsequence index)).physical
                      time timeMem).1).continuousAt.continuousWithinAt)
                (fun time timeMem =>
                  ((replay.current
                    (subsequence index)).physical
                      time timeMem).2.2.1)
                wave)
            atTop (𝓝 nonlinearLimit) ∧
          ∀ (test testDerivative : ℝ → ℂ),
            ∀ (testHasDeriv :
                ∀ time ∈ Icc (0 : ℝ) requestedTime,
                  HasDerivAt test
                    (testDerivative time) time)
              (testDerivativeContinuous :
                ContinuousOn testDerivative
                  (Icc (0 : ℝ) requestedTime))
              (_testZero : test 0 = 0)
              (_testTerminalZero :
                test requestedTime = 0),
            fixedWaveWeakAction
                requestedTime ν.coeff wave
                (restrictedScalarL2
                  requestedTime test
                  (fun time timeMem =>
                    (testHasDeriv
                      time timeMem).continuousAt.continuousWithinAt))
                (restrictedScalarL2
                  requestedTime testDerivative
                  testDerivativeContinuous)
                (restrictedScalarLInf
                  requestedTime test
                  (fun time timeMem =>
                    (testHasDeriv
                      time timeMem).continuousAt.continuousWithinAt))
                stateLimit nonlinearLimit =
              0

/--
Generate the full punctured-lattice weak closure from the actual infinite
requested-time replay.  Compactness choices and the generated-or-silent row
exhaustion are constructed internally.
-/
noncomputable def generatedRequestedTimeReplayWeakClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) :
    GeneratedRequestedTimeReplayWeakClosure replay := by
  let strongExists :=
    exists_requestedTimeReplayTrajectory_strong_subsequence replay
  let stateLimit := Classical.choose strongExists
  have stateLimitSpec := Classical.choose_spec strongExists
  have stateLimitMem := stateLimitSpec.1
  let subsequence := Classical.choose stateLimitSpec.2
  have subsequenceSpec :=
    Classical.choose_spec stateLimitSpec.2
  have subsequenceMono := subsequenceSpec.1
  have stateTendsto := subsequenceSpec.2
  refine
    { stateLimit := stateLimit
      stateLimit_mem := stateLimitMem
      subsequence := subsequence
      subsequence_strictMono := subsequenceMono
      state_tendsto := stateTendsto
      puncturedRow_weak := ?_ }
  intro wave waveNonzero
  let modes : ℕ → Finset IntegerWavevector :=
    fun index =>
      (replay.current (subsequence index)).modes
  let trajectories :
      ℕ → ℝ → ComplexVorticityHilbertState :=
    fun index =>
      (replay.current (subsequence index)).trajectory
  let trajectoryContinuous :
      ∀ index,
        ContinuousOn (trajectories index)
          (Icc (0 : ℝ) requestedTime) :=
    fun index =>
      HasDerivAt.continuousOn
        (fun time timeMem =>
          ((replay.current
            (subsequence index)).physical time timeMem).1)
  have evolves :
      ∀ index time,
        time ∈ Icc (0 : ℝ) requestedTime →
          HasDerivAt (trajectories index)
            (finiteStateVorticityGenerator
              (modes index) ν.coeff
              (trajectories index time))
            time := by
    intro index time timeMem
    exact
      ((replay.current
        (subsequence index)).physical time timeMem).1
  have supported :
      ∀ index time,
        time ∈ Icc (0 : ℝ) requestedTime →
          ∀ output : IntegerWavevector,
            output ∉ modes index →
              trajectories index time output = 0 := by
    intro index time timeMem output outputNotMem
    exact
      ((replay.current
        (subsequence index)).physical time timeMem).2.1
        output outputNotMem
  have transverse :
      ∀ index time,
        time ∈ Icc (0 : ℝ) requestedTime →
          WholeStateTransverse
            (trajectories index time) := by
    intro index time timeMem output
    exact
      ((replay.current
        (subsequence index)).physical time timeMem).2.2.1
        output
  have finiteWeakEventually :
      ∀ᶠ index : ℕ in atTop,
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈ Icc (0 : ℝ) requestedTime,
                HasDerivAt test
                  (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) requestedTime))
            (testZero : test 0 = 0)
            (testTerminalZero :
              test requestedTime = 0),
          fixedWaveWeakAction
              requestedTime ν.coeff wave
              (restrictedScalarL2
                requestedTime test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                requestedTime testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                requestedTime test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              (wholeTrajectorySpaceTimePath
                requestedTime
                (trajectories index)
                (trajectoryContinuous index))
              (wholeNonlinearRowSpaceTimePath
                requestedTime
                (trajectories index)
                (trajectoryContinuous index)
                (transverse index) wave) =
            0 := by
    by_cases waveGenerated :
        ∃ entry : ℕ,
          wave ∈ (replay.current entry).modes
    · have waveEventuallyMem :
          ∀ᶠ index : ℕ in atTop,
            wave ∈ modes index := by
        simpa only [modes,
          requestedTimeReplayCriticalPath_support] using
          generatedRequestedTimeReplayWave_eventually_mem_comp_strictMono
            replay subsequence subsequenceMono wave waveGenerated
      filter_upwards [waveEventuallyMem] with index waveMem
      intro test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
      simpa [modes, trajectories, trajectoryContinuous] using
        finiteSupportWave_infiniteRow_weak_identity
          (modes index) wave waveMem ν.coeff
          requestedTime requestedTimePos
          (trajectories index)
          (fun time timeMem =>
            evolves index time timeMem)
          (fun time timeMem =>
            supported index time timeMem)
          (transverse index)
          test testDerivative testHasDeriv
          testDerivativeContinuous testZero testTerminalZero
    · apply Filter.Eventually.of_forall
      intro index test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
      have residualZero :
          ∀ time ∈ Icc (0 : ℝ) requestedTime,
            wholeLatticeVorticityFourierPDEResidualAt
                ν.coeff (trajectories index time)
                (finiteStateVorticityGenerator
                  (modes index) ν.coeff
                  (trajectories index time))
                wave =
              0 := by
        intro time timeMem
        simpa [modes, trajectories,
          GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual] using
          requestedTimeResidual_eq_zero_of_never_generated
            replay wave waveNonzero waveGenerated
            (subsequence index) time timeMem
      simpa [modes, trajectories, trajectoryContinuous] using
        finiteSupportWave_infiniteRow_weak_identity_of_wholeResidual_zero
          (modes index) wave ν.coeff
          requestedTime requestedTimePos
          (trajectories index)
          (fun time timeMem =>
            evolves index time timeMem)
          (fun time timeMem =>
            supported index time timeMem)
          (transverse index)
          residualZero
          test testDerivative testHasDeriv
          testDerivativeContinuous testZero testTerminalZero
  simpa [trajectories, trajectoryContinuous] using
    fixedWave_weakLimit_all_tests_of_wholeTendsto_of_eventually_weak
      ν.coeff requestedTime requestedTimePos
      trajectories trajectoryContinuous transverse
      stateLimit
      (by simpa [trajectories, trajectoryContinuous] using stateTendsto)
      wave finiteWeakEventually

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure
end NavierStokes
end SaturationMonoid

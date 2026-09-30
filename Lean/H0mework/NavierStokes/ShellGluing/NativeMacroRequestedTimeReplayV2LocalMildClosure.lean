import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalWeakClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness
import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveResidualSilenceMildDuhamel

/-!
# Common-initial mild closure of requested-time residual replay

The complete residual responder already generates one actual unforced
Galerkin replay, one strong whole-carrier subsequence, and a weak nonlinear
row at every nonzero Fourier wave.  This module restores the missing time
trace without adding a coverage premise.

For a fixed nonzero wave the same source replay exhausts two cases:

* the wave is generated and is eventually retained, so the retained-row
  heat/Duhamel identity applies;
* the wave is never generated, so the source responder proves its whole
  residual silent at every stage and every physical time, and the
  residual-silence heat/Duhamel identity applies.

Finite-observation compactness then gives a continuous representative of
the actual strong space-time limit.  Every stage starts from the same
source-owned initial state, so the limiting representative carries that
exact initial trace.  No target path, lattice coverage, cutoff, terminal
witness, or continuation certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildClosure

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplayWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWeakClosure

noncomputable section

/--
One fixed nonzero row of the actual requested-time replay has, on the
same generated subsequence:

* its source-generated nonlinear-row limit;
* its all-tests weak vorticity identity; and
* a continuous common-initial heat/Duhamel representative of the strong
  whole-state limit.

The generated/never-generated exhaustion is internal.  In particular,
eventual support membership is not a theorem premise.
-/
theorem
    GeneratedLocalReplayV2WeakClosure.exists_fixedWaveContinuousMildData
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < (sourceOwnedLocalReplayV2Duration lineage)}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        ((sourceOwnedLocalReplayV2Duration lineage)) durationPos}
    (receipt : GeneratedLocalReplayV2WeakClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∃ nonlinearLimit :
        NonlinearRowSpaceTimeState
          (sourceOwnedLocalReplayV2Duration lineage),
      (Tendsto
          (fun index =>
            wholeNonlinearRowSpaceTimePath
              (sourceOwnedLocalReplayV2Duration lineage)
              (replay.current
                (receipt.subsequence index)).trajectory
              (fun time timeMem =>
                (((replay.current
                  (receipt.subsequence index)).physical
                    time timeMem).1).continuousAt.continuousWithinAt)
              (fun time timeMem =>
                ((replay.current
                  (receipt.subsequence index)).physical
                    time timeMem).2.2.1)
              wave)
          atTop (𝓝 nonlinearLimit) ∧
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈
                  Icc (0 : ℝ)
                    (sourceOwnedLocalReplayV2Duration lineage),
                HasDerivAt test
                  (testDerivative time) time)
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
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                (sourceOwnedLocalReplayV2Duration lineage)
                testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                (sourceOwnedLocalReplayV2Duration lineage) test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              receipt.stateLimit nonlinearLimit =
            0) ∧
      Nonempty
        (FixedWaveContinuousMildData
          (sourceOwnedLocalReplayV2Duration lineage)
          ν.coeff wave
          (fun _index =>
            commonTimeReplayInitialState lineage)
          receipt.stateLimit nonlinearLimit) := by
  classical
  rcases receipt.puncturedRow_weak wave waveNonzero with
    ⟨nonlinearLimit, nonlinearTendsto, weakIdentity⟩
  refine ⟨nonlinearLimit, ⟨nonlinearTendsto, weakIdentity⟩, ?_⟩
  let observed : Finset IntegerWavevector := {wave}
  let coordinate :
      {actual : IntegerWavevector // actual ∈ observed} :=
    ⟨wave, by simp [observed]⟩
  let observedSequence :
      ℕ →
        BoundedContinuousFunction
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
          (FiniteObservedCoefficientState observed) :=
    fun index =>
      localReplayV2FiniteObservedBoundedPath replay observed
        (receipt.subsequence index)
  have observedSequenceMem :
      ∀ index,
        observedSequence index ∈
          closure
            (localReplayV2FiniteObservedPathFamily replay observed) := by
    intro index
    apply subset_closure
    exact ⟨receipt.subsequence index, rfl⟩
  rcases
      (localReplayV2FiniteObservedPathFamily_isCompact_closure
        replay observed).tendsto_subseq
        observedSequenceMem with
    ⟨observedLimit, _observedLimitMem, refinement,
      refinementStrictMono, observedTendsto⟩
  let observedRowMap :
      BoundedContinuousFunction
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
          (FiniteObservedCoefficientState observed) →L[ℂ]
        BoundedContinuousFunction
          (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
          ComplexCoordinateVector :=
    (ContinuousLinearMap.proj coordinate).compLeftContinuousBounded
      (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
  let rowPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage))
        ComplexCoordinateVector :=
    observedRowMap observedLimit
  have observedValue_eq_actual :
      ∀ (index : ℕ)
        (time :
          Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)),
        observedRowMap (observedSequence index) time =
          (replay.current
            (receipt.subsequence index)).trajectory
              time.1 wave := by
    intro index time
    rfl
  have observedRowTendsto :
      Tendsto
        (fun index =>
          observedRowMap
            (observedSequence (refinement index)))
        atTop (𝓝 rowPath) := by
    have mapped :=
      (observedRowMap.continuous.tendsto observedLimit).comp
        observedTendsto
    change
      Tendsto
        (observedRowMap ∘ observedSequence ∘ refinement)
        atTop (𝓝 rowPath)
    simpa only [rowPath] using mapped
  have observedRowSpaceTimeTendsto :
      Tendsto
        (fun index =>
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure
              (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
            (observedRowMap
              (observedSequence (refinement index))))
        atTop
        (𝓝
          ((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure
              (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
            rowPath)) := by
    exact
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure
          (sourceOwnedLocalReplayV2Duration lineage)) ℂ).continuous.tendsto
          rowPath).comp observedRowTendsto
  have stateRefinedTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn
              (fun time timeMem =>
                ((replay.current
                  (receipt.subsequence
                    (refinement index))).physical
                      time timeMem).1)))
        atTop (𝓝 receipt.stateLimit) := by
    have refined :=
      receipt.state_tendsto.comp
        refinementStrictMono.tendsto_atTop
    change
      Tendsto
        ((fun index =>
          wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence index)).trajectory
            (HasDerivAt.continuousOn
              (fun time timeMem =>
                ((replay.current
                  (receipt.subsequence index)).physical
                    time timeMem).1))) ∘ refinement)
        atTop (𝓝 receipt.stateLimit)
    exact refined
  have fixedStateRefinedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (sourceOwnedLocalReplayV2Duration lineage) wave
            (wholeTrajectorySpaceTimePath
              (sourceOwnedLocalReplayV2Duration lineage)
              (replay.current
                (receipt.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn
                (fun time timeMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        time timeMem).1))))
        atTop
        (𝓝
          (fixedWaveSpaceTimeRestriction
            (sourceOwnedLocalReplayV2Duration lineage) wave
            receipt.stateLimit)) := by
    exact
      ((fixedWaveSpaceTimeRestriction
        (sourceOwnedLocalReplayV2Duration lineage) wave).continuous.tendsto
          receipt.stateLimit).comp stateRefinedTendsto
  have observedRowSpaceTime_eq_fixedWave :
      ∀ index,
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure
            (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
            (observedRowMap
              (observedSequence (refinement index))) =
          fixedWaveSpaceTimeRestriction
            (sourceOwnedLocalReplayV2Duration lineage) wave
            (wholeTrajectorySpaceTimePath
              (sourceOwnedLocalReplayV2Duration lineage)
              (replay.current
                (receipt.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn
                (fun time timeMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        time timeMem).1))) := by
    intro index
    apply MeasureTheory.Lp.ext
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure
          (sourceOwnedLocalReplayV2Duration lineage)) ℂ
        (observedRowMap
          (observedSequence (refinement index)))
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        (sourceOwnedLocalReplayV2Duration lineage) wave
        (wholeTrajectorySpaceTimePath
          (sourceOwnedLocalReplayV2Duration lineage)
          (replay.current
            (receipt.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn
            (fun time timeMem =>
              ((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    time timeMem).1)))
    have wholeAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure
          (sourceOwnedLocalReplayV2Duration lineage)) ℂ
        (wholeTrajectoryBoundedPath
          (sourceOwnedLocalReplayV2Duration lineage)
          (replay.current
            (receipt.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn
            (fun time timeMem =>
              ((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    time timeMem).1)))
    filter_upwards [rowAE, restrictionAE, wholeAE] with
      time rowEq restrictionEq wholeEq
    rw [rowEq, restrictionEq]
    have statePoint :
        (wholeTrajectorySpaceTimePath
          (sourceOwnedLocalReplayV2Duration lineage)
          (replay.current
            (receipt.subsequence
              (refinement index))).trajectory
          (HasDerivAt.continuousOn
            (fun actual actualMem =>
              ((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    actual actualMem).1))) time =
          (replay.current
            (receipt.subsequence
              (refinement index))).trajectory time.1 := by
      have statePoint' :
          (wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn
              (fun actual actualMem =>
                ((replay.current
                  (receipt.subsequence
                    (refinement index))).physical
                      actual actualMem).1))) time =
            wholeTrajectoryBoundedPath
              (sourceOwnedLocalReplayV2Duration lineage)
              (replay.current
                (receipt.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn
                (fun actual actualMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).1)) time := by
        simpa [wholeTrajectorySpaceTimePath] using wholeEq
      exact statePoint'.trans rfl
    rw [statePoint]
    exact observedValue_eq_actual (refinement index) time
  have observedAsFixedTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (sourceOwnedLocalReplayV2Duration lineage) wave
            (wholeTrajectorySpaceTimePath
              (sourceOwnedLocalReplayV2Duration lineage)
              (replay.current
                (receipt.subsequence
                  (refinement index))).trajectory
              (HasDerivAt.continuousOn
                (fun time timeMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        time timeMem).1))))
        atTop
        (𝓝
          ((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure
              (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
            rowPath)) := by
    simpa only [observedRowSpaceTime_eq_fixedWave] using
      observedRowSpaceTimeTendsto
  have rowSpaceTimeEq :
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure
          (sourceOwnedLocalReplayV2Duration lineage)) ℂ) rowPath =
        fixedWaveSpaceTimeRestriction
          (sourceOwnedLocalReplayV2Duration lineage) wave
          receipt.stateLimit :=
    tendsto_nhds_unique
      observedAsFixedTendsto fixedStateRefinedTendsto
  have rowRepresents :
      ∀ᵐ time
          ∂(commonTimeMeasure
            (sourceOwnedLocalReplayV2Duration lineage)),
        rowPath time =
          fixedWaveSpaceTimeRestriction
            (sourceOwnedLocalReplayV2Duration lineage) wave
            receipt.stateLimit time := by
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure
          (sourceOwnedLocalReplayV2Duration lineage)) ℂ
        rowPath
    rw [rowSpaceTimeEq] at rowAE
    exact rowAE.symm
  have nonlinearRefinedTendsto :
      Tendsto
        (fun index =>
          wholeNonlinearRowSpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence
                (refinement index))).trajectory
            (fun time timeMem =>
              (((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    time timeMem).1).continuousAt.continuousWithinAt)
            (fun time timeMem =>
              ((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    time timeMem).2.2.1)
            wave)
        atTop (𝓝 nonlinearLimit) := by
    have refined :=
      nonlinearTendsto.comp
        refinementStrictMono.tendsto_atTop
    change
      Tendsto
        ((fun index =>
          wholeNonlinearRowSpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence index)).trajectory
            (fun time timeMem =>
              (((replay.current
                (receipt.subsequence index)).physical
                  time timeMem).1).continuousAt.continuousWithinAt)
            (fun time timeMem =>
              ((replay.current
                (receipt.subsequence index)).physical
                  time timeMem).2.2.1)
            wave) ∘ refinement)
        atTop (𝓝 nonlinearLimit)
    exact refined
  have mildIdentity :
      ∀ time :
          Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
        rowPath time =
          fixedWaveHeatDuhamelValue
            (sourceOwnedLocalReplayV2Duration lineage)
            ν.coeff wave
            (commonTimeReplayInitialState lineage wave)
            nonlinearLimit time := by
    intro time
    have observedValueTendsto :
        Tendsto
          (fun index =>
            observedRowMap
              (observedSequence (refinement index)) time)
          atTop (𝓝 (rowPath time)) := by
      have evaluated :=
        ((BoundedContinuousFunction.evalCLM
          ℂ time).continuous.tendsto rowPath).comp
            observedRowTendsto
      change
        Tendsto
          ((BoundedContinuousFunction.evalCLM ℂ time) ∘
            (fun index =>
              observedRowMap
                (observedSequence (refinement index))))
          atTop (𝓝 (rowPath time))
      exact evaluated
    have duhamelTendsto :
        Tendsto
          (fun index =>
            fixedWaveHeatDuhamelValue
              (sourceOwnedLocalReplayV2Duration lineage)
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (replay.current
                  (receipt.subsequence
                    (refinement index))).trajectory
                (fun actual actualMem =>
                  (((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).1).continuousAt.continuousWithinAt)
                (fun actual actualMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).2.2.1)
                wave)
              time)
          atTop
          (𝓝
            (fixedWaveHeatDuhamelValue
              (sourceOwnedLocalReplayV2Duration lineage)
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              nonlinearLimit time)) :=
      tendsto_fixedWaveHeatDuhamelValue
        (sourceOwnedLocalReplayV2Duration lineage)
        ν.coeff ν.coeff_pos.le wave time
        (fun _index =>
          commonTimeReplayInitialState lineage wave)
        (fun index =>
          wholeNonlinearRowSpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage)
            (replay.current
              (receipt.subsequence
                (refinement index))).trajectory
            (fun actual actualMem =>
              (((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    actual actualMem).1).continuousAt.continuousWithinAt)
            (fun actual actualMem =>
              ((replay.current
                (receipt.subsequence
                  (refinement index))).physical
                    actual actualMem).2.2.1)
            wave)
        (commonTimeReplayInitialState lineage wave)
        nonlinearLimit
        tendsto_const_nhds nonlinearRefinedTendsto
    have finiteMildEventually :
        (fun index =>
          observedRowMap
            (observedSequence (refinement index)) time) =ᶠ[atTop]
          (fun index =>
            fixedWaveHeatDuhamelValue
              (sourceOwnedLocalReplayV2Duration lineage)
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (replay.current
                  (receipt.subsequence
                    (refinement index))).trajectory
                (fun actual actualMem =>
                  (((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).1).continuousAt.continuousWithinAt)
                (fun actual actualMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).2.2.1)
                wave)
              time) := by
      by_cases waveGenerated :
          ∃ entry : ℕ,
            wave ∈ (replay.current entry).modes
      · have retainedEventually :
            ∀ᶠ index : ℕ in atTop,
              wave ∈
                (replay.current
                  ((receipt.subsequence ∘ refinement)
                    index)).modes := by
          exact
            localReplayV2Wave_eventually_mem_comp_strictMono
              replay (receipt.subsequence ∘ refinement)
              (receipt.subsequence_strictMono.comp
                refinementStrictMono)
              wave waveGenerated
        filter_upwards [retainedEventually] with index waveMem
        change
          observedRowMap
              (observedSequence (refinement index)) time =
            fixedWaveHeatDuhamelValue
              (sourceOwnedLocalReplayV2Duration lineage)
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (replay.current
                  (receipt.subsequence
                    (refinement index))).trajectory
                (fun actual actualMem =>
                  (((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).1).continuousAt.continuousWithinAt)
                (fun actual actualMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).2.2.1)
                wave)
              time
        rw [observedValue_eq_actual (refinement index) time]
        let stage :=
          replay.current
            (receipt.subsequence (refinement index))
        have actual :=
          finiteSupportWave_eq_fixedWaveHeatDuhamelValue
            stage.modes wave waveMem ν.coeff
            (sourceOwnedLocalReplayV2Duration lineage)
            (durationPos)
            stage.trajectory
            (fun actual actualMem =>
              (stage.physical actual actualMem).1)
            (fun actual actualMem =>
              (stage.physical actual actualMem).2.1)
            (fun actual actualMem =>
              (stage.physical actual actualMem).2.2.1)
            time
        rw [stage.initial] at actual
        simpa only [stage] using actual
      · apply Filter.Eventually.of_forall
        intro index
        change
          observedRowMap
              (observedSequence (refinement index)) time =
            fixedWaveHeatDuhamelValue
              (sourceOwnedLocalReplayV2Duration lineage)
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                (sourceOwnedLocalReplayV2Duration lineage)
                (replay.current
                  (receipt.subsequence
                    (refinement index))).trajectory
                (fun actual actualMem =>
                  (((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).1).continuousAt.continuousWithinAt)
                (fun actual actualMem =>
                  ((replay.current
                    (receipt.subsequence
                      (refinement index))).physical
                        actual actualMem).2.2.1)
                wave)
              time
        rw [observedValue_eq_actual (refinement index) time]
        let stage :=
          replay.current
            (receipt.subsequence (refinement index))
        have residualZero :
            ∀ actual ∈
                Icc (0 : ℝ)
                  (sourceOwnedLocalReplayV2Duration lineage),
              wholeLatticeVorticityFourierPDEResidualAt
                  ν.coeff (stage.trajectory actual)
                  (finiteStateVorticityGenerator
                    stage.modes ν.coeff
                    (stage.trajectory actual))
                  wave =
                0 := by
          intro actual actualMem
          simpa [stage,
            ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource.GeneratedRequestedTimeReplayStage.wholeSpaceTimeResidual] using
            localReplayV2Residual_eq_zero_of_never_generated
              replay wave waveNonzero waveGenerated
              (receipt.subsequence (refinement index))
              actual actualMem
        have actual :=
          finiteSupportWave_eq_fixedWaveHeatDuhamelValue_of_wholeResidual_zero
            stage.modes wave ν.coeff
            (sourceOwnedLocalReplayV2Duration lineage)
            (durationPos)
            stage.trajectory
            (fun actual actualMem =>
              (stage.physical actual actualMem).1)
            (fun actual actualMem =>
              (stage.physical actual actualMem).2.1)
            (fun actual actualMem =>
              (stage.physical actual actualMem).2.2.1)
            residualZero time
        rw [stage.initial] at actual
        simpa only [stage] using actual
    exact
      tendsto_nhds_unique observedValueTendsto
        (duhamelTendsto.congr' finiteMildEventually.symm)
  exact
    ⟨
      { initialLimit :=
          commonTimeReplayInitialState lineage
        initial_tendsto := tendsto_const_nhds
        rowPath := rowPath
        row_represents := rowRepresents
        mild_identity := mildIdentity }⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildClosure
end NavierStokes
end SaturationMonoid

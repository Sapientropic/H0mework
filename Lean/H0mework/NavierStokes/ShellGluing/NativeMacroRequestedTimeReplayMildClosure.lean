import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWeakClosure
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildClosure

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
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure.GeneratedRequestedTimeReplayStage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplaySource
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure

noncomputable section

private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by
  norm_num

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
    GeneratedRequestedTimeReplayWeakClosure.exists_fixedWaveContinuousMildData
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (receipt : GeneratedRequestedTimeReplayWeakClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∃ nonlinearLimit :
        NonlinearRowSpaceTimeState
          requestedTime,
      (Tendsto
          (fun index =>
            wholeNonlinearRowSpaceTimePath
              requestedTime
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
                    requestedTime,
                HasDerivAt test
                  (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ)
                  requestedTime))
            (_testZero : test 0 = 0)
            (_testTerminalZero :
              test requestedTime = 0),
          fixedWaveWeakAction
              requestedTime
              ν.coeff wave
              (restrictedScalarL2
                requestedTime test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                requestedTime
                testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                requestedTime test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              receipt.stateLimit nonlinearLimit =
            0) ∧
      Nonempty
        (FixedWaveContinuousMildData
          requestedTime
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
  let pathSequence :
      ℕ → GeneratedCriticalScalePath ν (1 / 2 : ℝ) :=
    fun index =>
      requestedTimeReplayCriticalPath replay
        (receipt.subsequence index)
  let observedSequence :
      ℕ →
        BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          (FiniteObservedCoefficientState observed) :=
    fun index =>
      generatedFiniteObservedBoundedPath
        half_lt_one (requestedTimePos)
        observed (pathSequence index)
  have observedSequenceMem :
      ∀ index,
        observedSequence index ∈
          closure
            (generatedFiniteObservedPathFamily
              (ν := ν) half_lt_one
              (requestedTimePos)
              observed) := by
    intro index
    apply subset_closure
    exact ⟨pathSequence index, rfl⟩
  rcases
      (generatedFiniteObservedPathFamily_isCompact_closure
        (ν := ν) half_lt_one
        (requestedTimePos)
        observed).tendsto_subseq
        observedSequenceMem with
    ⟨observedLimit, _observedLimitMem, refinement,
      refinementStrictMono, observedTendsto⟩
  let observedRowMap :
      BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          (FiniteObservedCoefficientState observed) →L[ℂ]
        BoundedContinuousFunction
          (Icc (0 : ℝ) requestedTime)
          ComplexCoordinateVector :=
    (ContinuousLinearMap.proj coordinate).compLeftContinuousBounded
      (Icc (0 : ℝ) requestedTime)
  let rowPath :
      BoundedContinuousFunction
        (Icc (0 : ℝ) requestedTime)
        ComplexCoordinateVector :=
    observedRowMap observedLimit
  have observedValue_eq_actual :
      ∀ (index : ℕ)
        (time :
          Icc (0 : ℝ) requestedTime),
        observedRowMap (observedSequence index) time =
          (replay.current
            (receipt.subsequence index)).trajectory
              time.1 wave := by
    intro index time
    change
      ((toCriticalScalePath
          (replay.current (receipt.subsequence index))
          initialSubcritical).commonTimeBudget
        half_lt_one
        (requestedTimePos)).trajectory
          time.1 wave =
        (replay.current
          (receipt.subsequence index)).trajectory
            time.1 wave
    exact
      congrArg (fun state => state wave)
        ((trajectory_eq_criticalPathTrajectory
          (replay.current (receipt.subsequence index))
          initialSubcritical requestedTimePos time.2).symm)
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
              requestedTime) ℂ)
            (observedRowMap
              (observedSequence (refinement index))))
        atTop
        (𝓝
          ((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure
              requestedTime) ℂ)
            rowPath)) := by
    exact
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure
          requestedTime) ℂ).continuous.tendsto
          rowPath).comp observedRowTendsto
  have stateRefinedTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            requestedTime
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
            requestedTime
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
            requestedTime wave
            (wholeTrajectorySpaceTimePath
              requestedTime
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
            requestedTime wave
            receipt.stateLimit)) := by
    exact
      ((fixedWaveSpaceTimeRestriction
        requestedTime wave).continuous.tendsto
          receipt.stateLimit).comp stateRefinedTendsto
  have observedRowSpaceTime_eq_fixedWave :
      ∀ index,
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure
            requestedTime) ℂ)
            (observedRowMap
              (observedSequence (refinement index))) =
          fixedWaveSpaceTimeRestriction
            requestedTime wave
            (wholeTrajectorySpaceTimePath
              requestedTime
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
          requestedTime) ℂ
        (observedRowMap
          (observedSequence (refinement index)))
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave
        (wholeTrajectorySpaceTimePath
          requestedTime
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
          requestedTime) ℂ
        (wholeTrajectoryBoundedPath
          requestedTime
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
          requestedTime
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
            requestedTime
            (replay.current
              (receipt.subsequence
                (refinement index))).trajectory
            (HasDerivAt.continuousOn
              (fun actual actualMem =>
                ((replay.current
                  (receipt.subsequence
                    (refinement index))).physical
                      actual actualMem).1))) time =
            wholeTrajectoryBoundedPath requestedTime
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
            requestedTime wave
            (wholeTrajectorySpaceTimePath
              requestedTime
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
              requestedTime) ℂ)
            rowPath)) := by
    simpa only [observedRowSpaceTime_eq_fixedWave] using
      observedRowSpaceTimeTendsto
  have rowSpaceTimeEq :
      (BoundedContinuousFunction.toLp 2
        (commonTimeMeasure
          requestedTime) ℂ) rowPath =
        fixedWaveSpaceTimeRestriction
          requestedTime wave
          receipt.stateLimit :=
    tendsto_nhds_unique
      observedAsFixedTendsto fixedStateRefinedTendsto
  have rowRepresents :
      ∀ᵐ time
          ∂(commonTimeMeasure
            requestedTime),
        rowPath time =
          fixedWaveSpaceTimeRestriction
            requestedTime wave
            receipt.stateLimit time := by
    have rowAE :=
      BoundedContinuousFunction.coeFn_toLp
        (2 : ℝ≥0∞)
        (commonTimeMeasure
          requestedTime) ℂ
        rowPath
    rw [rowSpaceTimeEq] at rowAE
    exact rowAE.symm
  have nonlinearRefinedTendsto :
      Tendsto
        (fun index =>
          wholeNonlinearRowSpaceTimePath
            requestedTime
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
            requestedTime
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
          Icc (0 : ℝ) requestedTime,
        rowPath time =
          fixedWaveHeatDuhamelValue
            requestedTime
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
              requestedTime
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                requestedTime
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
              requestedTime
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              nonlinearLimit time)) :=
      tendsto_fixedWaveHeatDuhamelValue
        requestedTime
        ν.coeff ν.coeff_pos.le wave time
        (fun _index =>
          commonTimeReplayInitialState lineage wave)
        (fun index =>
          wholeNonlinearRowSpaceTimePath
            requestedTime
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
              requestedTime
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                requestedTime
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
          simpa only [requestedTimeReplayCriticalPath_support] using
            generatedRequestedTimeReplayWave_eventually_mem_comp_strictMono
              replay (receipt.subsequence ∘ refinement)
              (receipt.subsequence_strictMono.comp
                refinementStrictMono)
              wave waveGenerated
        filter_upwards [retainedEventually] with index waveMem
        change
          observedRowMap
              (observedSequence (refinement index)) time =
            fixedWaveHeatDuhamelValue
              requestedTime
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                requestedTime
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
            requestedTime
            (requestedTimePos)
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
              requestedTime
              ν.coeff wave
              (commonTimeReplayInitialState lineage wave)
              (wholeNonlinearRowSpaceTimePath
                requestedTime
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
                  requestedTime,
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
            requestedTimeResidual_eq_zero_of_never_generated
              replay wave waveNonzero waveGenerated
              (receipt.subsequence (refinement index))
              actual actualMem
        have actual :=
          finiteSupportWave_eq_fixedWaveHeatDuhamelValue_of_wholeResidual_zero
            stage.modes wave ν.coeff
            requestedTime
            (requestedTimePos)
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildClosure
end NavierStokes
end SaturationMonoid

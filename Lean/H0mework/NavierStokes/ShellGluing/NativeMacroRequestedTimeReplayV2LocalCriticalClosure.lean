import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalWeakClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalBudget
import H0mework.NavierStokes.ShellSources.PointwiseMassLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin

/-!
# Requested-time critical whole-carrier closure

The requested-time weak closure already carries the actual source-generated
Galerkin sequence, its strong whole-space-time limit, and every punctured
weak Fourier law.  This module transports the remaining critical analytic
responsibility along that exact sequence:

* a transverse whole-space-time limit;
* the actual quadratic nonlinear row of the same limit;
* cutoff-free `L²_t H¹_x` gradient summability and mass;
* the almost-everywhere whole coefficient-mass ceiling.

The requested interval, trajectories, compactness subsequence, limit, and
bounds are generated internally.  No critical-margin certificate, coverage
family, cutoff, target path, or continuation witness enters the public
constructor.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalCriticalClosure

open scoped BigOperators ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientFinitePhysicalStateGeneratedCriticalPath
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPointwiseMassLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
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
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWeakClosure

noncomputable section

/--
Every actual V2 stage pays the source-owned local gradient bound on the
same unconditional physical trajectory.
-/
theorem GeneratedRequestedTimeReplayStage.localReplayV2_gradientDensity_finsetSum_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage :
      GeneratedRequestedTimeReplayStage lineage
        (sourceOwnedLocalReplayV2Duration lineage))
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity
          (sourceOwnedLocalReplayV2Duration lineage)
          (wholeTrajectorySpaceTimePath
            (sourceOwnedLocalReplayV2Duration lineage) stage.trajectory
            (HasDerivAt.continuousOn
              (fun time timeMem =>
                (stage.physical time timeMem).1)))
          wave) ≤
      sourceOwnedLocalReplayV2GradientCeiling lineage := by
  exact
    (wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
      (sourceOwnedLocalReplayV2Duration lineage)
      (sourceOwnedLocalReplayV2Duration_pos lineage)
      stage.modes waves ν.coeff stage.trajectory
      (fun time timeMem =>
        (stage.physical time timeMem).1)
      (fun time timeMem =>
        (stage.physical time timeMem).2.1)).trans
      (requestedTimeReplayV2Stage_uniformLocalCompactnessBudget stage).2.1

/-- The exact Euclidean Fourier mass of every actual local V2 stage is
bounded by the same source-generated coefficient ceiling. -/
theorem GeneratedRequestedTimeReplayStage.localReplayV2_euclideanMass_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    (stage :
      GeneratedRequestedTimeReplayStage lineage
        (sourceOwnedLocalReplayV2Duration lineage))
    (time : Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)) :
    wholeVorticityEuclideanMass (stage.trajectory time.1) ≤
      sourceOwnedLocalReplayV2EnstrophyCeiling lineage := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    stage.modes (stage.trajectory time.1)
    (stage.physical time.1 time.2).2.1]
  exact
    (requestedTimeReplayV2Stage_uniformLocalCompactnessBudget stage).1
      time.1 time.2

/--
The infinite requested-time replay closes on one transverse weak state with
its cutoff-free gradient and coefficient-mass budgets.
-/
structure GeneratedLocalReplayV2CriticalClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) where
  weakClosure :
    GeneratedLocalReplayV2WeakClosure replay
  transverseLimit :
    TransverseSpaceTimeState (sourceOwnedLocalReplayV2Duration lineage)
  inclusion_eq :
    transverseSpaceTimeInclusion
        (sourceOwnedLocalReplayV2Duration lineage) transverseLimit =
      weakClosure.stateLimit
  transverse_tendsto :
    Tendsto
      (fun index =>
        wholeTransverseTrajectorySpaceTimePath
          (sourceOwnedLocalReplayV2Duration lineage)
          (replay.current
            (weakClosure.subsequence index)).trajectory
          (fun time timeMem =>
            (((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).1).continuousAt.continuousWithinAt)
          (fun time timeMem =>
            ((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).2.2.1))
      atTop (𝓝 transverseLimit)
  weak_action :
    ∀ wave : IntegerWavevector, wave ≠ 0 →
      ∀ (test testDerivative : ℝ → ℂ),
        ∀ (testHasDeriv :
            ∀ time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
              HasDerivAt test (testDerivative time) time)
          (testDerivativeContinuous :
            ContinuousOn testDerivative
              (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)))
          (_testZero : test 0 = 0)
          (_testTerminalZero :
            test (sourceOwnedLocalReplayV2Duration lineage) = 0),
        fixedWaveWeakAction
            (sourceOwnedLocalReplayV2Duration lineage) ν.coeff wave
            (restrictedScalarL2
              (sourceOwnedLocalReplayV2Duration lineage) test
              (fun time timeMem =>
                (testHasDeriv
                  time timeMem).continuousAt.continuousWithinAt))
            (restrictedScalarL2
              (sourceOwnedLocalReplayV2Duration lineage) testDerivative
              testDerivativeContinuous)
            (restrictedScalarLInf
              (sourceOwnedLocalReplayV2Duration lineage) test
              (fun time timeMem =>
                (testHasDeriv
                  time timeMem).continuousAt.continuousWithinAt))
            weakClosure.stateLimit
            (transverseSpaceTimeNonlinearRow
              transverseLimit wave) =
          0
  gradient_summable :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          (sourceOwnedLocalReplayV2Duration lineage) weakClosure.stateLimit wave)
  gradient_mass_le :
    wholeSpaceTimeVorticityGradientMass
        (sourceOwnedLocalReplayV2Duration lineage) weakClosure.stateLimit ≤
      sourceOwnedLocalReplayV2GradientCeiling lineage
  coefficientMass_ae_le :
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      wholeVorticityEuclideanMass
          (weakClosure.stateLimit time) ≤
        sourceOwnedLocalReplayV2EnstrophyCeiling lineage

/--
Generate the critical whole-carrier closure directly from the actual
requested-time infinite replay.
-/
noncomputable def generatedLocalReplayV2CriticalClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < (sourceOwnedLocalReplayV2Duration lineage)}
    (replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos) :
    GeneratedLocalReplayV2CriticalClosure replay := by
  let weakClosure :=
    generatedLocalReplayV2WeakClosure replay
  let stateSequence :
      ℕ → SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
    fun index =>
      wholeTrajectorySpaceTimePath
        (sourceOwnedLocalReplayV2Duration lineage)
        (replay.current
          (weakClosure.subsequence index)).trajectory
        (HasDerivAt.continuousOn
          (fun time timeMem =>
            ((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).1))
  let transverseStates :
      ℕ → TransverseSpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        (sourceOwnedLocalReplayV2Duration lineage)
        (replay.current
          (weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current
            (weakClosure.subsequence index)).physical
              time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current
            (weakClosure.subsequence index)).physical
              time timeMem).2.2.1)
  have stateTendsto :
      Tendsto stateSequence atTop
        (𝓝 weakClosure.stateLimit) := by
    have pathEq :
        stateSequence =
          (fun index =>
            localReplayV2SpaceTimePath replay
              (weakClosure.subsequence index)) := by
      funext index
      exact
        (localReplayV2SpaceTimePath_eq_wholeTrajectory
          replay (weakClosure.subsequence index)).symm
    rw [pathEq]
    exact weakClosure.state_tendsto
  have includedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion
            (sourceOwnedLocalReplayV2Duration lineage) (transverseStates index))
        atTop (𝓝 weakClosure.stateLimit) := by
    apply stateTendsto.congr
    intro index
    exact (transverseSpaceTimeInclusion_wholeTransverseTrajectory
      (sourceOwnedLocalReplayV2Duration lineage)
      (replay.current (weakClosure.subsequence index)).trajectory
      (fun time timeMem =>
        (((replay.current (weakClosure.subsequence index)).physical
          time timeMem).1).continuousAt.continuousWithinAt)
      (fun time timeMem =>
        ((replay.current (weakClosure.subsequence index)).physical
          time timeMem).2.2.1)).symm
  let transverseLimitResult :=
    transverseSpaceTime_limit_of_inclusion_tendsto
      (sourceOwnedLocalReplayV2Duration lineage) transverseStates
      weakClosure.stateLimit includedTendsto
  let transverseLimit :
      TransverseSpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
    Classical.choose transverseLimitResult
  have transverseLimitSpec :=
    Classical.choose_spec transverseLimitResult
  have transverseTendsto := transverseLimitSpec.1
  have inclusionEq := transverseLimitSpec.2
  have finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            (sourceOwnedLocalReplayV2Duration lineage) (stateSequence index) wave) ≤
          sourceOwnedLocalReplayV2GradientCeiling lineage := by
    intro index waves
    simpa only [stateSequence] using
      GeneratedRequestedTimeReplayStage.localReplayV2_gradientDensity_finsetSum_le
        (replay.current
          (weakClosure.subsequence index))
        waves
  have gradientSummable :
      Summable
        (fun wave : IntegerWavevector =>
          wholeSpaceTimeVorticityGradientDensity
            (sourceOwnedLocalReplayV2Duration lineage) weakClosure.stateLimit wave) :=
    summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
      (sourceOwnedLocalReplayV2Duration lineage) stateSequence weakClosure.stateLimit
      stateTendsto
      (sourceOwnedLocalReplayV2GradientCeiling lineage)
      finiteSumBound
  have gradientMassLe :
      wholeSpaceTimeVorticityGradientMass
          (sourceOwnedLocalReplayV2Duration lineage) weakClosure.stateLimit ≤
        sourceOwnedLocalReplayV2GradientCeiling lineage :=
    wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
      (sourceOwnedLocalReplayV2Duration lineage) stateSequence weakClosure.stateLimit
      stateTendsto
      (sourceOwnedLocalReplayV2GradientCeiling lineage)
      finiteSumBound
  have weakAction :
      ∀ wave : IntegerWavevector, wave ≠ 0 →
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈ Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage),
                HasDerivAt test
                  (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) (sourceOwnedLocalReplayV2Duration lineage)))
            (testZero : test 0 = 0)
            (testTerminalZero :
              test (sourceOwnedLocalReplayV2Duration lineage) = 0),
          fixedWaveWeakAction
              (sourceOwnedLocalReplayV2Duration lineage) ν.coeff wave
              (restrictedScalarL2
                (sourceOwnedLocalReplayV2Duration lineage) test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                (sourceOwnedLocalReplayV2Duration lineage) testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                (sourceOwnedLocalReplayV2Duration lineage) test
                (fun time timeMem =>
                  (testHasDeriv
                    time timeMem).continuousAt.continuousWithinAt))
              weakClosure.stateLimit
              (transverseSpaceTimeNonlinearRow
                transverseLimit wave) =
            0 := by
    intro wave waveNonzero test testDerivative
      testHasDeriv testDerivativeContinuous
      testZero testTerminalZero
    rcases
        weakClosure.puncturedRow_weak wave waveNonzero with
      ⟨nonlinearLimit, nonlinearTendsto, allTests⟩
    have transverseRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop (𝓝 nonlinearLimit) := by
      apply nonlinearTendsto.congr
      intro index
      exact (transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
        (sourceOwnedLocalReplayV2Duration lineage)
        (replay.current (weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current (weakClosure.subsequence index)).physical
            time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current (weakClosure.subsequence index)).physical
            time timeMem).2.2.1)
        wave).symm
    have generatedRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop
          (𝓝
            (transverseSpaceTimeNonlinearRow
              transverseLimit wave)) :=
      tendsto_transverseSpaceTimeNonlinearRow
        transverseStates transverseLimit
        transverseTendsto wave
    have nonlinearEq :
        nonlinearLimit =
          transverseSpaceTimeNonlinearRow
            transverseLimit wave :=
      tendsto_nhds_unique transverseRowTendsto
        generatedRowTendsto
    simpa only [nonlinearEq] using
      allTests test testDerivative testHasDeriv
        testDerivativeContinuous testZero
        testTerminalZero
  have coefficientMassAE :
      ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
        wholeVorticityEuclideanMass
            (weakClosure.stateLimit time) ≤
          sourceOwnedLocalReplayV2EnstrophyCeiling lineage := by
    obtain
        ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
          pointwiseTendsto⟩ :=
      (tendstoInMeasure_of_tendsto_Lp
        stateTendsto).exists_seq_tendsto_ae
    have approximantBounds :
        ∀ index : ℕ,
          ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
            wholeVorticityEuclideanMass
                (stateSequence
                  (pointwiseSubsequence index) time) ≤
              sourceOwnedLocalReplayV2EnstrophyCeiling lineage := by
      intro index
      let stage := replay.current
        (weakClosure.subsequence (pointwiseSubsequence index))
      have coeFnEq :=
        BoundedContinuousFunction.coeFn_toLp
          (p := (2 : ℝ≥0∞))
          (μ := commonTimeMeasure
            (sourceOwnedLocalReplayV2Duration lineage))
          ℂ
          (wholeTrajectoryBoundedPath
            (sourceOwnedLocalReplayV2Duration lineage)
            stage.trajectory
            (HasDerivAt.continuousOn fun time timeMem =>
              (stage.physical time timeMem).1))
      filter_upwards [coeFnEq] with time timeEq
      change
        wholeVorticityEuclideanMass
            (((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure
                (sourceOwnedLocalReplayV2Duration lineage)) ℂ)
              (wholeTrajectoryBoundedPath
                (sourceOwnedLocalReplayV2Duration lineage)
                stage.trajectory
                (HasDerivAt.continuousOn fun actual actualMem =>
                  (stage.physical actual actualMem).1))) time) ≤
          sourceOwnedLocalReplayV2EnstrophyCeiling lineage
      rw [timeEq]
      exact
        GeneratedRequestedTimeReplayStage.localReplayV2_euclideanMass_le
          stage time
    have allApproximantBounds :
        ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
          ∀ index : ℕ,
            wholeVorticityEuclideanMass
                (stateSequence
                  (pointwiseSubsequence index) time) ≤
              sourceOwnedLocalReplayV2EnstrophyCeiling lineage :=
      eventually_countable_forall.2 approximantBounds
    filter_upwards
        [pointwiseTendsto, allApproximantBounds] with
        time timeTendsto timeBounds
    apply le_of_tendsto
      (tendsto_wholeVorticityEuclideanMass
        timeTendsto)
    exact Filter.Eventually.of_forall timeBounds
  exact
    { weakClosure := weakClosure
      transverseLimit := transverseLimit
      inclusion_eq := inclusionEq
      transverse_tendsto := by
        simpa only [transverseStates] using
          transverseTendsto
      weak_action := weakAction
      gradient_summable := gradientSummable
      gradient_mass_le := gradientMassLe
      coefficientMass_ae_le := coefficientMassAE }

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalCriticalClosure
end NavierStokes
end SaturationMonoid

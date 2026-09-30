import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWeakClosure
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayCriticalClosure

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
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure.GeneratedRequestedTimeReplayStage

noncomputable section

private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by
  norm_num

/-- The source-generated gradient ceiling, independent of requested horizon. -/
def requestedTimeReplayGradientCeiling
    (ν : Viscosity) : ℝ :=
  ((1 / 2 : ℝ) *
      criticalCoefficientEnstrophyCeiling ν (1 / 2 : ℝ)) /
    criticalEnstrophyAbsorptionCoefficient (1 / 2 : ℝ) ν

/--
Every actual requested-time stage pays the same finite-wave gradient bound.
The estimate is attached to the stage's actual unforced trajectory.
-/
theorem GeneratedRequestedTimeReplayStage.gradientDensity_finsetSum_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {requestedTime : ℝ}
    (stage :
      GeneratedRequestedTimeReplayStage lineage requestedTime)
    (initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0)
    (requestedTimePos : 0 < requestedTime)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity
          requestedTime
          (wholeTrajectorySpaceTimePath
            requestedTime stage.trajectory
            (HasDerivAt.continuousOn
              (fun time timeMem =>
                (stage.physical time timeMem).1)))
          wave) ≤
      requestedTimeReplayGradientCeiling ν := by
  let path := toCriticalScalePath stage initialSubcritical
  have initialCoefficientLe :
      finiteStateVorticityCoefficientEnstrophy
          stage.modes (stage.trajectory 0) ≤
        criticalCoefficientEnstrophyCeiling
          ν (1 / 2 : ℝ) := by
    have generated := path.initialEnstrophy_le_ceiling
    have supportEq :=
      toCriticalScalePath_support
        stage initialSubcritical
    have initialEq :=
      toCriticalScalePath_initialState
        stage initialSubcritical
    dsimp [path] at generated
    rw [supportEq] at initialEq
    rw [supportEq, initialEq] at generated
    rw [stage.initial]
    exact generated
  have initialHalfLe :
      finiteStateVorticityHalfEnstrophy
          stage.modes (stage.trajectory 0) ≤
        (1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling
            ν (1 / 2 : ℝ) := by
    unfold finiteStateVorticityHalfEnstrophy
    exact
      mul_le_mul_of_nonneg_left
        initialCoefficientLe (by norm_num)
  have initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            stage.modes (stage.trajectory 0) ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 *
          (2 * Real.pi) ^ 2 := by
    simpa only [stage.initial] using
      GeneratedRequestedTimeReplayStage.requestedInitial_halfCritical
        stage initialSubcritical
  obtain
      ⟨_criticalBarrier, enstrophyAbsorption,
        _serrinAbsorption, _serrinBound⟩ :=
    finiteStateVorticity_criticalSerrinBudget_on_Icc
      stage.modes stage.waveNeg_mem ν (1 / 2 : ℝ)
      half_lt_one stage.trajectory 0 requestedTime
      requestedTimePos.le
      (fun time timeMem =>
        (stage.physical time timeMem).1)
      (fun time timeMem =>
        (stage.physical time timeMem).2.2.2)
      (fun time timeMem wave _waveMem =>
        (stage.physical time timeMem).2.2.1 wave)
      initialMargin
  have absorptionBound :
      criticalEnstrophyAbsorptionCoefficient
            (1 / 2 : ℝ) ν *
          (∫ time in (0 : ℝ)..requestedTime,
            finiteStateVorticityEnstrophyMass
              stage.modes (stage.trajectory time)) ≤
        (1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling
            ν (1 / 2 : ℝ) := by
    calc
      criticalEnstrophyAbsorptionCoefficient
            (1 / 2 : ℝ) ν *
          (∫ time in (0 : ℝ)..requestedTime,
            finiteStateVorticityEnstrophyMass
              stage.modes (stage.trajectory time)) ≤
          finiteStateVorticityHalfEnstrophy
              stage.modes (stage.trajectory 0) -
            finiteStateVorticityHalfEnstrophy
              stage.modes
              (stage.trajectory requestedTime) :=
        enstrophyAbsorption
      _ ≤
          finiteStateVorticityHalfEnstrophy
            stage.modes (stage.trajectory 0) := by
        linarith [
          finiteStateVorticityHalfEnstrophy_nonneg
            stage.modes (stage.trajectory requestedTime)]
      _ ≤
          (1 / 2 : ℝ) *
            criticalCoefficientEnstrophyCeiling
              ν (1 / 2 : ℝ) :=
        initialHalfLe
  have enstrophyIntegralLe :
      (∫ time in (0 : ℝ)..requestedTime,
        finiteStateVorticityEnstrophyMass
          stage.modes (stage.trajectory time)) ≤
        requestedTimeReplayGradientCeiling ν := by
    unfold requestedTimeReplayGradientCeiling
    exact
      (le_div_iff₀
        (criticalEnstrophyAbsorptionCoefficient_pos
          (1 / 2 : ℝ) half_lt_one ν)).2 (by
            simpa only [mul_comm] using absorptionBound)
  exact
    (wholeTrajectory_gradientDensity_finsetSum_le_enstrophyIntegral
      requestedTime requestedTimePos
      stage.modes waves ν.coeff stage.trajectory
      (fun time timeMem =>
        (stage.physical time timeMem).1)
      (fun time timeMem =>
        (stage.physical time timeMem).2.1)).trans
      enstrophyIntegralLe

/--
The infinite requested-time replay closes on one transverse weak state with
its cutoff-free gradient and coefficient-mass budgets.
-/
structure GeneratedRequestedTimeReplayCriticalClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) where
  weakClosure :
    GeneratedRequestedTimeReplayWeakClosure replay
  transverseLimit :
    TransverseSpaceTimeState requestedTime
  inclusion_eq :
    transverseSpaceTimeInclusion
        requestedTime transverseLimit =
      weakClosure.stateLimit
  transverse_tendsto :
    Tendsto
      (fun index =>
        wholeTransverseTrajectorySpaceTimePath
          requestedTime
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
            ∀ time ∈ Icc (0 : ℝ) requestedTime,
              HasDerivAt test (testDerivative time) time)
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
            weakClosure.stateLimit
            (transverseSpaceTimeNonlinearRow
              transverseLimit wave) =
          0
  gradient_summable :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime weakClosure.stateLimit wave)
  gradient_mass_le :
    wholeSpaceTimeVorticityGradientMass
        requestedTime weakClosure.stateLimit ≤
      requestedTimeReplayGradientCeiling ν
  coefficientMass_ae_le :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          (weakClosure.stateLimit time) ≤
        criticalCoefficientEnstrophyCeiling
          ν (1 / 2 : ℝ)

/--
Generate the critical whole-carrier closure directly from the actual
requested-time infinite replay.
-/
noncomputable def generatedRequestedTimeReplayCriticalClosure
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    (replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos) :
    GeneratedRequestedTimeReplayCriticalClosure replay := by
  let weakClosure :=
    generatedRequestedTimeReplayWeakClosure replay
  let stateSequence :
      ℕ → SpaceTimeState requestedTime :=
    fun index =>
      wholeTrajectorySpaceTimePath
        requestedTime
        (replay.current
          (weakClosure.subsequence index)).trajectory
        (HasDerivAt.continuousOn
          (fun time timeMem =>
            ((replay.current
              (weakClosure.subsequence index)).physical
                time timeMem).1))
  let transverseStates :
      ℕ → TransverseSpaceTimeState requestedTime :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        requestedTime
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
    simpa only [stateSequence] using
      weakClosure.state_tendsto
  have includedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion
            requestedTime (transverseStates index))
        atTop (𝓝 weakClosure.stateLimit) := by
    apply stateTendsto.congr
    intro index
    exact (transverseSpaceTimeInclusion_wholeTransverseTrajectory
      requestedTime
      (replay.current (weakClosure.subsequence index)).trajectory
      (fun time timeMem =>
        (((replay.current (weakClosure.subsequence index)).physical
          time timeMem).1).continuousAt.continuousWithinAt)
      (fun time timeMem =>
        ((replay.current (weakClosure.subsequence index)).physical
          time timeMem).2.2.1)).symm
  let transverseLimitResult :=
    transverseSpaceTime_limit_of_inclusion_tendsto
      requestedTime transverseStates
      weakClosure.stateLimit includedTendsto
  let transverseLimit :
      TransverseSpaceTimeState requestedTime :=
    Classical.choose transverseLimitResult
  have transverseLimitSpec :=
    Classical.choose_spec transverseLimitResult
  have transverseTendsto := transverseLimitSpec.1
  have inclusionEq := transverseLimitSpec.2
  have finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity
            requestedTime (stateSequence index) wave) ≤
          requestedTimeReplayGradientCeiling ν := by
    intro index waves
    simpa only [stateSequence] using
      GeneratedRequestedTimeReplayStage.gradientDensity_finsetSum_le
        (replay.current
          (weakClosure.subsequence index))
        initialSubcritical requestedTimePos waves
  have gradientSummable :
      Summable
        (fun wave : IntegerWavevector =>
          wholeSpaceTimeVorticityGradientDensity
            requestedTime weakClosure.stateLimit wave) :=
    summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
      requestedTime stateSequence weakClosure.stateLimit
      stateTendsto
      (requestedTimeReplayGradientCeiling ν)
      finiteSumBound
  have gradientMassLe :
      wholeSpaceTimeVorticityGradientMass
          requestedTime weakClosure.stateLimit ≤
        requestedTimeReplayGradientCeiling ν :=
    wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
      requestedTime stateSequence weakClosure.stateLimit
      stateTendsto
      (requestedTimeReplayGradientCeiling ν)
      finiteSumBound
  have weakAction :
      ∀ wave : IntegerWavevector, wave ≠ 0 →
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
        requestedTime
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
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        wholeVorticityEuclideanMass
            (weakClosure.stateLimit time) ≤
          criticalCoefficientEnstrophyCeiling
            ν (1 / 2 : ℝ) := by
    obtain
        ⟨pointwiseSubsequence, _pointwiseSubsequenceMono,
          pointwiseTendsto⟩ :=
      (tendstoInMeasure_of_tendsto_Lp
        stateTendsto).exists_seq_tendsto_ae
    have approximantBounds :
        ∀ index : ℕ,
          ∀ᵐ time ∂(commonTimeMeasure requestedTime),
            wholeVorticityEuclideanMass
                (stateSequence
                  (pointwiseSubsequence index) time) ≤
              criticalCoefficientEnstrophyCeiling
                ν (1 / 2 : ℝ) := by
      intro index
      have generated :=
        generatedCriticalSpaceTimePath_euclideanMass_ae_le_ceiling
          half_lt_one requestedTimePos
          (requestedTimeReplayCriticalPath replay
            (weakClosure.subsequence
              (pointwiseSubsequence index)))
      simpa only [stateSequence,
        requestedTimeReplayCriticalPath,
        criticalSpaceTimePath_eq_replayTrajectory]
        using generated
    have allApproximantBounds :
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          ∀ index : ℕ,
            wholeVorticityEuclideanMass
                (stateSequence
                  (pointwiseSubsequence index) time) ≤
              criticalCoefficientEnstrophyCeiling
                ν (1 / 2 : ℝ) :=
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayCriticalClosure
end NavierStokes
end SaturationMonoid

import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayMildClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayCriticalClosure
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeNonlinearNegativeOne

/-!
# Requested-time nonlinear negative-one forcing

The requested-time critical closure already generates one transverse
whole-space-time limit with finite gradient mass and an almost-everywhere
coefficient-mass ceiling.  The domain-generic negative-one construction
therefore turns its actual quadratic nonlinearity into an
`L²_t H⁻¹_x` forcing.

For every nonzero Fourier row, unweighting this forcing recovers the same
transverse nonlinear row selected by the requested-time mild closure.
No forcing, integrability, coverage, target path, or continuation
certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildForcing

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRedirectRuntime.GeneratedRedirectedCompleteRoundInfiniteLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCriticalLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeResidualCommonTimeReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayCriticalClosure

noncomputable section

/--
The transverse realization of the requested-time limit retains the
source-generated whole gradient summability.
-/
theorem requestedReplayTransverseGradient_summable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime
          (transverseSpaceTimeInclusion
            requestedTime closure.transverseLimit)
          wave) := by
  simpa only [closure.inclusion_eq] using
    closure.gradient_summable

/--
The transverse realization carries the same almost-everywhere coefficient
mass ceiling as the strong whole-state limit.
-/
theorem requestedReplayTransverseCoefficientMass_ae_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeVorticityEuclideanMass
          ((closure.transverseLimit time).1) ≤
        criticalCoefficientEnstrophyCeiling
          ν (1 / 2 : ℝ) := by
  have includedEq :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        transverseSpaceTimeInclusion
            requestedTime closure.transverseLimit time =
          closure.weakClosure.stateLimit time := by
    rw [closure.inclusion_eq]
    exact Filter.Eventually.of_forall fun _ => rfl
  filter_upwards [
    closure.coefficientMass_ae_le,
    transverseSpaceTimeInclusion_coeFn
      requestedTime closure.transverseLimit,
    includedEq] with
      time massLe transverseEq stateEq
  rw [← stateEq, transverseEq] at massLe
  exact massLe

/--
The actual inverse-Laplacian weighted quadratic forcing generated by the
same requested-time transverse limit.
-/
def negativeOneForcing
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay) :
    SpaceTimeState requestedTime :=
  wholeSpaceTimeNonlinearNegativeOneState
    closure.transverseLimit
    (requestedReplayTransverseGradient_summable closure)
    (criticalCoefficientEnstrophyCeiling_nonneg
      ν (1 / 2 : ℝ))
    (requestedReplayTransverseCoefficientMass_ae_le closure)

/--
Every nonzero unweighted row of the generated `H⁻¹` forcing is exactly the
transverse nonlinear row used by the requested-time mild equation.
-/
theorem negativeOneForcing_unweighted_row_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
          (negativeOneForcing closure time) wave =
        transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave time := by
  exact
    wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae
      closure.transverseLimit
      (requestedReplayTransverseGradient_summable closure)
      (criticalCoefficientEnstrophyCeiling_nonneg
        ν (1 / 2 : ℝ))
      (requestedReplayTransverseCoefficientMass_ae_le closure)
      wave waveNonzero

/--
The mild datum generated from the weak closure can be chosen on the exact
nonlinear row recovered from `negativeOneForcing`.  This is the row bridge
needed by the later whole-mild assembly.
-/
theorem exists_fixedWaveContinuousMildData
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {initialSubcritical :
      ¬ lineageHalfCriticalCrossing lineage 0}
    {requestedTime : ℝ}
    {requestedTimePos : 0 < requestedTime}
    {replay :
      GeneratedRequestedTimeReplayInfiniteLineage
        lineage initialSubcritical requestedTime requestedTimePos}
    (closure :
      GeneratedRequestedTimeReplayCriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    Nonempty
      (FixedWaveContinuousMildData
        requestedTime ν.coeff wave
        (fun _index =>
          commonTimeReplayInitialState lineage)
        closure.weakClosure.stateLimit
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)) := by
  rcases
      GeneratedRequestedTimeReplayWeakClosure.exists_fixedWaveContinuousMildData
        closure.weakClosure wave waveNonzero with
    ⟨nonlinearLimit, ⟨nonlinearTendsto, _weakIdentity⟩,
      mildData⟩
  let transverseStates :
      ℕ → TransverseSpaceTimeState requestedTime :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        requestedTime
        (replay.current
          (closure.weakClosure.subsequence index)).trajectory
        (fun time timeMem =>
          (((replay.current
            (closure.weakClosure.subsequence index)).physical
              time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          ((replay.current
            (closure.weakClosure.subsequence index)).physical
              time timeMem).2.2.1)
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
      (replay.current
        (closure.weakClosure.subsequence index)).trajectory
      (fun time timeMem =>
        (((replay.current
          (closure.weakClosure.subsequence index)).physical
            time timeMem).1).continuousAt.continuousWithinAt)
      (fun time timeMem =>
        ((replay.current
          (closure.weakClosure.subsequence index)).physical
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
            closure.transverseLimit wave)) :=
    tendsto_transverseSpaceTimeNonlinearRow
      transverseStates closure.transverseLimit
      closure.transverse_tendsto wave
  have nonlinearEq :
      nonlinearLimit =
        transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave :=
    tendsto_nhds_unique transverseRowTendsto
      generatedRowTendsto
  simpa only [nonlinearEq] using mildData

end

end
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayMildForcing
end NavierStokes
end SaturationMonoid

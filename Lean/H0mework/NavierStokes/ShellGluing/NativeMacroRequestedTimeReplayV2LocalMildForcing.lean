import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalMildClosure
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayV2LocalCriticalClosure
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildForcing

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
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Source
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2Runtime
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalCriticalClosure

noncomputable section

/--
The transverse realization of the requested-time limit retains the
source-generated whole gradient summability.
-/
theorem localReplayV2TransverseGradient_summable
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          (sourceOwnedLocalReplayV2Duration lineage)
          (transverseSpaceTimeInclusion
            (sourceOwnedLocalReplayV2Duration lineage) closure.transverseLimit)
          wave) := by
  simpa only [closure.inclusion_eq] using
    closure.gradient_summable

/--
The transverse realization carries the same almost-everywhere coefficient
mass ceiling as the strong whole-state limit.
-/
theorem localReplayV2TransverseCoefficientMass_ae_le
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      wholeVorticityEuclideanMass
          ((closure.transverseLimit time).1) ≤
        sourceOwnedLocalReplayV2EnstrophyCeiling lineage := by
  have includedEq :
      ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
        transverseSpaceTimeInclusion
            (sourceOwnedLocalReplayV2Duration lineage) closure.transverseLimit time =
          closure.weakClosure.stateLimit time := by
    rw [closure.inclusion_eq]
    exact Filter.Eventually.of_forall fun _ => rfl
  filter_upwards [
    closure.coefficientMass_ae_le,
    transverseSpaceTimeInclusion_coeFn
      (sourceOwnedLocalReplayV2Duration lineage) closure.transverseLimit,
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
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay) :
    SpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
  wholeSpaceTimeNonlinearNegativeOneState
    closure.transverseLimit
    (localReplayV2TransverseGradient_summable closure)
    (sourceOwnedLocalEnstrophyCeiling_pos
      (lineageReceiptModes lineage 0)
      (commonTimeReplayInitialState lineage)).le
    (localReplayV2TransverseCoefficientMass_ae_le closure)

/--
Every nonzero unweighted row of the generated `H⁻¹` forcing is exactly the
transverse nonlinear row used by the requested-time mild equation.
-/
theorem negativeOneForcing_unweighted_row_ae
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure (sourceOwnedLocalReplayV2Duration lineage)),
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
          (negativeOneForcing closure time) wave =
        transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave time := by
  exact
    wholeSpaceTimeNonlinearNegativeOneState_unweighted_row_ae
      closure.transverseLimit
      (localReplayV2TransverseGradient_summable closure)
      (sourceOwnedLocalEnstrophyCeiling_pos
        (lineageReceiptModes lineage 0)
        (commonTimeReplayInitialState lineage)).le
      (localReplayV2TransverseCoefficientMass_ae_le closure)
      wave waveNonzero

/--
The mild datum generated from the weak closure can be chosen on the exact
nonlinear row recovered from `negativeOneForcing`.  This is the row bridge
needed by the later whole-mild assembly.
-/
theorem exists_fixedWaveContinuousMildData
    {ν : Viscosity}
    {lineage : GeneratedRedirectedCompleteRoundInfiniteLineage ν}
    {durationPos : 0 < sourceOwnedLocalReplayV2Duration lineage}
    {replay :
      GeneratedRequestedTimeReplayV2InfiniteLineage lineage
        (sourceOwnedLocalReplayV2Duration lineage) durationPos}
    (closure :
      GeneratedLocalReplayV2CriticalClosure replay)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    Nonempty
      (FixedWaveContinuousMildData
        (sourceOwnedLocalReplayV2Duration lineage) ν.coeff wave
        (fun _index =>
          commonTimeReplayInitialState lineage)
        closure.weakClosure.stateLimit
        (transverseSpaceTimeNonlinearRow
          closure.transverseLimit wave)) := by
  rcases
      GeneratedLocalReplayV2WeakClosure.exists_fixedWaveContinuousMildData
        closure.weakClosure wave waveNonzero with
    ⟨nonlinearLimit, ⟨nonlinearTendsto, _weakIdentity⟩,
      mildData⟩
  let transverseStates :
      ℕ → TransverseSpaceTimeState (sourceOwnedLocalReplayV2Duration lineage) :=
    fun index =>
      wholeTransverseTrajectorySpaceTimePath
        (sourceOwnedLocalReplayV2Duration lineage)
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
      (sourceOwnedLocalReplayV2Duration lineage)
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
    ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroRequestedTimeReplayV2LocalMildForcing
end NavierStokes
end SaturationMonoid


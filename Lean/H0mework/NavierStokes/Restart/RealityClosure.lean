import H0mework.NavierStokes.Restart.CriticalClosure

/-!
# Fourier reality of the generated whole restart limit

Every canonical restart stage is an actual real Galerkin trajectory.  Its
strong whole-carrier limit therefore retains the Fourier conjugation law,
first rowwise in time `L²` and then almost everywhere on the transverse
whole state.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartRealityClosure

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-- Every opposite Fourier-row pair of the strong restart limit satisfies
the real-field conjugation law in the time-`L²` carrier. -/
theorem wholeRestartStateLimit_fourierReality
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay)
    (wave : IntegerWavevector) :
    fixedWaveSpaceTimeRestriction
        (wholeRestartDuration contact) (waveNeg wave)
        closure.weakClosure.stateLimit =
      fixedWaveSpaceTimeConjugation
        (wholeRestartDuration contact)
        (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit) := by
  let stage :
      ∀ index : ℕ,
        GeneratedWholeRestartCanonicalStage contact
          (closure.weakClosure.subsequence index) :=
    fun index => replay.current (closure.weakClosure.subsequence index)
  let stageContinuous :
      ∀ index,
        ContinuousOn (stage index).trajectory
          (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    fun index =>
      HasDerivAt.continuousOn fun time timeMem =>
        ((stage index).physical time timeMem).1
  let stagePath : ℕ → SpaceTimeState (wholeRestartDuration contact) :=
    fun index =>
      wholeTrajectorySpaceTimePath (wholeRestartDuration contact)
        (stage index).trajectory (stageContinuous index)
  have approximantReality :
      ∀ index : ℕ,
        fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) (waveNeg wave) (stagePath index) =
          fixedWaveSpaceTimeConjugation
            (wholeRestartDuration contact)
            (fixedWaveSpaceTimeRestriction
              (wholeRestartDuration contact) wave (stagePath index)) := by
    intro index
    apply MeasureTheory.Lp.ext
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) (waveNeg wave) (stagePath index),
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) wave (stagePath index),
      fixedWaveSpaceTimeConjugation_coeFn
        (wholeRestartDuration contact)
        (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave (stagePath index)),
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure (wholeRestartDuration contact)) ℂ
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) (stage index).trajectory
          (stageContinuous index))] with
        time negRowEq rowEq conjugateEq wholeEq
    rw [negRowEq, conjugateEq]
    change
      stagePath index time (waveNeg wave) =
        vectorConj
          ((fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave (stagePath index)) time)
    rw [rowEq]
    change
      stagePath index time (waveNeg wave) =
        vectorConj (stagePath index time wave)
    change
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
        (wholeTrajectoryBoundedPath
          (wholeRestartDuration contact) (stage index).trajectory
          (stageContinuous index))) time (waveNeg wave) =
        vectorConj
          (((BoundedContinuousFunction.toLp 2
            (commonTimeMeasure (wholeRestartDuration contact)) ℂ)
            (wholeTrajectoryBoundedPath
              (wholeRestartDuration contact) (stage index).trajectory
              (stageContinuous index))) time wave)
    rw [wholeEq]
    exact ((stage index).physical time.1 time.2).2.2.2 wave
  have stageTendsto :
      Tendsto stagePath atTop (𝓝 closure.weakClosure.stateLimit) := by
    have pathEq :
        stagePath =
          (fun index =>
            wholeRestartSpaceTimePath replay
              (closure.weakClosure.subsequence index)) := by
      funext index
      exact
        (wholeRestartSpaceTimePath_eq_wholeTrajectory
          replay (closure.weakClosure.subsequence index)).symm
    rw [pathEq]
    exact closure.weakClosure.state_tendsto
  have negativeRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) (waveNeg wave) (stagePath index))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) (waveNeg wave)
          closure.weakClosure.stateLimit)) :=
    (fixedWaveSpaceTimeRestriction
      (wholeRestartDuration contact) (waveNeg wave)).continuous.tendsto
        closure.weakClosure.stateLimit |>.comp stageTendsto
  have positiveRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave (stagePath index))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit)) :=
    (fixedWaveSpaceTimeRestriction
      (wholeRestartDuration contact) wave).continuous.tendsto
        closure.weakClosure.stateLimit |>.comp stageTendsto
  have conjugateRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeConjugation
            (wholeRestartDuration contact)
            (fixedWaveSpaceTimeRestriction
              (wholeRestartDuration contact) wave (stagePath index)))
        atTop
        (𝓝 (fixedWaveSpaceTimeConjugation
          (wholeRestartDuration contact)
          (fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) wave
            closure.weakClosure.stateLimit))) :=
    (fixedWaveSpaceTimeConjugation
      (wholeRestartDuration contact)).continuous.tendsto
        (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit) |>.comp positiveRowTendsto
  exact
    tendsto_nhds_unique negativeRowTendsto <| by
      simpa only [approximantReality] using conjugateRowTendsto

/-- The strong whole-state restart limit is Fourier-real almost everywhere. -/
theorem wholeRestartStateLimit_fourierReality_ae
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      FiniteStateFourierReality
        (closure.weakClosure.stateLimit time) := by
  have realityAE :
      ∀ wave : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
          closure.weakClosure.stateLimit time (waveNeg wave) =
            vectorConj (closure.weakClosure.stateLimit time wave) := by
    intro wave
    have negRowAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) (waveNeg wave)
        closure.weakClosure.stateLimit
    have rowAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        (wholeRestartDuration contact) wave
        closure.weakClosure.stateLimit
    have conjugationAE :=
      fixedWaveSpaceTimeConjugation_coeFn
        (wholeRestartDuration contact)
        (fixedWaveSpaceTimeRestriction
          (wholeRestartDuration contact) wave
          closure.weakClosure.stateLimit)
    filter_upwards [negRowAE, rowAE, conjugationAE] with
        time negRowEq rowEq conjugationEq
    calc
      closure.weakClosure.stateLimit time (waveNeg wave) =
          fixedWaveSpaceTimeRestriction
            (wholeRestartDuration contact) (waveNeg wave)
            closure.weakClosure.stateLimit time := negRowEq.symm
      _ =
          fixedWaveSpaceTimeConjugation
            (wholeRestartDuration contact)
            (fixedWaveSpaceTimeRestriction
              (wholeRestartDuration contact) wave
              closure.weakClosure.stateLimit) time := by
        rw [wholeRestartStateLimit_fourierReality closure wave]
      _ =
          vectorConj
            (fixedWaveSpaceTimeRestriction
              (wholeRestartDuration contact) wave
              closure.weakClosure.stateLimit time) := conjugationEq
      _ = vectorConj (closure.weakClosure.stateLimit time wave) := by
        rw [rowEq]
  exact eventually_countable_forall.2 realityAE

/-- The transverse realization carries the same generated Fourier-reality
law through its faithful whole-state inclusion. -/
theorem wholeRestartTransverseLimit_fourierReality_ae
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    (closure : GeneratedWholeRestartCriticalClosure replay) :
    ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
      FiniteStateFourierReality (closure.transverseLimit time).1 := by
  have inclusionAE :
      ∀ᵐ time ∂(commonTimeMeasure (wholeRestartDuration contact)),
        closure.weakClosure.stateLimit time =
          (closure.transverseLimit time).1 := by
    simpa only [closure.inclusion_eq] using
      transverseSpaceTimeInclusion_coeFn
        (wholeRestartDuration contact) closure.transverseLimit
  filter_upwards [
    inclusionAE,
    wholeRestartStateLimit_fourierReality_ae closure] with
      time inclusionEq timeReality
  intro wave
  rw [← inclusionEq]
  exact timeReality wave

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartRealityClosure
end NavierStokes
end SaturationMonoid

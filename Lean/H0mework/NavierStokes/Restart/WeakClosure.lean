import H0mework.NavierStokes.Restart.StrongCompactness
import H0mework.NavierStokes.ShellGluing.NativeMacroRequestedTimeReplayWeakClosure

/-!
# Whole weak equation from the generated whole restart replay

The canonical punctured cubes exhaust every nonzero integer wave.  Along the
strong whole-carrier subsequence, each fixed nonzero row therefore eventually
belongs to the actual finite Galerkin law surface.  Passing the same native
equation to the strong limit yields the unforced punctured whole weak law.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure

open scoped ENNReal Topology

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartStrongCompactness
open
  ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

@[simp] theorem wholeRestartSpaceTimePath_eq_wholeTrajectory
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact)
    (index : ℕ) :
    wholeRestartSpaceTimePath replay index =
      wholeTrajectorySpaceTimePath
        (wholeRestartDuration contact)
        (replay.current index).trajectory
        (HasDerivAt.continuousOn fun time timeMem =>
          ((replay.current index).physical time timeMem).1) := by
  rfl

theorem wholeRestartWave_eventually_mem_comp_subsequence
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (_replay : GeneratedWholeRestartCanonicalReplay contact)
    (subsequence : ℕ → ℕ)
    (subsequenceMono : StrictMono subsequence)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᶠ index : ℕ in atTop,
      wave ∈ wholeRestartModes (subsequence index) := by
  have eventualRadius :
      ∀ᶠ radius : ℕ in atTop,
        wave ∈ puncturedIntegerWaveFrequencyCube radius :=
    nonzero_integerWave_eventually_mem_puncturedFrequencyCube
      wave waveNonzero
  exact subsequenceMono.tendsto_atTop.eventually eventualRadius

structure GeneratedWholeRestartWeakClosure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) where
  stateLimit : SpaceTimeState (wholeRestartDuration contact)
  stateLimit_mem :
    stateLimit ∈ closure (wholeRestartSpaceTimePathFamily replay)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  state_tendsto :
    Tendsto
      (fun index =>
        wholeRestartSpaceTimePath replay (subsequence index))
      atTop (𝓝 stateLimit)
  puncturedRow_weak :
    ∀ wave : IntegerWavevector,
      wave ≠ 0 →
      ∃ nonlinearLimit :
          NonlinearRowSpaceTimeState (wholeRestartDuration contact),
        Tendsto
            (fun index =>
              wholeNonlinearRowSpaceTimePath
                (wholeRestartDuration contact)
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
                ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
                  HasDerivAt test (testDerivative time) time)
              (testDerivativeContinuous :
                ContinuousOn testDerivative
                  (Icc (0 : ℝ) (wholeRestartDuration contact)))
              (_testZero : test 0 = 0)
              (_testTerminalZero :
                test (wholeRestartDuration contact) = 0),
            fixedWaveWeakAction
                (wholeRestartDuration contact) ν.coeff wave
                (restrictedScalarL2
                  (wholeRestartDuration contact) test
                  (fun time timeMem =>
                    (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                (restrictedScalarL2
                  (wholeRestartDuration contact) testDerivative
                  testDerivativeContinuous)
                (restrictedScalarLInf
                  (wholeRestartDuration contact) test
                  (fun time timeMem =>
                    (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
                stateLimit nonlinearLimit = 0

/-- Generate the punctured whole weak equation directly from the actual
canonical restart replay and its common strong subsequence. -/
noncomputable def generatedWholeRestartWeakClosure
    {ν : Viscosity}
    {Seed : Type}
    [WholeRestartPhysicalSeed ν Seed]
    {contact : Seed}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    GeneratedWholeRestartWeakClosure replay := by
  let strongExists := exists_wholeRestartSpaceTime_strong_subsequence replay
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
    wholeRestartModes (subsequence index)
  let trajectories : ℕ → ℝ → ComplexVorticityHilbertState := fun index =>
    (replay.current (subsequence index)).trajectory
  let trajectoryContinuous :
      ∀ index,
        ContinuousOn (trajectories index)
          (Icc (0 : ℝ) (wholeRestartDuration contact)) :=
    fun index => HasDerivAt.continuousOn fun time timeMem =>
      ((replay.current (subsequence index)).physical time timeMem).1
  have evolves :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (wholeRestartDuration contact) →
          HasDerivAt (trajectories index)
            (finiteStateVorticityGenerator
              (modes index) ν.coeff (trajectories index time)) time := by
    intro index time timeMem
    exact ((replay.current (subsequence index)).physical time timeMem).1
  have supported :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (wholeRestartDuration contact) →
          ∀ output, output ∉ modes index →
            trajectories index time output = 0 := by
    intro index time timeMem output outputNotMem
    exact ((replay.current (subsequence index)).physical
      time timeMem).2.1 output outputNotMem
  have transverse :
      ∀ index time,
        time ∈ Icc (0 : ℝ) (wholeRestartDuration contact) →
          WholeStateTransverse (trajectories index time) := by
    intro index time timeMem output
    exact ((replay.current (subsequence index)).physical
      time timeMem).2.2.1 output
  have waveEventuallyMem :
      ∀ᶠ index : ℕ in atTop, wave ∈ modes index := by
    simpa only [modes] using
      wholeRestartWave_eventually_mem_comp_subsequence
        replay subsequence subsequenceMono wave waveNonzero
  have finiteWeakEventually :
      ∀ᶠ index : ℕ in atTop,
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ time ∈ Icc (0 : ℝ) (wholeRestartDuration contact),
                HasDerivAt test (testDerivative time) time)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) (wholeRestartDuration contact)))
            (testZero : test 0 = 0)
            (testTerminalZero :
              test (wholeRestartDuration contact) = 0),
          fixedWaveWeakAction
              (wholeRestartDuration contact) ν.coeff wave
              (restrictedScalarL2
                (wholeRestartDuration contact) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2
                (wholeRestartDuration contact) testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf
                (wholeRestartDuration contact) test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (wholeTrajectorySpaceTimePath
                (wholeRestartDuration contact)
                (trajectories index) (trajectoryContinuous index))
              (wholeNonlinearRowSpaceTimePath
                (wholeRestartDuration contact)
                (trajectories index) (trajectoryContinuous index)
                (transverse index) wave) = 0 := by
    filter_upwards [waveEventuallyMem] with index waveMem
    intro test testDerivative testHasDeriv
      testDerivativeContinuous testZero testTerminalZero
    simpa [modes, trajectories, trajectoryContinuous] using
      finiteSupportWave_infiniteRow_weak_identity
        (modes index) wave waveMem ν.coeff
        (wholeRestartDuration contact) (wholeRestartDuration_pos contact)
        (trajectories index)
        (fun time timeMem => evolves index time timeMem)
        (fun time timeMem => supported index time timeMem)
        (transverse index)
        test testDerivative testHasDeriv
        testDerivativeContinuous testZero testTerminalZero
  have stateTendstoWhole :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (trajectories index) (trajectoryContinuous index))
        atTop (𝓝 stateLimit) := by
    have pathEq :
        (fun index =>
          wholeTrajectorySpaceTimePath
            (wholeRestartDuration contact)
            (trajectories index) (trajectoryContinuous index)) =
          (fun index =>
            wholeRestartSpaceTimePath replay (subsequence index)) := by
      funext index
      exact
        (wholeRestartSpaceTimePath_eq_wholeTrajectory
          replay (subsequence index)).symm
    rw [pathEq]
    exact stateTendsto
  simpa [trajectories, trajectoryContinuous] using
    fixedWave_weakLimit_all_tests_of_wholeTendsto_of_eventually_weak
      ν.coeff (wholeRestartDuration contact) (wholeRestartDuration_pos contact)
      trajectories trajectoryContinuous transverse
      stateLimit stateTendstoWhole wave finiteWeakEventually

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWeakClosure
end NavierStokes
end SaturationMonoid

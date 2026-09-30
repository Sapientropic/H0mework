import H0mework.NavierStokes.Fourier.PuncturedCanonicalWeakLimit

/-!
# One nonlinear-row weak limit for all time tests

Strong whole-trajectory convergence makes the fixed-wave nonlinear row
Cauchy in `L¹_t`.  Its complete-space limit is therefore determined before
choosing a time test.  This module reorders the resulting quantifiers:
for one fixed wave it generates one nonlinear-row limit, proves convergence
to that limit, and then proves the distributional Fourier identity against
every admissible endpoint-zero `C¹` test.

The proof reuses the existing per-test passage and uniqueness of limits; no
test-dependent nonlinear state, compactness witness, or target solution is
added to the producer mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteModeWeakLimitAllTests

open scoped ENNReal Topology

open Set
open Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalWeakLimit

noncomputable section

/--
A concrete whole-state strong limit generates one fixed nonlinear-row limit
for the selected Fourier wave, and that same row limit satisfies the
distributional equation against every admissible endpoint-zero `C¹` test.
-/
theorem
    finiteModeSequence_fixedWave_weakLimit_all_tests_of_wholeTendsto
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (modes : ℕ → Finset IntegerWavevector)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ index t, t ∈ Icc (0 : ℝ) requestedTime →
        HasDerivAt (trajectories index)
          (finiteStateVorticityGenerator
            (modes index) ν (trajectories index t)) t)
    (supported :
      ∀ index t, t ∈ Icc (0 : ℝ) requestedTime →
        ∀ output : IntegerWavevector,
          output ∉ modes index →
            trajectories index t output = 0)
    (transverse :
      ∀ index t, t ∈ Icc (0 : ℝ) requestedTime →
        WholeStateTransverse (trajectories index t))
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath requestedTime
            (trajectories index)
            (fun t timeMem =>
              (evolves index t timeMem).continuousAt.continuousWithinAt))
        atTop (𝓝 stateLimit))
    (wave : IntegerWavevector)
    (waveEventuallyMem :
      ∀ᶠ index : ℕ in atTop, wave ∈ modes index) :
    ∃ nonlinearLimit :
        NonlinearRowSpaceTimeState requestedTime,
      Tendsto
          (fun index =>
            wholeNonlinearRowSpaceTimePath requestedTime
              (trajectories index)
              (fun t timeMem =>
                (evolves index t timeMem).continuousAt.continuousWithinAt)
              (transverse index) wave)
          atTop (𝓝 nonlinearLimit) ∧
      ∀ (test testDerivative : ℝ → ℂ),
        ∀ (testHasDeriv :
            ∀ t ∈ Icc (0 : ℝ) requestedTime,
              HasDerivAt test (testDerivative t) t)
          (testDerivativeContinuous :
            ContinuousOn testDerivative
              (Icc (0 : ℝ) requestedTime))
          (_testZero : test 0 = 0)
          (_testRequestedTimeZero : test requestedTime = 0),
        fixedWaveWeakAction requestedTime ν wave
            (restrictedScalarL2 requestedTime test
              (fun t timeMem =>
                (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
            (restrictedScalarL2 requestedTime testDerivative
              testDerivativeContinuous)
            (restrictedScalarLInf requestedTime test
              (fun t timeMem =>
                (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
            stateLimit nonlinearLimit =
          0 := by
  let zeroTest : ℝ → ℂ := fun _ => 0
  have zeroHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt zeroTest (zeroTest t) t := by
    intro t tMem
    simpa [zeroTest] using
      (hasDerivAt_const t (0 : ℂ))
  have zeroContinuous :
      ContinuousOn zeroTest (Icc (0 : ℝ) requestedTime) := by
    exact continuous_const.continuousOn
  obtain ⟨nonlinearLimit, nonlinearTendsto, _zeroWeak⟩ :=
    finiteModeSequence_fixedWave_weakLimit_of_wholeTendsto
      ν requestedTime requestedTimePos modes trajectories
      evolves supported transverse stateLimit stateTendsto
      wave waveEventuallyMem zeroTest zeroTest
      zeroHasDeriv zeroContinuous rfl rfl
  refine ⟨nonlinearLimit, nonlinearTendsto, ?_⟩
  intro test testDerivative testHasDeriv
    testDerivativeContinuous testZero testRequestedTimeZero
  obtain
      ⟨otherNonlinearLimit, otherNonlinearTendsto, otherWeak⟩ :=
    finiteModeSequence_fixedWave_weakLimit_of_wholeTendsto
      ν requestedTime requestedTimePos modes trajectories
      evolves supported transverse stateLimit stateTendsto
      wave waveEventuallyMem test testDerivative
      testHasDeriv testDerivativeContinuous
      testZero testRequestedTimeZero
  have otherEq : otherNonlinearLimit = nonlinearLimit :=
    tendsto_nhds_unique otherNonlinearTendsto nonlinearTendsto
  subst otherNonlinearLimit
  exact otherWeak

end

end ThreeDimensionalVorticityCoefficientFiniteModeWeakLimitAllTests
end NavierStokes
end SaturationMonoid

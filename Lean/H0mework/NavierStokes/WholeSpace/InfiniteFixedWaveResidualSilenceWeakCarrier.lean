import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveWeakCarrier
import H0mework.NavierStokes.Fourier.CanonicalExhaustiveGalerkinTarget

/-!
# Fixed-wave weak identity from whole-residual silence

A fixed Fourier row of an actual finite Galerkin trajectory satisfies the
whole weak equation in either of two source-owned ways:

* the row is retained, so the existing retained-row theorem applies;
* the row is omitted, but its complete whole-PDE residual is zero throughout
  the physical interval.  Then both its physical coefficient and its whole
  nonlinear row vanish pointwise, so the same weak action is zero.

This is the consumer needed by complete space-time residual replay.  It does
not accept coverage, eventual membership, a target limit, or a weak-solution
certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier

open scoped ENNReal Topology

open Set
open Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open
  ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier

noncomputable section

/--
An actual finite Galerkin row has zero whole weak action whenever its
whole-PDE residual vanishes throughout the same physical interval.  Retained
and omitted rows are exhausted internally.
-/
theorem finiteSupportWave_infiniteRow_weak_identity_of_wholeResidual_zero
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (supported :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ output : IntegerWavevector,
          output ∉ modes → trajectory t output = 0)
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        WholeStateTransverse (trajectory t))
    (wholeResidualZero :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        wholeLatticeVorticityFourierPDEResidualAt
            ν (trajectory t)
            (finiteStateVorticityGenerator
              modes ν (trajectory t))
            wave =
          0)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    fixedWaveWeakAction requestedTime ν wave
        (restrictedScalarL2 requestedTime test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (restrictedScalarL2 requestedTime testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf requestedTime test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt))
        (wholeNonlinearRowSpaceTimePath requestedTime trajectory
          (fun t timeMem =>
            (evolves t timeMem).continuousAt.continuousWithinAt)
          transverse wave) =
      0 := by
  by_cases waveMem : wave ∈ modes
  · exact
      finiteSupportWave_infiniteRow_weak_identity
        modes wave waveMem ν requestedTime requestedTimePos
        trajectory evolves supported transverse
        test testDerivative testHasDeriv
        testDerivativeContinuous testZero testRequestedTimeZero
  let trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) requestedTime) :=
    fun t timeMem =>
      (evolves t timeMem).continuousAt.continuousWithinAt
  let testContinuous :
      ContinuousOn test (Icc (0 : ℝ) requestedTime) :=
    fun t timeMem =>
      (testHasDeriv t timeMem).continuousAt.continuousWithinAt
  have stateZero :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        trajectory t wave = 0 := by
    intro t timeMem
    exact supported t timeMem wave waveMem
  have nonlinearZero :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        wholeStateVorticityNonlinearCoefficientAt
            (trajectory t) wave =
          0 := by
    intro t timeMem
    have residualZero := wholeResidualZero t timeMem
    have rowZero := stateZero t timeMem
    simpa [wholeLatticeVorticityFourierPDEResidualAt,
      wholeLatticeVorticityFourierTangentAt,
      finiteStateVorticityGenerator_apply,
      waveMem, rowZero] using residualZero
  have derivativeIntegralZero :
      (∫ t in (0 : ℝ)..requestedTime,
          testDerivative t • trajectory t wave) =
        0 := by
    calc
      (∫ t in (0 : ℝ)..requestedTime,
          testDerivative t • trajectory t wave) =
          ∫ _t in (0 : ℝ)..requestedTime,
            (0 : ComplexCoordinateVector) := by
        apply intervalIntegral.integral_congr
        intro t timeMem
        have timeInIcc : t ∈ Icc (0 : ℝ) requestedTime := by
          rwa [uIcc_of_le requestedTimePos.le] at timeMem
        simp [stateZero t timeInIcc]
      _ = 0 := intervalIntegral.integral_zero
  have nonlinearIntegralZero :
      (∫ t in (0 : ℝ)..requestedTime,
          test t •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave) =
        0 := by
    calc
      (∫ t in (0 : ℝ)..requestedTime,
          test t •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave) =
          ∫ _t in (0 : ℝ)..requestedTime,
            (0 : ComplexCoordinateVector) := by
        apply intervalIntegral.integral_congr
        intro t timeMem
        have timeInIcc : t ∈ Icc (0 : ℝ) requestedTime := by
          rwa [uIcc_of_le requestedTimePos.le] at timeMem
        simp [nonlinearZero t timeInIcc]
      _ = 0 := intervalIntegral.integral_zero
  have viscousIntegralZero :
      (∫ t in (0 : ℝ)..requestedTime,
          test t •
            ((ν * integerWaveViscousMultiplier wave) •
              trajectory t wave)) =
        0 := by
    calc
      (∫ t in (0 : ℝ)..requestedTime,
          test t •
            ((ν * integerWaveViscousMultiplier wave) •
              trajectory t wave)) =
          ∫ _t in (0 : ℝ)..requestedTime,
            (0 : ComplexCoordinateVector) := by
        apply intervalIntegral.integral_congr
        intro t timeMem
        have timeInIcc : t ∈ Icc (0 : ℝ) requestedTime := by
          rwa [uIcc_of_le requestedTimePos.le] at timeMem
        simp [stateZero t timeInIcc]
      _ = 0 := intervalIntegral.integral_zero
  change
    fixedWaveWeakAction requestedTime ν wave
        (restrictedScalarL2 requestedTime test testContinuous)
        (restrictedScalarL2 requestedTime testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf requestedTime test testContinuous)
        (wholeTrajectorySpaceTimePath requestedTime trajectory
          trajectoryContinuous)
        (wholeNonlinearRowSpaceTimePath requestedTime trajectory
          trajectoryContinuous transverse wave) =
      0
  unfold fixedWaveWeakAction
  rw [
    fixedL2ScalarL2IntegralCLM_wholeTrajectory_eq_intervalIntegral
      requestedTime requestedTimePos
      testDerivative testDerivativeContinuous
      trajectory trajectoryContinuous wave,
    fixedLInfScalarL1IntegralCLM_wholeNonlinear_eq_intervalIntegral
      requestedTime requestedTimePos test testContinuous
      trajectory trajectoryContinuous transverse wave,
    fixedL2ScalarL2IntegralCLM_viscousWholeTrajectory_eq_intervalIntegral
      requestedTime requestedTimePos test testContinuous
      trajectory trajectoryContinuous wave
      (ν * integerWaveViscousMultiplier wave),
    derivativeIntegralZero,
    nonlinearIntegralZero,
    viscousIntegralZero]
  simp

/--
A strong whole-trajectory limit and an eventually exact fixed-row weak law
generate one nonlinear-row limit valid for every admissible time test.

This is the quantifier order required by source replay: the source first
generates the stagewise weak law (by retained membership or whole-residual
silence), while compactness later selects one subsequence and one nonlinear
row limit.
-/
theorem
    fixedWave_weakLimit_all_tests_of_wholeTendsto_of_eventually_weak
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (trajectoryContinuous :
      ∀ index,
        ContinuousOn (trajectories index)
          (Icc (0 : ℝ) requestedTime))
    (transverse :
      ∀ index t, t ∈ Icc (0 : ℝ) requestedTime →
        WholeStateTransverse (trajectories index t))
    (stateLimit : SpaceTimeState requestedTime)
    (stateTendsto :
      Tendsto
        (fun index =>
          wholeTrajectorySpaceTimePath requestedTime
            (trajectories index)
            (trajectoryContinuous index))
        atTop (𝓝 stateLimit))
    (wave : IntegerWavevector)
    (finiteWeakEventually :
      ∀ᶠ index : ℕ in atTop,
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ t ∈ Icc (0 : ℝ) requestedTime,
                HasDerivAt test (testDerivative t) t)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) requestedTime))
            (_testZero : test 0 = 0)
            (_testRequestedTimeZero :
              test requestedTime = 0),
          fixedWaveWeakAction requestedTime ν wave
              (restrictedScalarL2 requestedTime test
                (fun t timeMem =>
                  (testHasDeriv
                    t timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2 requestedTime testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf requestedTime test
                (fun t timeMem =>
                  (testHasDeriv
                    t timeMem).continuousAt.continuousWithinAt))
              (wholeTrajectorySpaceTimePath requestedTime
                (trajectories index)
                (trajectoryContinuous index))
              (wholeNonlinearRowSpaceTimePath requestedTime
                (trajectories index)
                (trajectoryContinuous index)
                (transverse index) wave) =
            0) :
    ∃ nonlinearLimit :
        NonlinearRowSpaceTimeState requestedTime,
      Tendsto
          (fun index =>
            wholeNonlinearRowSpaceTimePath requestedTime
              (trajectories index)
              (trajectoryContinuous index)
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
          (_testRequestedTimeZero :
            test requestedTime = 0),
        fixedWaveWeakAction requestedTime ν wave
            (restrictedScalarL2 requestedTime test
              (fun t timeMem =>
                (testHasDeriv
                  t timeMem).continuousAt.continuousWithinAt))
            (restrictedScalarL2 requestedTime testDerivative
              testDerivativeContinuous)
            (restrictedScalarLInf requestedTime test
              (fun t timeMem =>
                (testHasDeriv
                  t timeMem).continuousAt.continuousWithinAt))
            stateLimit nonlinearLimit =
          0 := by
  let stateSequence : ℕ → SpaceTimeState requestedTime :=
    fun index =>
      wholeTrajectorySpaceTimePath requestedTime
        (trajectories index) (trajectoryContinuous index)
  let nonlinearSequence :
      ℕ → NonlinearRowSpaceTimeState requestedTime :=
    fun index =>
      wholeNonlinearRowSpaceTimePath requestedTime
        (trajectories index) (trajectoryContinuous index)
        (transverse index) wave
  have stateCauchy : CauchySeq stateSequence := by
    exact (by
      simpa [stateSequence] using stateTendsto.cauchySeq)
  have nonlinearCauchy :
      CauchySeq nonlinearSequence := by
    simpa [nonlinearSequence] using
      wholeNonlinearRowSpaceTimePath_cauchySeq
        requestedTime requestedTimePos trajectories
        trajectoryContinuous transverse wave stateCauchy
  obtain ⟨nonlinearLimit, nonlinearTendsto⟩ :=
    cauchySeq_tendsto_of_complete nonlinearCauchy
  refine ⟨nonlinearLimit, ?_, ?_⟩
  · simpa [nonlinearSequence] using nonlinearTendsto
  · intro test testDerivative testHasDeriv
      testDerivativeContinuous testZero testRequestedTimeZero
    let testContinuous :
        ContinuousOn test (Icc (0 : ℝ) requestedTime) :=
      fun t timeMem =>
        (testHasDeriv t timeMem).continuousAt.continuousWithinAt
    let testL2 :=
      restrictedScalarL2 requestedTime test testContinuous
    let testDerivativeL2 :=
      restrictedScalarL2 requestedTime testDerivative
        testDerivativeContinuous
    let testLInf :=
      restrictedScalarLInf requestedTime test testContinuous
    have actionTendsto :
        Tendsto
          (fun index =>
            fixedWaveWeakAction requestedTime ν wave
              testL2 testDerivativeL2 testLInf
              (stateSequence index)
              (nonlinearSequence index))
          atTop
          (𝓝
            (fixedWaveWeakAction requestedTime ν wave
              testL2 testDerivativeL2 testLInf
              stateLimit nonlinearLimit)) :=
      tendsto_fixedWaveWeakAction
        requestedTime ν wave
        testL2 testDerivativeL2 testLInf
        stateSequence nonlinearSequence
        stateLimit nonlinearLimit
        (by simpa [stateSequence] using stateTendsto)
        nonlinearTendsto
    have actionEventuallyZero :
        ∀ᶠ index : ℕ in atTop,
          fixedWaveWeakAction requestedTime ν wave
              testL2 testDerivativeL2 testLInf
              (stateSequence index)
              (nonlinearSequence index) =
            0 := by
      filter_upwards [finiteWeakEventually] with index rowWeak
      simpa [stateSequence, nonlinearSequence,
        testL2, testDerivativeL2, testLInf,
        testContinuous] using
          rowWeak test testDerivative testHasDeriv
            testDerivativeContinuous testZero
            testRequestedTimeZero
    have actionZeroTendsto :
        Tendsto
          (fun index =>
            fixedWaveWeakAction requestedTime ν wave
              testL2 testDerivativeL2 testLInf
              (stateSequence index)
              (nonlinearSequence index))
          atTop (𝓝 0) := by
      have actionEventuallyEq :
          (fun index =>
            fixedWaveWeakAction requestedTime ν wave
              testL2 testDerivativeL2 testLInf
              (stateSequence index)
              (nonlinearSequence index)) =ᶠ[atTop]
            (fun _ : ℕ =>
              (0 : ComplexCoordinateVector)) :=
        actionEventuallyZero
      exact
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ =>
              (0 : ComplexCoordinateVector))
            atTop (𝓝 0)).congr'
          actionEventuallyEq.symm
    have weakLimit :
        fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            stateLimit nonlinearLimit =
          0 :=
      tendsto_nhds_unique actionTendsto actionZeroTendsto
    simpa [testL2, testDerivativeL2,
      testLInf, testContinuous] using weakLimit

end

end
    ThreeDimensionalVorticityCoefficientInfiniteFixedWaveResidualSilenceWeakCarrier
end NavierStokes
end SaturationMonoid

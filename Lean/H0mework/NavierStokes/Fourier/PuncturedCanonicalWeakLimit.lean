import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveWeakCarrier
import H0mework.NavierStokes.Fourier.PuncturedCanonicalGalerkinTarget

/-!
# Punctured canonical Galerkin weak limit

The physical punctured-cube exhaustion generates eventual membership for each
nonzero fixed wave.  Conditional on whole-trajectory Cauchy convergence, this
module passes the complete infinite nonlinear row to the distributional
Fourier equation.  The Cauchy hypothesis is deliberately exposed as the
remaining source/energy compactness producer gate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientPuncturedCanonicalWeakLimit

open scoped ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget

noncomputable section

/-! ## Arbitrary finite-mode weak passage -/

/--
Conditional analytic passage theorem for an arbitrary sequence of actual
finite-mode Galerkin systems.

Once the whole space-time trajectories are Cauchy in `L²_t(ℓ²)`, completeness
generates both the whole-state limit and, through the actual infinite
nonlinear row estimate, its `L¹_t` nonlinear-row limit.  Every nonzero fixed
wave satisfying eventual membership in the actual mode sequence then obeys
the full infinite-row distributional equation.

The remaining `wholeCauchy` hypothesis is intentionally exposed: a later
source/energy compactness producer must discharge it.
-/
theorem
    finiteModeSequence_fixedWave_weakLimit_of_wholeCauchy
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
    (wholeCauchy :
      CauchySeq
        (fun radius =>
          wholeTrajectorySpaceTimePath requestedTime
            (trajectories radius)
            (fun t timeMem =>
              (evolves radius t timeMem).continuousAt.continuousWithinAt)))
    (wave : IntegerWavevector)
    (waveEventuallyMem :
      ∀ᶠ index : ℕ in atTop, wave ∈ modes index)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    ∃ stateLimit : SpaceTimeState requestedTime,
      Tendsto
          (fun radius =>
            wholeTrajectorySpaceTimePath requestedTime
              (trajectories radius)
              (fun t timeMem =>
                (evolves radius t timeMem).continuousAt.continuousWithinAt))
          atTop (𝓝 stateLimit) ∧
      ∃ nonlinearLimit :
          NonlinearRowSpaceTimeState requestedTime,
        Tendsto
            (fun radius =>
              wholeNonlinearRowSpaceTimePath requestedTime
                (trajectories radius)
                (fun t timeMem =>
                  (evolves radius t timeMem).continuousAt.continuousWithinAt)
                (transverse radius) wave)
            atTop (𝓝 nonlinearLimit) ∧
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
  let trajectoryContinuous :
      ∀ radius,
        ContinuousOn (trajectories radius)
          (Icc (0 : ℝ) requestedTime) :=
    fun radius t timeMem =>
      (evolves radius t timeMem).continuousAt.continuousWithinAt
  let stateSequence : ℕ → SpaceTimeState requestedTime :=
    fun radius =>
      wholeTrajectorySpaceTimePath requestedTime
        (trajectories radius) (trajectoryContinuous radius)
  let nonlinearSequence :
      ℕ → NonlinearRowSpaceTimeState requestedTime :=
    fun radius =>
      wholeNonlinearRowSpaceTimePath requestedTime
        (trajectories radius) (trajectoryContinuous radius)
        (transverse radius) wave
  have wholeCauchy' : CauchySeq stateSequence := by
    simpa [stateSequence, trajectoryContinuous] using wholeCauchy
  obtain ⟨stateLimit, stateTendsto⟩ :=
    cauchySeq_tendsto_of_complete wholeCauchy'
  have nonlinearCauchy : CauchySeq nonlinearSequence := by
    simpa [nonlinearSequence] using
      wholeNonlinearRowSpaceTimePath_cauchySeq
        requestedTime requestedTimePos trajectories
        trajectoryContinuous transverse wave wholeCauchy'
  obtain ⟨nonlinearLimit, nonlinearTendsto⟩ :=
    cauchySeq_tendsto_of_complete nonlinearCauchy
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
        (fun radius =>
          fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            (stateSequence radius)
            (nonlinearSequence radius))
        atTop
        (𝓝
          (fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            stateLimit nonlinearLimit)) :=
    tendsto_fixedWaveWeakAction
      requestedTime ν wave testL2 testDerivativeL2 testLInf
      stateSequence nonlinearSequence stateLimit nonlinearLimit
      stateTendsto nonlinearTendsto
  have actionEventuallyZero :
      ∀ᶠ radius : ℕ in atTop,
        fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            (stateSequence radius)
            (nonlinearSequence radius) =
          0 := by
    filter_upwards [waveEventuallyMem] with radius waveMem
    have actual :=
      finiteSupportWave_infiniteRow_weak_identity
        (modes radius)
        wave waveMem ν requestedTime requestedTimePos
        (trajectories radius)
        (fun t timeMem => evolves radius t timeMem)
        (fun t timeMem => supported radius t timeMem)
        (transverse radius)
        test testDerivative testHasDeriv
        testDerivativeContinuous testZero
        testRequestedTimeZero
    simpa [stateSequence, nonlinearSequence,
      trajectoryContinuous, testL2, testDerivativeL2,
      testLInf, testContinuous] using actual
  have actionZeroTendsto :
      Tendsto
        (fun radius =>
          fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            (stateSequence radius)
            (nonlinearSequence radius))
        atTop
        (𝓝 0) := by
    have actionEventuallyEq :
        (fun radius =>
          fixedWaveWeakAction requestedTime ν wave
            testL2 testDerivativeL2 testLInf
            (stateSequence radius)
            (nonlinearSequence radius)) =ᶠ[atTop]
          (fun _ : ℕ => (0 : ComplexCoordinateVector)) :=
      actionEventuallyZero
    exact
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ => (0 : ComplexCoordinateVector))
          atTop (𝓝 0)).congr'
        actionEventuallyEq.symm
  have weakLimit :
      fixedWaveWeakAction requestedTime ν wave
          testL2 testDerivativeL2 testLInf
          stateLimit nonlinearLimit =
        0 :=
    tendsto_nhds_unique actionTendsto actionZeroTendsto
  refine ⟨stateLimit, ?_, nonlinearLimit, ?_, ?_⟩
  · simpa [stateSequence, trajectoryContinuous] using stateTendsto
  · simpa [nonlinearSequence, trajectoryContinuous] using nonlinearTendsto
  · simpa [testL2, testDerivativeL2,
      testLInf, testContinuous] using weakLimit

/-!
Compactness normally supplies a concrete whole-state limit rather than a
bare Cauchy sequence.  The next theorem preserves that exact limit while
generating the corresponding complete nonlinear-row limit.
-/

theorem
    finiteModeSequence_fixedWave_weakLimit_of_wholeTendsto
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
      ∀ᶠ index : ℕ in atTop, wave ∈ modes index)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
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
  obtain
      ⟨generatedStateLimit, generatedStateTendsto,
        nonlinearLimit, nonlinearTendsto, weakIdentity⟩ :=
    finiteModeSequence_fixedWave_weakLimit_of_wholeCauchy
      ν requestedTime requestedTimePos modes trajectories
      evolves supported transverse stateTendsto.cauchySeq
      wave waveEventuallyMem test testDerivative
      testHasDeriv testDerivativeContinuous
      testZero testRequestedTimeZero
  have stateLimitEq : generatedStateLimit = stateLimit :=
    tendsto_nhds_unique generatedStateTendsto stateTendsto
  subst generatedStateLimit
  exact ⟨nonlinearLimit, nonlinearTendsto, weakIdentity⟩

/-! ## Punctured-cube specialization -/

/--
Strictly monotone reindexing preserves punctured-cube exhaustion.  This is
the exact coverage fact needed when compactness generates a subsequence.
-/
theorem
    nonzero_integerWave_eventually_mem_puncturedFrequencyCube_comp_strictMono
    (subsequence : ℕ → ℕ)
    (subsequenceMono : StrictMono subsequence)
    (wave : IntegerWavevector)
    (waveNeZero : wave ≠ 0) :
    ∀ᶠ index : ℕ in atTop,
      wave ∈
        puncturedIntegerWaveFrequencyCube (subsequence index) :=
  subsequenceMono.tendsto_atTop.eventually
    (nonzero_integerWave_eventually_mem_puncturedFrequencyCube
      wave waveNeZero)

/--
The physical punctured canonical exhaustion supplies the generic theorem's
eventual-membership law for every nonzero fixed wave.
-/
theorem
    puncturedCanonicalCube_fixedWave_weakLimit_of_wholeCauchy
    (ν requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (evolves :
      ∀ radius t, t ∈ Icc (0 : ℝ) requestedTime →
        HasDerivAt (trajectories radius)
          (finiteStateVorticityGenerator
            (puncturedIntegerWaveFrequencyCube radius)
            ν (trajectories radius t)) t)
    (supported :
      ∀ radius t, t ∈ Icc (0 : ℝ) requestedTime →
        ∀ output : IntegerWavevector,
          output ∉ puncturedIntegerWaveFrequencyCube radius →
            trajectories radius t output = 0)
    (transverse :
      ∀ radius t, t ∈ Icc (0 : ℝ) requestedTime →
        WholeStateTransverse (trajectories radius t))
    (wholeCauchy :
      CauchySeq
        (fun radius =>
          wholeTrajectorySpaceTimePath requestedTime
            (trajectories radius)
            (fun t timeMem =>
              (evolves radius t timeMem).continuousAt.continuousWithinAt)))
    (wave : IntegerWavevector)
    (waveNeZero : wave ≠ 0)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative
        (Icc (0 : ℝ) requestedTime))
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    ∃ stateLimit : SpaceTimeState requestedTime,
      Tendsto
          (fun radius =>
            wholeTrajectorySpaceTimePath requestedTime
              (trajectories radius)
              (fun t timeMem =>
                (evolves radius t timeMem).continuousAt.continuousWithinAt))
          atTop (𝓝 stateLimit) ∧
      ∃ nonlinearLimit :
          NonlinearRowSpaceTimeState requestedTime,
        Tendsto
            (fun radius =>
              wholeNonlinearRowSpaceTimePath requestedTime
                (trajectories radius)
                (fun t timeMem =>
                  (evolves radius t timeMem).continuousAt.continuousWithinAt)
                (transverse radius) wave)
            atTop (𝓝 nonlinearLimit) ∧
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
  exact
    finiteModeSequence_fixedWave_weakLimit_of_wholeCauchy
      ν requestedTime requestedTimePos
      puncturedIntegerWaveFrequencyCube trajectories
      evolves supported transverse wholeCauchy wave
      (nonzero_integerWave_eventually_mem_puncturedFrequencyCube
        wave waveNeZero)
      test testDerivative testHasDeriv
      testDerivativeContinuous testZero
      testRequestedTimeZero

end

end ThreeDimensionalVorticityCoefficientPuncturedCanonicalWeakLimit
end NavierStokes
end SaturationMonoid

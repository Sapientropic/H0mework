import H0mework.NavierStokes.VelocityGalerkin.VelocityEquation
import H0mework.NavierStokes.VelocityGalerkin.NonlinearSpaceTimePassage
import H0mework.NavierStokes.WholeSpace.InfiniteFixedWaveWeakCarrier

/-!
# Source-generated whole-velocity weak limit

The actual endpoint Galerkin family now supplies both sides of the nonlinear
passage: a strongly convergent whole velocity subsequence in `L²_t(ℓ²)` and,
on the same subsequence, a complete fixed-output convection limit in `L¹_t`.
This module applies the genuine Leray projection, transports the exact
finite unforced weak equation, and generates a distributional velocity NSE
row at the limit.

The limit, subsequence, nonlinear row, tests, and convergence witnesses are
all generated or universally quantified in the conclusion.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit

open scoped ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityEquation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage
open
  ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow

noncomputable section

/-! ## Leray projection on the complete nonlinear row carrier -/

/-- The genuine rowwise Leray projection lifted to the complete nonlinear
`L¹_t` carrier. -/
def wholeVelocityLerayProjectionSpaceTime
    (output : IntegerWavevector) :
    NonlinearRowSpaceTimeState 1 →L[ℝ]
      NonlinearRowSpaceTimeState 1 :=
  (transverseProjectionCLM output).compLpL 1 (commonTimeMeasure 1)

/-- Projected actual whole velocity convection row of one generated radius. -/
def generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector) : NonlinearRowSpaceTimeState 1 :=
  wholeVelocityLerayProjectionSpaceTime output
    (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
      ledger radius output)

/-- The `Lp` Leray row is almost everywhere the actual projected whole
velocity convolution generated at the same radius and time. -/
theorem generatedVelocityEndpointGalerkinProjectedNonlinearRow_coeFn_ae
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
          ledger radius output time =
        transverseProjection output
          (wholeStateVelocityNonlinearCoefficientAt
            (generatedVelocityEndpointGalerkinWholeState
              ledger radius time) output) := by
  have projectionAE :=
    (transverseProjectionCLM output).coeFn_compLpL
      (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
        ledger radius output)
  have nonlinearAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (1 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
        ledger radius output)
  filter_upwards [projectionAE, nonlinearAE] with
    time projectionEq nonlinearEq
  change
    (wholeVelocityLerayProjectionSpaceTime output
      (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
        ledger radius output)) time = _
  rw [show
    (wholeVelocityLerayProjectionSpaceTime output
      (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
        ledger radius output)) time =
      transverseProjectionCLM output
        (generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
          ledger radius output time) from projectionEq]
  rw [show
    generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
        ledger radius output time =
      wholeStateVelocityNonlinearCoefficientAt
        (generatedVelocityEndpointGalerkinWholeState
          ledger radius time) output by
      have nonlinearPoint :
          generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
              ledger radius output time =
            generatedVelocityEndpointGalerkinWholeNonlinearRowBoundedPath
              ledger radius output time := by
        simpa [generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath]
          using nonlinearEq
      exact nonlinearPoint.trans rfl]
  rfl

/-! ## Exact interpretation of the projected nonlinear weak action -/

theorem
    fixedLInfScalarL1IntegralCLM_generatedProjectedVelocityNonlinear_eq_intervalIntegral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (scalar : ℝ → ℂ)
    (scalarContinuous : ContinuousOn scalar (Icc (0 : ℝ) 1)) :
    fixedLInfScalarL1IntegralCLM 1
        (restrictedScalarLInf 1 scalar scalarContinuous)
        (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
          ledger radius output) =
      ∫ t in (0 : ℝ)..1,
        scalar t •
          transverseProjection output
            (wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger radius t) output) := by
  let scalarLp := restrictedScalarLInf 1 scalar scalarContinuous
  let nonlinearLp :=
    generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
      ledger radius output
  have scalarAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (∞ : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (restrictedScalarBoundedPath 1 scalar scalarContinuous)
  have nonlinearAE :=
    generatedVelocityEndpointGalerkinProjectedNonlinearRow_coeFn_ae
      ledger radius output
  have productAE :
      ⇑(scalarLp • nonlinearLp :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure 1)) =ᵐ[commonTimeMeasure 1]
        ⇑scalarLp • ⇑nonlinearLp :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLp nonlinearLp
  change
    (MeasureTheory.L1.integralCLM' ℂ) (scalarLp • nonlinearLp) = _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ time, (scalarLp • nonlinearLp) time
        ∂(commonTimeMeasure 1)) =
      ∫ time : Icc (0 : ℝ) 1,
        scalar time.1 •
          transverseProjection output
            (wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeState
                ledger radius time) output)
        ∂(commonTimeMeasure 1) := by
      apply integral_congr_ae
      filter_upwards [productAE, scalarAE, nonlinearAE] with
        time productEq scalarEq nonlinearEq
      rw [productEq]
      change scalarLp time • nonlinearLp time = _
      have scalarPoint : scalarLp time = scalar time.1 := by
        have scalarPoint' :
            scalarLp time =
              restrictedScalarBoundedPath
                1 scalar scalarContinuous time := by
          simpa [scalarLp, restrictedScalarLInf] using scalarEq
        exact scalarPoint'.trans rfl
      rw [scalarPoint, nonlinearEq]
    _ = _ := by
      simpa [generatedVelocityEndpointGalerkinWholeState] using
        commonTime_integral_eq_intervalIntegral_vector
          1 (by norm_num)
          (fun t =>
            scalar t •
              transverseProjection output
                (wholeStateVelocityNonlinearCoefficientAt
                  (generatedVelocityEndpointGalerkinWholeStateAtTime
                    ledger radius t) output))

/-! ## Exact finite actions on the source-generated `Lp` carriers -/

/-- `Lp` packaging of the exact actual unforced velocity weak equation.
The nonlinear row is the genuine projected whole convolution generated by
the same Galerkin event. -/
theorem generatedVelocityEndpointGalerkin_fixedWaveWeakAction_eq_zero
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius)
    (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative (Icc (0 : ℝ) 1))
    (testZero : test 0 = 0)
    (testOneZero : test 1 = 0) :
    fixedWaveWeakAction 1 nu.coeff output
        (restrictedScalarL2 1 test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (restrictedScalarL2 1 testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf 1 test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
        (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
          ledger radius output) =
      0 := by
  let velocityTrajectory : ℝ → ComplexVorticityHilbertState :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius
  let velocityContinuous :
      ContinuousOn velocityTrajectory (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius
  let testContinuous : ContinuousOn test (Icc (0 : ℝ) 1) :=
    fun t timeMem =>
      (testHasDeriv t timeMem).continuousAt.continuousWithinAt
  have statePathEq :
      generatedVelocityEndpointGalerkinSpaceTimePath ledger radius =
        wholeTrajectorySpaceTimePath 1
          velocityTrajectory velocityContinuous := by
    rfl
  have weakInterval :=
    generatedVelocityEndpointGalerkinWholeVelocityWave_weakInterval_eq_zero
      ledger radius output outputMem test testDerivative testHasDeriv
      testDerivativeContinuous testZero testOneZero
  change
    fixedWaveWeakAction 1 nu.coeff output
        (restrictedScalarL2 1 test testContinuous)
        (restrictedScalarL2 1 testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf 1 test testContinuous)
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
        (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
          ledger radius output) = 0
  rw [statePathEq]
  unfold fixedWaveWeakAction
  rw [
    fixedL2ScalarL2IntegralCLM_wholeTrajectory_eq_intervalIntegral
      1 (by norm_num) testDerivative testDerivativeContinuous
      velocityTrajectory velocityContinuous output,
    fixedLInfScalarL1IntegralCLM_generatedProjectedVelocityNonlinear_eq_intervalIntegral
      ledger radius output test testContinuous,
    fixedL2ScalarL2IntegralCLM_viscousWholeTrajectory_eq_intervalIntegral
      1 (by norm_num) test testContinuous
      velocityTrajectory velocityContinuous output
      (nu.coeff * integerWaveViscousMultiplier output)]
  simpa [velocityTrajectory] using weakInterval

/-! ## Source-generated distributional velocity row -/

/-- The complete distributional unforced velocity NSE obligation on one
fixed Fourier row. -/
def WholeVelocityFixedWaveWeakNSE
    (ν : ℝ)
    (output : IntegerWavevector)
    (state : SpaceTimeState 1)
    (nonlinear : NonlinearRowSpaceTimeState 1) : Prop :=
  ∀ (test testDerivative : ℝ → ℂ)
    (testHasDeriv :
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt test (testDerivative t) t)
    (testDerivativeContinuous :
      ContinuousOn testDerivative (Icc (0 : ℝ) 1))
    (_testZero : test 0 = 0)
    (_testOneZero : test 1 = 0),
    fixedWaveWeakAction 1 ν output
        (restrictedScalarL2 1 test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        (restrictedScalarL2 1 testDerivative
          testDerivativeContinuous)
        (restrictedScalarLInf 1 test
          (fun t timeMem =>
            (testHasDeriv t timeMem).continuousAt.continuousWithinAt))
        state nonlinear =
      0

/-- Strong state convergence and same-subsequence nonlinear convergence
transport the exact actual Galerkin actions to the complete fixed-row weak
NSE obligation. -/
theorem generatedVelocityEndpoint_fixedWaveWeakNSE_of_tendsto
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (subsequenceMono : StrictMono subsequence)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit))
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (nonlinearLimit : NonlinearRowSpaceTimeState 1)
    (nonlinearTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
            ledger (subsequence index) output)
        atTop (𝓝 nonlinearLimit)) :
    WholeVelocityFixedWaveWeakNSE nu.coeff output stateLimit
      (wholeVelocityLerayProjectionSpaceTime output nonlinearLimit) := by
  have projectedNonlinearTendsto :
      Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (subsequence index) output)
          atTop
          (𝓝 (wholeVelocityLerayProjectionSpaceTime output nonlinearLimit)) :=
    ((wholeVelocityLerayProjectionSpaceTime output).continuous.tendsto
      nonlinearLimit).comp nonlinearTendsto
  have outputEventuallyMem :
      ∀ᶠ index : ℕ in atTop,
        output ∈ wholeRestartModes (subsequence index) := by
    have eventualRadius :
        ∀ᶠ radius : ℕ in atTop,
          output ∈ puncturedIntegerWaveFrequencyCube radius :=
      nonzero_integerWave_eventually_mem_puncturedFrequencyCube
        output outputNe
    exact subsequenceMono.tendsto_atTop.eventually eventualRadius
  unfold WholeVelocityFixedWaveWeakNSE
  intro test testDerivative testHasDeriv testDerivativeContinuous
    testZero testOneZero
  let testContinuous : ContinuousOn test (Icc (0 : ℝ) 1) :=
    fun t timeMem =>
      (testHasDeriv t timeMem).continuousAt.continuousWithinAt
  let testL2 := restrictedScalarL2 1 test testContinuous
  let testDerivativeL2 :=
    restrictedScalarL2 1 testDerivative testDerivativeContinuous
  let testLInf := restrictedScalarLInf 1 test testContinuous
  have actionTendsto :
      Tendsto
        (fun index =>
          fixedWaveWeakAction 1 nu.coeff output
            testL2 testDerivativeL2 testLInf
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index))
            (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (subsequence index) output))
        atTop
        (𝓝
          (fixedWaveWeakAction 1 nu.coeff output
            testL2 testDerivativeL2 testLInf stateLimit
            (wholeVelocityLerayProjectionSpaceTime output
              nonlinearLimit))) :=
    tendsto_fixedWaveWeakAction
      1 nu.coeff output testL2 testDerivativeL2 testLInf
      (fun index =>
        generatedVelocityEndpointGalerkinSpaceTimePath
          ledger (subsequence index))
      (fun index =>
        generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
          ledger (subsequence index) output)
      stateLimit
      (wholeVelocityLerayProjectionSpaceTime output nonlinearLimit)
      stateTendsto projectedNonlinearTendsto
  have actionEventuallyZero :
      ∀ᶠ index : ℕ in atTop,
        fixedWaveWeakAction 1 nu.coeff output
            testL2 testDerivativeL2 testLInf
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index))
            (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (subsequence index) output) =
          0 := by
    filter_upwards [outputEventuallyMem] with index outputMem
    simpa [testL2, testDerivativeL2, testLInf, testContinuous] using
      generatedVelocityEndpointGalerkin_fixedWaveWeakAction_eq_zero
        ledger (subsequence index) output outputMem
        test testDerivative testHasDeriv testDerivativeContinuous
        testZero testOneZero
  have actionZeroTendsto :
      Tendsto
        (fun index =>
          fixedWaveWeakAction 1 nu.coeff output
            testL2 testDerivativeL2 testLInf
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index))
            (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (subsequence index) output))
        atTop (𝓝 0) := by
    have actionEventuallyEq :
        (fun index =>
          fixedWaveWeakAction 1 nu.coeff output
            testL2 testDerivativeL2 testLInf
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index))
            (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (subsequence index) output)) =ᶠ[atTop]
          (fun _ : ℕ => (0 : ComplexCoordinateVector)) :=
      actionEventuallyZero
    exact (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ComplexCoordinateVector))
          atTop (𝓝 0)).congr' actionEventuallyEq.symm
  have weakLimit :
      fixedWaveWeakAction 1 nu.coeff output
          testL2 testDerivativeL2 testLInf stateLimit
          (wholeVelocityLerayProjectionSpaceTime output nonlinearLimit) =
        0 :=
    tendsto_nhds_unique actionTendsto actionZeroTendsto
  simpa [testL2, testDerivativeL2, testLInf, testContinuous] using weakLimit

/-- For every fixed nonzero Fourier output, the bounded whole-restart
source generates a strong velocity limit, a same-subsequence whole
convection limit, and the full distributional unforced NSE row for every
compactly supported `C¹` time test.

The source-facing mouth contains only the actual source data and the
observation row.  The limit, subsequence, nonlinear row, and all test
quantification live in the conclusion. -/
theorem sourceGeneratedVelocityEndpoint_fixedNonzeroWave_weakNSE
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    ∃ stateLimit : SpaceTimeState 1,
      stateLimit ∈
          closure
            (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              generatedVelocityEndpointGalerkinSpaceTimePath
                ledger (subsequence index))
            atTop (𝓝 stateLimit) ∧
        ∃ nonlinearLimit : NonlinearRowSpaceTimeState 1,
          Tendsto
              (fun index =>
                generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
                  ledger (subsequence index) output)
              atTop (𝓝 nonlinearLimit) ∧
          WholeVelocityFixedWaveWeakNSE nu.coeff output stateLimit
            (wholeVelocityLerayProjectionSpaceTime output
              nonlinearLimit) := by
  obtain
      ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
        stateTendsto, nonlinearLimit, nonlinearTendsto⟩ :=
    generatedVelocityEndpointGalerkinSpaceTimePath_strong_subsequence_with_nonlinearRow_limit
      ledger output
  exact
    ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
      stateTendsto, nonlinearLimit, nonlinearTendsto,
      generatedVelocityEndpoint_fixedWaveWeakNSE_of_tendsto
        ledger subsequence subsequenceMono stateLimit stateTendsto
        output outputNe nonlinearLimit nonlinearTendsto⟩

/-- One source-generated strong subsequence simultaneously carries a
complete nonlinear `L¹_t` limit and the unforced weak NSE identity at every
nonzero Fourier output.  No diagonal subsequence is required: strong whole
velocity convergence makes every fixed-output nonlinear sequence Cauchy on
the same radius subsequence. -/
theorem sourceGeneratedVelocityEndpoint_allNonzeroWaves_weakNSE
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    ∃ stateLimit : SpaceTimeState 1,
      stateLimit ∈
          closure
            (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              generatedVelocityEndpointGalerkinSpaceTimePath
                ledger (subsequence index))
            atTop (𝓝 stateLimit) ∧
        ∃ nonlinearLimit :
            IntegerWavevector → NonlinearRowSpaceTimeState 1,
          (∀ output : IntegerWavevector,
            Tendsto
              (fun index =>
                generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
                  ledger (subsequence index) output)
              atTop (𝓝 (nonlinearLimit output))) ∧
          ∀ output : IntegerWavevector,
            output ≠ 0 →
              WholeVelocityFixedWaveWeakNSE nu.coeff output stateLimit
                (wholeVelocityLerayProjectionSpaceTime output
                  (nonlinearLimit output)) := by
  obtain
      ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
        stateTendsto, _stateStrong, _initialTendsto,
        _initialEnergyTendsto, _fixedWaveTendsto, _fixedWaveStrong⟩ :=
    generatedVelocityEndpointGalerkinSpaceTimePath_strong_subsequence_with_fixed_wave_rows
      ledger
  have stateCauchy :
      CauchySeq
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index)) :=
    stateTendsto.cauchy_map
  have nonlinearExists (output : IntegerWavevector) :
      ∃ limit : NonlinearRowSpaceTimeState 1,
        Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
              ledger (subsequence index) output)
          atTop (𝓝 limit) := by
    exact cauchySeq_tendsto_of_complete
      (generatedVelocityEndpointGalerkinWholeNonlinearRow_cauchySeq_of_spaceTime_cauchySeq
        ledger subsequence output stateCauchy)
  let nonlinearLimit :
      IntegerWavevector → NonlinearRowSpaceTimeState 1 :=
    fun output => Classical.choose (nonlinearExists output)
  have nonlinearTendsto (output : IntegerWavevector) :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
            ledger (subsequence index) output)
        atTop (𝓝 (nonlinearLimit output)) := by
    exact Classical.choose_spec (nonlinearExists output)
  refine
    ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
      stateTendsto, nonlinearLimit, nonlinearTendsto, ?_⟩
  intro output outputNe
  exact generatedVelocityEndpoint_fixedWaveWeakNSE_of_tendsto
    ledger subsequence subsequenceMono stateLimit stateTendsto
    output outputNe (nonlinearLimit output) (nonlinearTendsto output)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
end NavierStokes
end SaturationMonoid

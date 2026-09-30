import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness
import H0mework.NavierStokes.VelocityGalerkin.StrongSpaceTimeCompactness
import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow
import H0mework.NavierStokes.Fourier.WholeVelocityNonlinearTimePassage

/-!
# Actual whole-velocity equation of the generated endpoint Galerkin family

The source-generated Galerkin stage already evolves its vorticity by the
unforced finite Navier--Stokes generator.  Biot--Savart, Leray projection,
and the exact finite/whole velocity convolution identity turn that same
actual event into the physical whole-velocity Fourier equation.

No target solution, continuation, cutoff, nonlinear row, or derivative is
provided by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityEquation

open Set MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open
  ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientWholeVelocityNonlinearTimePassage
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness

noncomputable section

/-- The installed whole velocity state of every generated stage is
transverse at every ambient time. -/
theorem generatedVelocityEndpointGalerkinWholeVelocity_transverse
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : ℝ) :
    WholeStateTransverse
      (finiteStateWholeVelocity
        (wholeRestartModes radius)
        ((ledger.family.stage radius).trajectory time)) :=
  finiteStateWholeVelocity_transverse _ _

/-- On every retained output, the same actual unforced Galerkin event writes
the Leray-projected whole velocity convection minus the viscous velocity
row.  This is the exact physical derivative consumed by weak passage. -/
theorem generatedVelocityEndpointGalerkinWholeVelocityWave_hasDerivAt
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector)
    (outputMem : output ∈ wholeRestartModes radius) :
    HasDerivAt
      (fun actual =>
        finiteStateWholeVelocity
          (wholeRestartModes radius)
          ((ledger.family.stage radius).trajectory actual) output)
      (transverseProjection output
          (wholeStateVelocityNonlinearCoefficientAt
            (finiteStateWholeVelocity
              (wholeRestartModes radius)
              ((ledger.family.stage radius).trajectory time.1))
            output) -
        (nu.coeff * integerWaveViscousMultiplier output) •
          finiteStateWholeVelocity
            (wholeRestartModes radius)
            ((ledger.family.stage radius).trajectory time.1) output)
      time.1 := by
  let stage := ledger.family.stage radius
  have physical := stage.physical time.1 time.2
  have rowDerivative :=
    finiteStateVelocityTrajectoryWave_hasDerivAt
      stage.trajectory time.1
      (finiteStateVorticityGenerator
        (wholeRestartModes radius) nu.coeff
        (stage.trajectory time.1))
      output physical.1
  rw [biotSavart_finiteStateVorticityGenerator_eq_velocityUpdate
    (wholeRestartModes radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    nu.coeff (stage.trajectory time.1)
    (fun wave waveMem => physical.2.2.1 wave)
    output outputMem] at rowDerivative
  rw [← wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity]
    at rowDerivative
  simpa only [finiteStateWholeVelocity_apply, if_pos outputMem] using
    rowDerivative

/-! ## Actual velocity weak action before the space-time quotient -/

/-- Every retained Fourier row of the actual generated Galerkin write obeys
the unforced velocity Navier--Stokes equation against a compactly supported
`C¹` time test.  The whole velocity convolution and Leray projection are
generated internally from the same trajectory. -/
theorem generatedVelocityEndpointGalerkinWholeVelocityWave_weakInterval_eq_zero
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
    (∫ t in (0 : ℝ)..1,
        testDerivative t •
          generatedVelocityEndpointGalerkinWholeStateAtTime
            ledger radius t output) +
      (∫ t in (0 : ℝ)..1,
        test t •
          transverseProjection output
            (wholeStateVelocityNonlinearCoefficientAt
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger radius t) output)) -
      (∫ t in (0 : ℝ)..1,
        test t •
          ((nu.coeff * integerWaveViscousMultiplier output) •
            generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger radius t output)) =
      0 := by
  let velocityTrajectory : ℝ → ComplexVorticityHilbertState :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius
  let nonlinearTrajectory : ℝ → ComplexCoordinateVector := fun t =>
    transverseProjection output
      (wholeStateVelocityNonlinearCoefficientAt
        (velocityTrajectory t) output)
  let tangent : ℝ → ComplexCoordinateVector := fun t =>
    nonlinearTrajectory t -
      (nu.coeff * integerWaveViscousMultiplier output) •
        velocityTrajectory t output
  have velocityContinuous :
      ContinuousOn velocityTrajectory (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius
  have velocityTransverse :
      ∀ t ∈ Icc (0 : ℝ) 1,
        WholeStateTransverse (velocityTrajectory t) := by
    intro t _timeMem
    exact finiteStateWholeVelocity_transverse
      (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory t)
  have waveDerivative :
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt
          (fun actual => velocityTrajectory actual output)
          (tangent t) t := by
    intro t timeMem
    simpa [velocityTrajectory, tangent, nonlinearTrajectory,
      generatedVelocityEndpointGalerkinWholeStateAtTime,
      finiteStateWholeVelocity] using
      generatedVelocityEndpointGalerkinWholeVelocityWave_hasDerivAt
        ledger radius ⟨t, timeMem⟩ output outputMem
  have rowContinuous :
      ContinuousOn (fun t => velocityTrajectory t output)
        (Icc (0 : ℝ) 1) :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 output).continuous.comp_continuousOn velocityContinuous
  have wholeNonlinearContinuous :
      ContinuousOn
        (fun t =>
          wholeStateVelocityNonlinearCoefficientAt
            (velocityTrajectory t) output)
        (Icc (0 : ℝ) 1) :=
    wholeStateVelocityNonlinearCoefficientAt_comp_continuousOn
      velocityTrajectory output 0 1 velocityContinuous velocityTransverse
  have nonlinearContinuous :
      ContinuousOn nonlinearTrajectory (Icc (0 : ℝ) 1) := by
    change ContinuousOn
      ((transverseProjectionCLM output) ∘
        fun t =>
          wholeStateVelocityNonlinearCoefficientAt
            (velocityTrajectory t) output)
      (Icc (0 : ℝ) 1)
    exact (transverseProjectionCLM output).continuous.comp_continuousOn
      wholeNonlinearContinuous
  have viscousContinuous :
      ContinuousOn
        (fun t =>
          (nu.coeff * integerWaveViscousMultiplier output) •
            velocityTrajectory t output)
        (Icc (0 : ℝ) 1) :=
    rowContinuous.const_smul
      (nu.coeff * integerWaveViscousMultiplier output)
  have tangentContinuous :
      ContinuousOn tangent (Icc (0 : ℝ) 1) :=
    nonlinearContinuous.sub viscousContinuous
  let testContinuous : ContinuousOn test (Icc (0 : ℝ) 1) :=
    fun t timeMem =>
      (testHasDeriv t timeMem).continuousAt.continuousWithinAt
  have testDerivativeIntegrable :
      IntervalIntegrable testDerivative volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (by norm_num) testDerivativeContinuous
  have tangentIntegrable :
      IntervalIntegrable tangent volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (by norm_num) tangentContinuous
  have interiorToIcc :
      ∀ t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        t ∈ Icc (0 : ℝ) 1 := by
    intro t timeMem
    have timeMem' : t ∈ Ioo (0 : ℝ) 1 := by
      simpa using timeMem
    exact ⟨le_of_lt timeMem'.1, le_of_lt timeMem'.2⟩
  have integrationByParts :=
    intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
      (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        testContinuous)
      (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        rowContinuous)
      (fun t timeMem => testHasDeriv t (interiorToIcc t timeMem))
      (fun t timeMem => waveDerivative t (interiorToIcc t timeMem))
      testDerivativeIntegrable tangentIntegrable
  rw [testZero, testOneZero] at integrationByParts
  simp only [zero_smul, zero_sub, neg_zero] at integrationByParts
  have nonlinearIntegrable :
      IntervalIntegrable
        (fun t => test t • nonlinearTrajectory t) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (by norm_num) (testContinuous.smul nonlinearContinuous)
  have viscousIntegrable :
      IntervalIntegrable
        (fun t =>
          test t •
            ((nu.coeff * integerWaveViscousMultiplier output) •
              velocityTrajectory t output)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc
      (by norm_num) (testContinuous.smul viscousContinuous)
  have splitTangent :
      (∫ t in (0 : ℝ)..1, test t • tangent t) =
        (∫ t in (0 : ℝ)..1, test t • nonlinearTrajectory t) -
          ∫ t in (0 : ℝ)..1,
            test t •
              ((nu.coeff * integerWaveViscousMultiplier output) •
                velocityTrajectory t output) := by
    rw [← intervalIntegral.integral_sub
      nonlinearIntegrable viscousIntegrable]
    apply intervalIntegral.integral_congr
    intro t _timeMem
    simp [tangent, smul_sub]
  rw [splitTangent] at integrationByParts
  change
    (∫ t in (0 : ℝ)..1,
        testDerivative t • velocityTrajectory t output) +
      (∫ t in (0 : ℝ)..1,
        test t • nonlinearTrajectory t) -
      (∫ t in (0 : ℝ)..1,
        test t •
          ((nu.coeff * integerWaveViscousMultiplier output) •
            velocityTrajectory t output)) = 0
  calc
    (∫ t in (0 : ℝ)..1,
        testDerivative t • velocityTrajectory t output) +
        (∫ t in (0 : ℝ)..1,
          test t • nonlinearTrajectory t) -
        (∫ t in (0 : ℝ)..1,
          test t •
            ((nu.coeff * integerWaveViscousMultiplier output) •
              velocityTrajectory t output)) =
      (∫ t in (0 : ℝ)..1,
          testDerivative t • velocityTrajectory t output) +
        ((∫ t in (0 : ℝ)..1,
            test t • nonlinearTrajectory t) -
          ∫ t in (0 : ℝ)..1,
            test t •
              ((nu.coeff * integerWaveViscousMultiplier output) •
                velocityTrajectory t output)) := by abel
    _ =
      (∫ t in (0 : ℝ)..1,
          testDerivative t • velocityTrajectory t output) +
        -(∫ t in (0 : ℝ)..1,
          testDerivative t • velocityTrajectory t output) := by
      rw [integrationByParts]
    _ = 0 := by simp

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityEquation
end NavierStokes
end SaturationMonoid

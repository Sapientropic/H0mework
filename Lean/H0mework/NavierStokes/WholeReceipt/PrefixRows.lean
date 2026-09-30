import H0mework.NavierStokes.Accumulation.ScaleCriticalWindow

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.WholePrefixRows

open scoped ContDiff
open Set MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice

noncomputable section

theorem initial_eq {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) (length : Nat) :
    wholeRestartPrefixPhysicalTrajectory initial length 0 = initial.initialState := by
  induction length with
  | zero => rfl
  | succ length previous =>
      rw [wholeRestartPrefixPhysicalTrajectory,
        endpointSplice_of_le _ _ _ _ (elapsedTime_nonneg initial length)]
      exact previous

/-- Read the same finite prefix's whole weak equation in heat coordinates. -/
theorem integratingFactor
    {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) (wave : IntegerWavevector) (waveNe : wave ≠ 0)
    {time : Real} (timePos : 0 < time) (timeLe : time ≤ elapsedTime initial length) :
    (∫ actual in (0 : Real)..time,
      Real.exp ((nu.coeff * integerWaveViscousMultiplier wave) * actual) •
        wholeStateVorticityNonlinearCoefficientAt
          (wholeRestartPrefixPhysicalTrajectory initial length actual) wave) =
      Real.exp ((nu.coeff * integerWaveViscousMultiplier wave) * time) •
          wholeRestartPrefixPhysicalTrajectory initial length time wave -
        initial.initialState wave := by
  let damping := nu.coeff * integerWaveViscousMultiplier wave
  let test := fun actual : Real => (Real.exp (damping * actual) : Complex)
  have realSmooth : ContDiff Real ∞ (fun actual : Real => Real.exp (damping * actual)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have smooth : ContDiff Real ∞ test := Complex.ofRealCLM.contDiff.comp realSmooth
  have derivative (actual : Real) :
      deriv test actual = (Real.exp (damping * actual) * damping : Real) := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id actual).const_mul damping).exp.ofReal_comp).deriv
  have weak := wholeRestartPrefix_physicalWeakRow_eq_boundary initial length
    (show (0 : Real) ≤ 0 from le_rfl) timePos timeLe wave waveNe test smooth
  have cancellation (actual : Real) :
      deriv test actual • wholeRestartPrefixPhysicalTrajectory initial length actual wave =
        test actual • (damping : Complex) •
          wholeRestartPrefixPhysicalTrajectory initial length actual wave := by
    rw [derivative, Complex.ofReal_mul, mul_smul]
  simp_rw [cancellation] at weak
  have reduced :
      (∫ actual in (0 : Real)..time, test actual •
        wholeStateVorticityNonlinearCoefficientAt
          (wholeRestartPrefixPhysicalTrajectory initial length actual) wave) =
      test time • wholeRestartPrefixPhysicalTrajectory initial length time wave -
        test 0 • wholeRestartPrefixPhysicalTrajectory initial length 0 wave := by
    dsimp only [damping] at weak
    exact (add_sub_cancel_left _ _).symm.trans weak
  have realAction (scalar : Real) (value : ComplexCoordinateVector) :
      (scalar : Complex) • value = scalar • value := by
    ext coordinate
    simp [Complex.real_smul]
  simpa only [test, damping, mul_zero, Real.exp_zero, Complex.ofReal_one,
    one_smul, initial_eq, realAction] using reduced

/-- The cumulative-time row is the heat path from the original raw initial state. -/
theorem heatPath_eq
    {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat) (wave : IntegerWavevector) (waveNe : wave ≠ 0)
    {time : Real} (timeNonneg : 0 ≤ time) (timeLe : time ≤ elapsedTime initial length) :
    heatDuhamelComplexCoordinatePath (initial.initialState wave)
      (fun actual => wholeStateVorticityNonlinearCoefficientAt
        (wholeRestartPrefixPhysicalTrajectory initial length actual) wave)
      (nu.coeff * integerWaveViscousMultiplier wave) 0 time =
        wholeRestartPrefixPhysicalTrajectory initial length time wave := by
  rcases timeNonneg.eq_or_lt with zero | positive
  · subst time
    simp [heatDuhamelComplexCoordinatePath, intervalIntegralComplexCoordinatePath, initial_eq]
  · have factor := integratingFactor initial length wave waveNe positive timeLe
    have ledger : initial.initialState wave +
        (∫ actual in (0 : Real)..time,
          Real.exp ((nu.coeff * integerWaveViscousMultiplier wave) * actual) •
            wholeStateVorticityNonlinearCoefficientAt
              (wholeRestartPrefixPhysicalTrajectory initial length actual) wave) =
        Real.exp ((nu.coeff * integerWaveViscousMultiplier wave) * time) •
          wholeRestartPrefixPhysicalTrajectory initial length time wave := by
      rw [factor]
      abel
    unfold heatDuhamelComplexCoordinatePath intervalIntegralComplexCoordinatePath
    change Real.exp (-(nu.coeff * integerWaveViscousMultiplier wave) * (time - 0)) •
      (initial.initialState wave + ∫ actual in (0 : Real)..time,
        Real.exp ((nu.coeff * integerWaveViscousMultiplier wave) * (actual - 0)) •
          wholeStateVorticityNonlinearCoefficientAt
            (wholeRestartPrefixPhysicalTrajectory initial length actual) wave) = _
    simp only [sub_zero]
    rw [ledger, smul_smul, ← Real.exp_add]
    simp

end
end SaturationMonoid.NavierStokes.WholePrefixRows

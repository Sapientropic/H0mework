import H0mework.NavierStokes.RecoveryAction.RecoveryJointCurrent

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryJointAction

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeRecoveryJointCurrent
open NativeTimeJetCarrier NativeStressCurlAlgebra NativeStressSource

noncomputable section

variable {nu : Viscosity}

theorem regular_current_hasDerivAt (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (regular : time.1 ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 3) (wave : IntegerWavevector) :
    HasDerivAt (fun actual => NativeRecoveryCurrentAction.physicalCoefficient initial actual direction.succ wave)
      (momentum initial time wave direction) time.1 := by
  rw [momentum_regular initial time regular]
  have row := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt _
    (NativeRecoveryCurrentAction.velocity_hasDerivAt initial time.1 regular)
  have coordinate := (ContinuousLinearMap.proj direction : ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt _ row
  change HasDerivAt (fun actual => velocity initial actual wave direction)
    (NativeRecoveryCurrentAction.momentum initial time.1 wave direction) time.1 at coordinate
  apply coordinate.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro actual
  change NativeRecoveryCurrentAction.physicalCoefficient initial actual direction.succ wave = velocity initial actual wave direction
  rw [NativeRecoveryCurrentAction.physicalCoefficient_eq]
  rfl

theorem uncovered_current_tendsto (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    let escape := NativeRecoveryCoverage.sourceUncoveredAction initial time.1 time.2 uncovered
    let source := NativeRecoveryEscapeStress.sourceStress initial time.1 time.2 uncovered
    Tendsto (fun index => NativeEscapePairedCurrent.actual escape (source.refinement index) direction wave) atTop
      (𝓝 (current initial time direction wave)) := by
  rw [current_uncovered initial time uncovered]
  exact NativeEscapePairedCurrent.source_current_tendsto initial time.1 time.2 uncovered direction wave

theorem uncovered_current_derivative_tendsto (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) (direction : Fin 3) (wave : IntegerWavevector) :
    let escape := NativeRecoveryCoverage.sourceUncoveredAction initial time.1 time.2 uncovered
    let source := NativeRecoveryEscapeStress.sourceStress initial time.1 time.2 uncovered
    Tendsto (fun index => deriv (NativeEscapeCurrentAction.currentCurve escape (source.refinement index) direction.succ wave)
      (escape.sample (source.refinement index))) atTop (𝓝 (momentum initial time wave direction)) := by
  rw [momentum_uncovered initial time uncovered]
  exact NativeEscapeCurrentAction.source_current_time_derivative_tendsto initial time.1 time.2 uncovered direction wave

theorem momentum_pressure (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) :
    momentum initial time wave = nativeFluidStressDivergenceCoefficient (stress initial time) wave -
      ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * pressure initial time wave) • complexWavevector wave -
        (nu.coeff * integerWaveViscousMultiplier wave) • velocity initial time.1 wave := by
  have original := nativeFluidStressDivergenceCoefficient_eq_leray_add_pressure wave (stress initial time wave)
  have resolved : projectedDivergenceCLM wave (stress initial time wave) =
      nativeFluidStressDivergenceCoefficient (stress initial time) wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) * pressure initial time wave) • complexWavevector wave :=
    eq_sub_of_add_eq original.symm
  rw [momentum, resolved]

theorem correction_from_current_action (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) :
    NativeJointStressFilterControl.coefficient modes (velocity initial time.1) (stress initial time) wave =
      (if wave ∈ modes then fourierCurlCoefficient wave (momentum initial time wave) else 0) -
        (nativeFluidConstitutiveVorticityAction (quadraticFlux (complexSharpSupportProjection modes (velocity initial time.1))) wave -
          (nu.coeff * integerWaveViscousMultiplier wave) •
            fourierCurlCoefficient wave (complexSharpSupportProjection modes (velocity initial time.1) wave)) := by
  let curl := (fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ
  have projected (tensor : NativeFluidStressCoefficient) :
      curl (projectedDivergenceCLM wave tensor) = NativeWholeVelocityFilterControl.rowAction wave tensor := by
    change fourierCurlCoefficient wave (transverseProjection wave (nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave)) = _
    rw [fourierCurlCoefficient_transverseProjection]
    rfl
  change NativeWholeVelocityFilterControl.rowAction wave
    (NativeRecoveryEscapeCorrection.projectStress modes (stress initial time) wave -
      quadraticFlux (complexSharpSupportProjection modes (velocity initial time.1)) wave) = _
  rw [map_sub]
  by_cases included : wave ∈ modes
  · simp only [NativeRecoveryEscapeCorrection.projectStress, if_pos included, complexSharpSupportProjection_apply]
    change NativeWholeVelocityFilterControl.rowAction wave (stress initial time wave) -
      NativeWholeVelocityFilterControl.rowAction wave (quadraticFlux (complexSharpSupportProjection modes (velocity initial time.1)) wave) =
        curl (projectedDivergenceCLM wave (stress initial time wave) -
          (nu.coeff * integerWaveViscousMultiplier wave) • velocity initial time.1 wave) -
          (NativeWholeVelocityFilterControl.rowAction wave (quadraticFlux (complexSharpSupportProjection modes (velocity initial time.1)) wave) -
            (nu.coeff * integerWaveViscousMultiplier wave) • curl (velocity initial time.1 wave))
    rw [map_sub, map_smul, projected]
    abel
  · simp only [NativeRecoveryEscapeCorrection.projectStress, if_neg included, map_zero, complexSharpSupportProjection_apply]
    change _ = (0 : ComplexCoordinateVector) - (NativeWholeVelocityFilterControl.rowAction wave
      (quadraticFlux (complexSharpSupportProjection modes (velocity initial time.1)) wave) -
        (nu.coeff * integerWaveViscousMultiplier wave) • curl 0)
    rw [map_zero, smul_zero, sub_zero]

end
end SaturationMonoid.NavierStokes.NativeRecoveryJointAction

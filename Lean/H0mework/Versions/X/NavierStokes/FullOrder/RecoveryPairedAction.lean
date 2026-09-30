import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryPairedCarrier

set_option autoImplicit false
open scoped Topology ENNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeRecoveryPairedAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeRecoveryJointCurrent
open NativeStressPairingCarrier NativeHilbertDiracCurrent NativeRecoveryPairedCarrier
open NativeTimeJetCarrier NativeStressCurlAlgebra NativeStressSource NativeFixedFilterGlobalControl

noncomputable section

variable {nu : Viscosity}

def momentum (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (fun output input =>
    -inner ℂ (component (source initial time) (wave, output)) (component (source initial time) (0, input))) -
      (nu.coeff * integerWaveViscousMultiplier wave) • fun direction => diracCurrent (source initial time) direction.succ wave

def pressure (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) : ℂ :=
  stressPressureCoefficient wave (fun output input =>
    -inner ℂ (component (source initial time) (wave, output)) (component (source initial time) (0, input)))

theorem momentum_eq (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) :
    momentum initial time wave = NativeRecoveryJointCurrent.momentum initial time wave := by
  simp only [momentum, source_stress, source_current]
  rfl

theorem pressure_eq (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) :
    pressure initial time wave = NativeRecoveryJointCurrent.pressure initial time wave := by
  simp only [pressure, source_stress]
  rfl

theorem source_regular_current_action (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (regular : time.1 ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 3) (wave : IntegerWavevector) :
    HasDerivAt (fun actual => NativeRecoveryCurrentAction.physicalCoefficient initial actual direction.succ wave)
      (momentum initial time wave direction) time.1 := by
  rw [momentum_eq]
  exact NativeRecoveryJointAction.regular_current_hasDerivAt initial time regular direction wave

theorem source_uncovered_current_action (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) (direction : Fin 3) (wave : IntegerWavevector) :
    let escape := NativeRecoveryCoverage.sourceUncoveredAction initial time.1 time.2 uncovered
    let generated := NativeRecoveryEscapeStress.sourceStress initial time.1 time.2 uncovered
    Tendsto (fun index => deriv (NativeEscapeCurrentAction.currentCurve escape (generated.refinement index) direction.succ wave)
      (escape.sample (generated.refinement index))) atTop (𝓝 (momentum initial time wave direction)) := by
  rw [momentum_eq]
  exact NativeRecoveryJointAction.uncovered_current_derivative_tendsto initial time uncovered direction wave

def correctionCoefficient (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  let resolved := complexSharpSupportProjection modes (NativeEndpointVelocityCarrier.wholeVelocity (source initial time).mean)
  (if wave ∈ modes then fourierCurlCoefficient wave (momentum initial time wave) else 0) -
    (nativeFluidConstitutiveVorticityAction (quadraticFlux resolved) wave -
      (nu.coeff * integerWaveViscousMultiplier wave) • fourierCurlCoefficient wave (resolved wave))

theorem correctionCoefficient_eq (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) (wave : IntegerWavevector) :
    correctionCoefficient initial time modes wave = NativeJointStressFilterControl.coefficient modes
      (velocity initial time.1) (stress initial time) wave := by
  unfold correctionCoefficient
  rw [momentum_eq]
  change (if wave ∈ modes then fourierCurlCoefficient wave (NativeRecoveryJointCurrent.momentum initial time wave) else 0) -
    (nativeFluidConstitutiveVorticityAction (quadraticFlux (complexSharpSupportProjection modes
      (NativeEndpointVelocityCarrier.wholeVelocity (mean initial time)))) wave -
        (nu.coeff * integerWaveViscousMultiplier wave) • fourierCurlCoefficient wave
          (complexSharpSupportProjection modes (NativeEndpointVelocityCarrier.wholeVelocity (mean initial time)) wave)) = _
  rw [mean_velocity]
  exact (NativeRecoveryJointAction.correction_from_current_action initial time modes wave).symm

def correctionField (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) : PhysicalSpace → PhysicalSpace :=
  finiteRealComplexFourierField (outputInventory modes) (correctionCoefficient initial time modes)

theorem correctionField_eq (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) : correctionField initial time modes = correction initial time modes := by
  unfold correctionField correction
  rw [NativeJointStressFilterControl.physicalField_eq_finite]
  exact congrArg (finiteRealComplexFourierField (outputInventory modes)) (funext (correctionCoefficient_eq initial time modes))

theorem source_correction_all_order_control (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) : ContDiff ℝ ∞ (correctionField initial time modes) ∧
      ∀ order place, ‖iteratedFDeriv ℝ order (correctionField initial time modes) place‖ ≤
        NativeJointStressFilterControl.spatialBudget modes (budget initial) order := by
  rw [correctionField_eq]
  exact NativeRecoveryJointCurrent.source_correction_all_order_control initial time modes

theorem source_correction_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (correctionField initial time modes)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (correctionField initial time modes)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (NativeJointStressFilterControl.spatialBudget modes (budget initial) order) * volume domain ^ (1 / exponent.toReal) := by
  rw [correctionField_eq]
  exact NativeRecoveryJointCurrent.source_correction_all_order_Lp initial time modes order exponent compact

end
end SaturationMonoid.NavierStokes.NativeRecoveryPairedAction

import H0mework.NavierStokes.SourceUnheated.PrefixPayment
import H0mework.Versions.X.NavierStokes.MacroAction.FiniteMacroGlobal
import H0mework.NavierStokes.Crossing.FrequencySupportExhaustion

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedBandGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open NativeUnheatedPrefixPayment
noncomputable section
variable {nu : Viscosity}

def band (waves : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) : ℝ :=
  ∑ wave ∈ waves, integerWaveNormSq wave.1 * ‖value wave‖ ^ 2

theorem band_nonnegative (waves : Finset NonzeroIntegerWavevector) (value : WholeRestartVelocityEndpointState) :
    0 ≤ band waves value := Finset.sum_nonneg fun wave _ => mul_nonneg (integerWaveNormSq_nonneg wave.1) (sq_nonneg _)

theorem band_continuous (waves : Finset NonzeroIntegerWavevector) : Continuous (band waves) := by
  apply continuous_finsetSum
  intro wave _
  exact ((lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).continuous.norm.pow 2).const_mul _

theorem band_curve_continuous {curve : ℝ → WholeRestartVelocityEndpointState}
    (rows : ∀ wave, Continuous (fun time => curve time wave)) (waves : Finset NonzeroIntegerWavevector) :
    Continuous (fun time => band waves (curve time)) :=
  continuous_finsetSum _ fun wave _ => ((rows wave).norm.pow 2).const_mul _

theorem biot_row_bound (state : ComplexVorticityHilbertState) (wave : NonzeroIntegerWavevector) :
    integerWaveNormSq wave.1 * ‖puncturedWholeVelocityEuclideanState state wave‖ ^ 2 ≤
      biotSavartSerrinConstant * complexCoordinateAmplitudeSq (state wave.1) := by
  change integerWaveNormSq wave.1 * ‖euclideanCoordinateRow (finiteStateVelocityCoefficient state wave.1)‖ ^ 2 ≤ _
  rw [euclideanCoordinateRow_norm_sq]
  have paid := finiteBiotSavartVelocityState_gradientMass_le {wave.1} state
  simpa [finiteStateVorticityEnstrophyMass, finiteStateVorticityCoefficientEnstrophy,
    finiteComplexVorticityState_apply] using paid

theorem band_biot_bound (waves : Finset NonzeroIntegerWavevector) (state : ComplexVorticityHilbertState) :
    band waves (puncturedWholeVelocityEuclideanState state) ≤
      biotSavartSerrinConstant * wholeVorticityEuclideanMass state := by
  classical
  have paid := finiteStateVorticityCoefficientEnstrophy_le_wholeMass (waves.image Subtype.val) state
  have same : (∑ wave ∈ waves, complexCoordinateAmplitudeSq (state wave.1)) =
      finiteStateVorticityCoefficientEnstrophy (waves.image Subtype.val) state := by
    rw [finiteStateVorticityCoefficientEnstrophy, Finset.sum_image]
    intro first _ last _ equal
    exact Subtype.ext equal
  calc
    _ ≤ biotSavartSerrinConstant * ∑ wave ∈ waves, complexCoordinateAmplitudeSq (state wave.1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun wave _ => biot_row_bound state wave
    _ ≤ _ := by rw [same]; exact mul_le_mul_of_nonneg_left paid biotSavartSerrinConstant_nonneg

theorem prefix_band_integrable (seed : GeneratedWholeRestartCurrent nu) (length : ℕ)
    (waves : Finset NonzeroIntegerWavevector) :
    IntervalIntegrable (fun time => band waves (puncturedWholeVelocityEuclideanState
      (wholeRestartPrefixPhysicalTrajectory seed length time))) volume 0 (elapsedTime seed length) :=
  ((band_continuous waves).comp continuous_puncturedWholeVelocityEuclideanState).comp_continuousOn
    (wholeRestartPrefixPhysicalTrajectory_continuousOn seed length) |>.intervalIntegrable_of_Icc (GeneratedWholeRestartCurrent.elapsedTime_nonneg seed length)

theorem prefix_band_integral_bound (seed : GeneratedWholeRestartCurrent nu) (length : ℕ)
    (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..elapsedTime seed length, band waves (puncturedWholeVelocityEuclideanState
      (wholeRestartPrefixPhysicalTrajectory seed length time))) ≤ biotSavartSerrinConstant * budget seed := by
  have paid := intervalIntegral.integral_mono_on (GeneratedWholeRestartCurrent.elapsedTime_nonneg seed length)
    (prefix_band_integrable seed length waves)
    ((prefix_integrable seed length).const_mul biotSavartSerrinConstant)
    (fun time _ => band_biot_bound waves (wholeRestartPrefixPhysicalTrajectory seed length time))
  rw [intervalIntegral.integral_const_mul] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (prefix_integral_bound seed length) biotSavartSerrinConstant_nonneg)

end
end SaturationMonoid.NavierStokes.NativeUnheatedBandGradient

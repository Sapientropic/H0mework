import H0mework.Versions.X.NavierStokes.SourceAction.Flux
import H0mework.NavierStokes.StressAction.Stress

set_option autoImplicit false
open scoped BigOperators ENNReal Matrix

namespace SaturationMonoid.NavierStokes.NativeFullOrderActionMoments

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderFlux NativeFullOrderStress NativeFullOrderSynthesis NativeStressSource

noncomputable section

def stressMomentDensity (order : ℕ) (stress : NativeFluidStressFourierState)
    (output input : Coordinate) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * Complex.normSq (stress wave output input)

def actionMomentDensity (order : ℕ) (stress : NativeFluidStressFourierState)
    (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 *
    complexCoordinateAmplitudeSq (nativeFluidConstitutiveVorticityAction stress wave)

theorem curl_amplitude_le (wave : IntegerWavevector) (row : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (fourierCurlCoefficient wave row) ≤
      integerWaveViscousMultiplier wave * complexCoordinateAmplitudeSq row := by
  have crossBound := complexWavevector_cross_normSq_le wave row
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [fourierCurlCoefficient, complexCoordinateVectorNormSq_smul,
    Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  unfold integerWaveViscousMultiplier
  simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_left crossBound (sq_nonneg (2 * Real.pi))

theorem action_amplitude_le (stress : NativeFluidStressFourierState) (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq (nativeFluidConstitutiveVorticityAction stress wave) ≤
      integerWaveViscousMultiplier wave ^ 2 *
        ∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (stress wave output input) := by
  have curl := curl_amplitude_le wave (nativeFluidStressDivergenceCoefficient stress wave)
  have div := divergence_amplitude_le stress wave
  have nonnegative : 0 ≤ integerWaveViscousMultiplier wave :=
    mul_nonneg (sq_nonneg (2 * Real.pi)) (integerWaveNormSq_nonneg wave)
  have scaled := mul_le_mul_of_nonneg_left div nonnegative
  apply curl.trans
  convert! scaled using 1
  ring

theorem multiplier_square_le (wave : IntegerWavevector) :
    integerWaveViscousMultiplier wave ^ 2 ≤ (2 * Real.pi) ^ 4 * frequencySize wave ^ 4 := by
  have squared := pow_le_pow_left₀ (integerWaveNormSq_nonneg wave) (normSq_le_frequencySize_sq wave) 2
  have scaled := mul_le_mul_of_nonneg_left squared (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) 4)
  unfold integerWaveViscousMultiplier
  convert! scaled using 1 <;> ring

theorem actionMoment_row_le (stress : NativeFluidStressFourierState) (order : ℕ) (wave : IntegerWavevector) :
    actionMomentDensity order stress wave ≤
      (2 * Real.pi) ^ 4 *
        ∑ output : Coordinate, ∑ input : Coordinate, stressMomentDensity (order + 2) stress output input wave := by
  have raw := (action_amplitude_le stress wave).trans
    (mul_le_mul_of_nonneg_right (multiplier_square_le wave)
      (Finset.sum_nonneg fun output _ => Finset.sum_nonneg fun input _ => Complex.normSq_nonneg _))
  have weighted := mul_le_mul_of_nonneg_left raw (sq_nonneg (frequencySize wave ^ order))
  unfold actionMomentDensity stressMomentDensity
  simp only [← Finset.mul_sum]
  convert! weighted using 1
  rw [pow_add]
  ring

theorem constitutive_moment_control (stress : NativeFluidStressFourierState) (order : ℕ) (bound : ℝ)
    (paid : ∀ output input : Coordinate,
      Summable (stressMomentDensity (order + 2) stress output input) ∧
        (∑' wave, stressMomentDensity (order + 2) stress output input wave) ≤ bound) :
    Summable (actionMomentDensity order stress) ∧
      (∑' wave, actionMomentDensity order stress wave) ≤ 9 * (2 * Real.pi) ^ 4 * bound := by
  have totalPaid : Summable fun wave =>
      ∑ output : Coordinate, ∑ input : Coordinate, stressMomentDensity (order + 2) stress output input wave := by
    apply summable_sum
    intro output _
    exact summable_sum fun input _ => (paid output input).1
  have generated := (totalPaid.mul_left ((2 * Real.pi) ^ 4)).of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _))
    (actionMoment_row_le stress order)
  refine ⟨generated, ?_⟩
  have boundAll := generated.tsum_le_tsum (actionMoment_row_le stress order)
    (totalPaid.mul_left ((2 * Real.pi) ^ 4))
  rw [tsum_mul_left, Summable.tsum_finsetSum] at boundAll
  · apply boundAll.trans
    have each (output : Coordinate) :
        (∑' wave, ∑ input : Coordinate, stressMomentDensity (order + 2) stress output input wave) ≤ 3 * bound := by
      rw [Summable.tsum_finsetSum (fun input _ => (paid output input).1)]
      have finite := Finset.sum_le_sum fun input (_ : input ∈ (Finset.univ : Finset Coordinate)) => (paid output input).2
      simpa using finite
    have total := Finset.sum_le_sum fun output (_ : output ∈ (Finset.univ : Finset Coordinate)) => each output
    have scaled := mul_le_mul_of_nonneg_left total (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) 4)
    apply scaled.trans_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro output _
    exact summable_sum fun input _ => (paid output input).1

theorem run_receipt_nonlinear_control (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    let state := (run stackedShortCurrent index).receipt.wholePath time
    (Summable fun wave => (frequencySize wave ^ order) ^ 2 *
      complexCoordinateAmplitudeSq (wholeStateVorticityNonlinearCoefficientAt state wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 *
        complexCoordinateAmplitudeSq (wholeStateVorticityNonlinearCoefficientAt state wave)) ≤
          9 * (2 * Real.pi) ^ 4 * sourceFluxBudget (order + 2) index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have source := constitutive_moment_control (quadraticFlux (wholeBiotSavartVelocityState state)) order
    (sourceFluxBudget (order + 2) index) (fun output input => run_receipt_flux_control (order + 2) index time output input)
  have actual (wave) := quadraticFlux_biotSavart_action state
    ((run stackedShortCurrent index).receipt.wholePath_zero_row time) (wholePath_transverse _ time) wave
  change Summable (actionMomentDensity order (quadraticFlux (wholeBiotSavartVelocityState state))) ∧ _ at source
  unfold actionMomentDensity at source
  simpa only [actual] using source

end
end SaturationMonoid.NavierStokes.NativeFullOrderActionMoments

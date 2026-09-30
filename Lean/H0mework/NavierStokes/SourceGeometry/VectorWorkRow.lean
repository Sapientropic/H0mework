import H0mework.NavierStokes.SourceGeometry.VectorWorkProjection

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry

noncomputable section

def testGramRow (wave : IntegerWavevector) (a : PhysicalSpace) : ℝ :=
  (integerWaveNormSq wave * ‖a‖ ^ 2 - (∑ i, (wave i : ℝ) * a i) ^ 2) /
    integerWaveNormSq wave ^ 3

theorem testGramRow_nonneg (wave : IntegerWavevector) (a : PhysicalSpace) :
    0 ≤ testGramRow wave a := by
  unfold testGramRow
  rw [← waveTestCross_norm]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (pow_nonneg (integerWaveNormSq_nonneg wave) 3)

theorem biot_row_inner_sq_le (wave : IntegerWavevector) (nonzero : wave ≠ 0)
    (a x : PhysicalSpace) (v : ComplexCoordinateVector) :
    inner ℝ a (realComplexFourierMode wave (biotSavartVelocityCoefficient wave v) x) ^ 2 ≤
      (testGramRow wave a / (2 * Real.pi) ^ 2) *
        (integerWaveNormSq wave * complexCoordinateAmplitudeSq v) := by
  have scalarBound := realFourierScalar_sq_le wave
    (complexTest a ⬝ᵥ biotSavartVelocityCoefficient wave v) x
  rw [← realFourier_inner_eq, test_dot_biot wave a v nonzero,
    Complex.normSq_mul, Complex.normSq_div, Complex.normSq_I,
    Complex.normSq_ofReal] at scalarBound
  have rowBound := realTest_dot_norm_sq_le (waveTestCross wave a) v
  rw [waveTestCross_norm] at rowBound
  have scaleNonneg : 0 ≤ 1 / ((2 * Real.pi * integerWaveNormSq wave) *
      (2 * Real.pi * integerWaveNormSq wave)) :=
    div_nonneg (by norm_num) (mul_self_nonneg _)
  have scaled := mul_le_mul_of_nonneg_left rowBound scaleNonneg
  calc
    inner ℝ a (realComplexFourierMode wave (biotSavartVelocityCoefficient wave v) x) ^ 2 ≤
        1 / ((2 * Real.pi * integerWaveNormSq wave) *
          (2 * Real.pi * integerWaveNormSq wave)) *
            Complex.normSq ((fun i => (waveTestCross wave a i : ℂ)) ⬝ᵥ v) := scalarBound
    _ ≤ 1 / ((2 * Real.pi * integerWaveNormSq wave) *
          (2 * Real.pi * integerWaveNormSq wave)) *
        ((integerWaveNormSq wave * ‖a‖ ^ 2 - (∑ i, (wave i : ℝ) * a i) ^ 2) *
          complexCoordinateAmplitudeSq v) := scaled
    _ = _ := by
      unfold testGramRow
      field_simp [integerWaveNormSq_ne_zero nonzero, Real.pi_ne_zero]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal

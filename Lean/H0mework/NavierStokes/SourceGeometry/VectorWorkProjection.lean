import H0mework.NavierStokes.Fourier.ShellSerrinGeometry

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval

noncomputable section

def complexTest (a : PhysicalSpace) : ComplexCoordinateVector := fun i => (a i : ℂ)

theorem complexTest_norm (a : PhysicalSpace) :
    complexCoordinateVectorNormSq (complexTest a) = ‖a‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [complexCoordinateVectorNormSq, complexTest, Complex.normSq_ofReal, pow_two]

theorem realTest_dot_norm_sq_le (b : Coordinate → ℝ) (v : ComplexCoordinateVector) :
    Complex.normSq ((fun i => (b i : ℂ)) ⬝ᵥ v) ≤
      (∑ i, (b i) ^ 2) * complexCoordinateAmplitudeSq v := by
  have realBound := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b (fun i => (v i).re)
  have imagBound := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b (fun i => (v i).im)
  simp only [dotProduct, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  have amp : complexCoordinateAmplitudeSq v =
      (∑ i, (v i).re ^ 2) + ∑ i, (v i).im ^ 2 := by
    simp only [complexCoordinateAmplitudeSq, Complex.normSq_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [amp, mul_add]
  nlinarith only [realBound, imagBound]

theorem realFourier_inner_eq (a : PhysicalSpace) (wave : IntegerWavevector)
    (v : ComplexCoordinateVector) (x : PhysicalSpace) :
    inner ℝ a (realComplexFourierMode wave v x) =
      realComplexScalarFourierMode wave (complexTest a ⬝ᵥ v) x := by
  simp only [PiLp.inner_apply, Real.inner_apply, realComplexFourierMode,
    WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    coefficientReal_apply, coefficientImag_apply, realComplexScalarFourierMode,
    complexTest, dotProduct, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realFourierScalar_sq_le (wave : IntegerWavevector) (v : ℂ) (x : PhysicalSpace) :
    realComplexScalarFourierMode wave v x ^ 2 ≤ Complex.normSq v := by
  have trig := Real.cos_sq_add_sin_sq (integerWavePhase wave x)
  change (integerCosine wave x * v.re - integerSine wave x * v.im) ^ 2 ≤ _
  rw [Complex.normSq_apply]
  change integerCosine wave x ^ 2 + integerSine wave x ^ 2 = 1 at trig
  nlinarith [sq_nonneg (integerSine wave x * v.re + integerCosine wave x * v.im)]

def waveTestCross (wave : IntegerWavevector) (a : PhysicalSpace) : Coordinate → ℝ :=
  (fun i => a i) ⨯₃ (fun i => (wave i : ℝ))

theorem waveTestCross_norm (wave : IntegerWavevector) (a : PhysicalSpace) :
    (∑ i, waveTestCross wave a i ^ 2) =
      integerWaveNormSq wave * ‖a‖ ^ 2 - (∑ i, (wave i : ℝ) * a i) ^ 2 := by
  have h := cross_dot_cross (fun i => a i) (fun i => (wave i : ℝ))
    (fun i => a i) (fun i => (wave i : ℝ))
  have commute : (∑ i : Coordinate, a i * (wave i : ℝ)) = ∑ i, (wave i : ℝ) * a i := by
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [dotProduct, ← pow_two, commute] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [waveTestCross, integerWaveNormSq, mul_comm] using h

theorem waveTestCross_complex (wave : IntegerWavevector) (a : PhysicalSpace) :
    complexTest a ⨯₃ complexWavevector wave = fun i => (waveTestCross wave a i : ℂ) := by
  ext i
  fin_cases i <;> simp [complexTest, complexWavevector, waveTestCross, cross_apply]

theorem test_dot_biot (wave : IntegerWavevector) (a : PhysicalSpace)
    (v : ComplexCoordinateVector) (nonzero : wave ≠ 0) :
    complexTest a ⬝ᵥ biotSavartVelocityCoefficient wave v =
      (Complex.I / ((2 * Real.pi * integerWaveNormSq wave : ℝ) : ℂ)) *
        ((fun i => (waveTestCross wave a i : ℂ)) ⬝ᵥ v) := by
  rw [biotSavartVelocityCoefficient, if_neg nonzero, dotProduct_smul]
  congr 1
  rw [triple_product_permutation, triple_product_permutation, waveTestCross_complex,
    dotProduct_comm]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal

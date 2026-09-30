import H0mework.NavierStokes.Galerkin.StretchingCriticalBound
import H0mework.NavierStokes.Energy.StrongContinuationDifferenceKineticEnergy

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferencePair

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

noncomputable section

private theorem dot_bound (wave : IntegerWavevector) (value : ComplexCoordinateVector) :
    Complex.normSq (complexWavevector wave ⬝ᵥ value) ≤
      integerWaveNormSq wave * complexCoordinateVectorNormSq value := by
  have identity := complexWavevector_cross_normSq wave value
  have positive := complexCoordinateVectorNormSq_nonneg (complexWavevector wave ⨯₃ value)
  linarith

def stretching (left right : ComplexCoordinateVector) (second : IntegerWavevector) :=
  (Complex.I * ((2 * Real.pi : Real) : Complex) *
    (complexWavevector second ⬝ᵥ left)) • biotSavartVelocityCoefficient second right

def transport (left right : ComplexCoordinateVector) (first second : IntegerWavevector) :=
  (Complex.I * ((2 * Real.pi : Real) : Complex) *
    (complexWavevector second ⬝ᵥ biotSavartVelocityCoefficient first left)) • right

theorem bilinear_eq (left right : ComplexVorticityHilbertState) (first second : IntegerWavevector) :
    finiteStateVorticityBilinearPairContribution left right (first, second) =
      stretching (left first) (right second) second -
        transport (left first) (right second) first second := by
  rfl

/-- Biot--Savart cancels the derivative on the transported slot exactly. -/
theorem stretching_sq_le (left right : ComplexCoordinateVector) (second : IntegerWavevector) :
    complexCoordinateAmplitudeSq (stretching left right second) ≤
      complexCoordinateAmplitudeSq left * complexCoordinateAmplitudeSq right := by
  by_cases zero : second = 0
  · subst second
    simpa [stretching, biotSavartVelocityCoefficient, complexCoordinateAmplitudeSq] using
      mul_nonneg (complexCoordinateAmplitudeSq_nonneg left)
        (complexCoordinateAmplitudeSq_nonneg right)
  · have angular := dot_bound second left
    have velocity := biotSavartVelocityCoefficient_normSq_le second right zero
    rw [stretching, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_smul]
    simp only [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul, ← pow_two]
    rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    calc
      _ ≤ (2 * Real.pi) ^ 2 *
          (integerWaveNormSq second * complexCoordinateVectorNormSq left) *
          (complexCoordinateVectorNormSq right / ((2 * Real.pi) ^ 2 * integerWaveNormSq second)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left angular (sq_nonneg _)) velocity
          (complexCoordinateVectorNormSq_nonneg _)
          (mul_nonneg (sq_nonneg _) (mul_nonneg (integerWaveNormSq_nonneg _)
            (complexCoordinateVectorNormSq_nonneg _)))
      _ = _ := by
        field_simp [integerWaveNormSq_ne_zero zero, Real.pi_ne_zero]

private theorem velocity_sq_le (value : ComplexCoordinateVector) (wave : IntegerWavevector) :
    (2 * Real.pi) ^ 2 * complexCoordinateVectorNormSq (biotSavartVelocityCoefficient wave value) ≤
      complexCoordinateVectorNormSq value := by
  by_cases zero : wave = 0
  · subst wave
    simpa [biotSavartVelocityCoefficient, complexCoordinateVectorNormSq] using
      complexCoordinateVectorNormSq_nonneg value
  · have lower := one_le_integerWaveNormSq ⟨wave, zero⟩
    have bound := biotSavartVelocityCoefficient_normSq_le wave value zero
    have denominator : 0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
      exact mul_pos (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)) (integerWaveNormSq_pos zero)
    have paid := (le_div_iff₀ denominator).mp bound
    calc
      _ ≤ ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) *
          complexCoordinateVectorNormSq (biotSavartVelocityCoefficient wave value) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left lower (sq_nonneg _))
          (complexCoordinateVectorNormSq_nonneg _)
      _ = complexCoordinateVectorNormSq (biotSavartVelocityCoefficient wave value) *
          ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) := mul_comm _ _
      _ ≤ _ := paid

/-- Only the reference frequency remains in the mixed transport bound. -/
theorem transport_sq_le (left right : ComplexCoordinateVector) (first second : IntegerWavevector) :
    complexCoordinateAmplitudeSq (transport left right first second) ≤
      integerWaveNormSq second * complexCoordinateAmplitudeSq left *
        complexCoordinateAmplitudeSq right := by
  have angular := dot_bound second (biotSavartVelocityCoefficient first left)
  have velocity := velocity_sq_le left first
  rw [transport, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateVectorNormSq_smul]
  simp only [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul, ← pow_two]
  rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  calc
    _ ≤ (2 * Real.pi) ^ 2 *
        (integerWaveNormSq second *
          complexCoordinateVectorNormSq (biotSavartVelocityCoefficient first left)) *
        complexCoordinateVectorNormSq right :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left angular (sq_nonneg _))
        (complexCoordinateVectorNormSq_nonneg _)
    _ = integerWaveNormSq second * ((2 * Real.pi) ^ 2 *
        complexCoordinateVectorNormSq (biotSavartVelocityCoefficient first left)) *
        complexCoordinateVectorNormSq right := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left velocity (integerWaveNormSq_nonneg _))
      (complexCoordinateVectorNormSq_nonneg _)

private theorem abs_le_roots {value first second third : Real}
    (firstNonneg : 0 ≤ first) (secondNonneg : 0 ≤ second) (thirdNonneg : 0 ≤ third)
    (bound : value ^ 2 ≤ first * second * third) :
    |value| ≤ Real.sqrt first * Real.sqrt second * Real.sqrt third := by
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt firstNonneg, Real.sq_sqrt secondNonneg,
    Real.sq_sqrt thirdNonneg] using bound

theorem stretchingWork_abs_le (test left right : ComplexCoordinateVector)
    (second : IntegerWavevector) :
    |complexCoordinateRealInner test (stretching left right second)| ≤
      Real.sqrt (complexCoordinateAmplitudeSq test) *
        Real.sqrt (complexCoordinateAmplitudeSq left) * Real.sqrt (complexCoordinateAmplitudeSq right) := by
  apply abs_le_roots (complexCoordinateAmplitudeSq_nonneg _)
    (complexCoordinateAmplitudeSq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _)
  have cauchy := complexCoordinateRealInner_sq_le test (stretching left right second)
  have pair := mul_le_mul_of_nonneg_left (stretching_sq_le left right second)
    (complexCoordinateAmplitudeSq_nonneg test)
  simpa only [mul_assoc] using cauchy.trans pair

theorem transportWork_abs_le (test left right : ComplexCoordinateVector)
    (first second : IntegerWavevector) :
    |complexCoordinateRealInner test (transport left right first second)| ≤
      Real.sqrt (complexCoordinateAmplitudeSq test) *
        Real.sqrt (complexCoordinateAmplitudeSq left) *
          Real.sqrt (integerWaveNormSq second * complexCoordinateAmplitudeSq right) := by
  apply abs_le_roots (complexCoordinateAmplitudeSq_nonneg _)
    (complexCoordinateAmplitudeSq_nonneg _)
    (mul_nonneg (integerWaveNormSq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _))
  have cauchy := complexCoordinateRealInner_sq_le test (transport left right first second)
  have pair := mul_le_mul_of_nonneg_left (transport_sq_le left right first second)
    (complexCoordinateAmplitudeSq_nonneg test)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using cauchy.trans pair

end
end SaturationMonoid.NavierStokes.ReferencePair

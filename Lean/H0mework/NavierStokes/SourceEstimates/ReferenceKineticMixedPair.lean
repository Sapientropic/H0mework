import H0mework.NavierStokes.SourceEstimates.ReferenceWork
import H0mework.NavierStokes.SourceEstimates.ReferenceKineticStrain

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceKineticMixed

open Matrix Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger

noncomputable section

private theorem transport_sq_le_kinetic (left right : ComplexCoordinateVector)
    (first second : IntegerWavevector) :
    complexCoordinateAmplitudeSq (ReferencePair.transport left right first second) ≤
      integerWaveViscousMultiplier second *
        (complexCoordinateAmplitudeSq left / integerWaveViscousMultiplier first) *
          complexCoordinateAmplitudeSq right := by
  by_cases nonzero : first ≠ 0
  · have angular := complexWavevector_dot_normSq_le second (biotSavartVelocityCoefficient first left)
    have velocity := biotSavartVelocityCoefficient_normSq_le first left nonzero
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at angular velocity ⊢
    rw [ReferencePair.transport, complexCoordinateVectorNormSq_smul]
    simp only [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, one_mul, ← pow_two]
    calc
      _ ≤ (2 * Real.pi) ^ 2 *
          (integerWaveNormSq second * complexCoordinateVectorNormSq (biotSavartVelocityCoefficient first left)) *
            complexCoordinateVectorNormSq right :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left angular (sq_nonneg _))
          (complexCoordinateVectorNormSq_nonneg _)
      _ ≤ (2 * Real.pi) ^ 2 *
          (integerWaveNormSq second * (complexCoordinateVectorNormSq left /
            ((2 * Real.pi) ^ 2 * integerWaveNormSq first))) * complexCoordinateVectorNormSq right :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left velocity (integerWaveNormSq_nonneg second)) (sq_nonneg _))
          (complexCoordinateVectorNormSq_nonneg _)
      _ = _ := by unfold integerWaveViscousMultiplier; ring
  · have zero : first = 0 := not_ne_iff.mp nonzero
    subst first
    simp [ReferencePair.transport, biotSavartVelocityCoefficient, integerWaveViscousMultiplier,
      integerWaveNormSq, complexCoordinateAmplitudeSq]

def kineticProduct (error : ComplexVorticityHilbertState) (first second : IntegerWavevector) : Real :=
  vorticityRowAmplitude error (first + second) *
    Real.sqrt (complexCoordinateAmplitudeSq (error second) / integerWaveViscousMultiplier second)

theorem derivativeWork_abs_le (reference error : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) :
    |ReferenceWork.derivativeWork reference error first second| ≤
      (2 * Real.pi * Real.sqrt (integerWaveNormSq first) * vorticityRowAmplitude reference first) *
        kineticProduct error first second := by
  have bound := (complexCoordinateRealInner_sq_le (error (first + second))
    (ReferencePair.transport (error second) (reference first) second first)).trans
      (mul_le_mul_of_nonneg_left (transport_sq_le_kinetic (error second) (reference first) second first)
        (complexCoordinateAmplitudeSq_nonneg _))
  have densityNonneg : 0 ≤ complexCoordinateAmplitudeSq (error second) / integerWaveViscousMultiplier second :=
    div_nonneg (complexCoordinateAmplitudeSq_nonneg _) (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (by
    unfold kineticProduct
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (vorticityRowAmplitude_nonneg _ _))
      (mul_nonneg (vorticityRowAmplitude_nonneg _ _) (Real.sqrt_nonneg _)))).mp
  simp only [sq_abs, kineticProduct, mul_pow, Real.sq_sqrt (integerWaveNormSq_nonneg first),
    Real.sq_sqrt densityNonneg, vorticityRowAmplitude_sq]
  unfold ReferenceWork.derivativeWork
  simp only [integerWaveViscousMultiplier, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at bound ⊢
  nlinarith only [bound]

theorem kineticProduct_budget (error : ComplexVorticityHilbertState) (first : IntegerWavevector) :
    Summable (kineticProduct error first) ∧ (∑' second, kineticProduct error first second) ≤
      Real.sqrt (wholeVorticityEuclideanMass error) * Real.sqrt (puncturedWholeVorticityKineticMass error) := by
  let density := fun wave => complexCoordinateAmplitudeSq (error wave) / integerWaveViscousMultiplier wave
  have nonnegative : ∀ wave, 0 ≤ density wave := fun wave => div_nonneg
    (complexCoordinateAmplitudeSq_nonneg _) (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))
  have support : Function.support density ⊆ {wave | wave ≠ (0 : IntegerWavevector)} := by
    intro wave nonzero
    by_contra zero
    have equal : wave = 0 := by simpa using zero
    subst wave
    simp [density, integerWaveViscousMultiplier, integerWaveNormSq] at nonzero
  have densitySum : HasSum density (puncturedWholeVorticityKineticMass error) := by
    apply (hasSum_subtype_iff_of_support_subset support).mp
    exact (summable_puncturedWholeVorticityKineticMass error).hasSum
  have shifted : Summable fun second : IntegerWavevector => vorticityRowAmplitude error (first + second) ^ 2 :=
    (Equiv.addLeft first).summable_iff.mpr (summable_vorticityRowAmplitude_sq error)
  have weighted : Summable fun second => Real.sqrt (density second) ^ 2 := by
    simpa only [Real.sq_sqrt (nonnegative _)] using densitySum.summable
  have cauchy := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun second => vorticityRowAmplitude_nonneg error (first + second)) (fun second => Real.sqrt_nonneg (density second))
    (by simpa only [Real.rpow_two] using shifted) (by simpa only [Real.rpow_two] using weighted)
  have shiftedMass : (∑' second, vorticityRowAmplitude error (first + second) ^ 2) =
      wholeVorticityEuclideanMass error := (Equiv.addLeft first).tsum_eq (fun second => vorticityRowAmplitude error second ^ 2)
  refine ⟨cauchy.1, ?_⟩
  have bound := cauchy.2
  simp only [Real.rpow_two, Real.sq_sqrt (nonnegative _), shiftedMass, densitySum.tsum_eq] at bound
  simpa only [kineticProduct, Real.sqrt_eq_rpow, one_div] using bound

end
end SaturationMonoid.NavierStokes.ReferenceKineticMixed

import H0mework.NavierStokes.Heat.Convergence
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCriticalSerrin

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatQuartetBudget

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

noncomputable section

def velocityAmplitude (x : ComplexVorticityHilbertState) (p : IntegerWavevector) : Real :=
  Real.sqrt (complexCoordinateAmplitudeSq (biotSavartVelocityCoefficient p (x p)))

def coefficient (x : ComplexVorticityHilbertState) (pair : IntegerWavevector × IntegerWavevector) : Real :=
  velocityAmplitude x pair.1 * velocityAmplitude x pair.2

def kernel (x : ComplexVorticityHilbertState)
    (shift : (IntegerWavevector × IntegerWavevector) → IntegerWavevector)
    (pair : IntegerWavevector × IntegerWavevector) (r : IntegerWavevector) : Real :=
  coefficient x pair * (vorticityRowAmplitude x (shift pair + r) * vorticityRowAmplitude x r)

private theorem coefficient_nonneg (x : ComplexVorticityHilbertState)
    (pair : IntegerWavevector × IntegerWavevector) : 0 ≤ coefficient x pair :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem coefficient_budget (x : ComplexVorticityHilbertState)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (x k)) :
    (Summable (coefficient x)) ∧ (∑' pair, coefficient x pair) = wholeStateVelocityMajorant x ^ 2 := by
  have velocity : Summable (velocityAmplitude x) := summable_wholeStateVelocityAmplitude x gradient
  have outer : Summable fun p : IntegerWavevector => ∑' q, velocityAmplitude x p * velocityAmplitude x q := by
    simp only [tsum_mul_left]
    exact velocity.mul_right _
  have total : Summable (coefficient x) :=
    (summable_prod_of_nonneg (coefficient_nonneg x)).2
      ⟨fun p => velocity.mul_left (velocityAmplitude x p), outer⟩
  refine ⟨total, ?_⟩
  rw [total.tsum_prod]
  simp only [coefficient, tsum_mul_left, tsum_mul_right, pow_two]
  rfl

private theorem product_budget (x : ComplexVorticityHilbertState) (shift : IntegerWavevector) :
    (Summable fun r => vorticityRowAmplitude x (shift + r) * vorticityRowAmplitude x r) ∧
      (∑' r, vorticityRowAmplitude x (shift + r) * vorticityRowAmplitude x r) ≤
        wholeVorticityEuclideanMass x := by
  have generated := HeatWholeWork.product_budget x x shift
  refine ⟨generated.1, ?_⟩
  have massNonneg : 0 ≤ wholeVorticityEuclideanMass x := tsum_nonneg fun _ => sq_nonneg _
  simpa only [Real.mul_self_sqrt massNonneg] using generated.2

/-- The shift is only an index map: one complete velocity/velocity/vorticity/vorticity budget pays every quartet incidence. -/
theorem kernel_budget (x : ComplexVorticityHilbertState)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (x k))
    (shift : (IntegerWavevector × IntegerWavevector) → IntegerWavevector) :
    (Summable fun index : (IntegerWavevector × IntegerWavevector) × IntegerWavevector =>
      kernel x shift index.1 index.2) ∧
    (∑' index : (IntegerWavevector × IntegerWavevector) × IntegerWavevector,
      kernel x shift index.1 index.2) ≤ wholeStateVelocityMajorant x ^ 2 * wholeVorticityEuclideanMass x := by
  have coefficients := coefficient_budget x gradient
  have productNonneg (pair : IntegerWavevector × IntegerWavevector) (r : IntegerWavevector) :
      0 ≤ vorticityRowAmplitude x (shift pair + r) * vorticityRowAmplitude x r :=
    mul_nonneg (vorticityRowAmplitude_nonneg _ _) (vorticityRowAmplitude_nonneg _ _)
  have outer : Summable fun pair => ∑' r, kernel x shift pair r := by
    simp only [kernel, tsum_mul_left]
    exact (coefficients.1.mul_right (wholeVorticityEuclideanMass x)).of_nonneg_of_le
      (fun pair => mul_nonneg (coefficient_nonneg x pair) (tsum_nonneg (productNonneg pair)))
      (fun pair => mul_le_mul_of_nonneg_left (product_budget x (shift pair)).2 (coefficient_nonneg x pair))
  have total : Summable fun index : (IntegerWavevector × IntegerWavevector) × IntegerWavevector =>
      kernel x shift index.1 index.2 :=
    (summable_prod_of_nonneg (fun index =>
      mul_nonneg (coefficient_nonneg x index.1) (productNonneg index.1 index.2))).2
      ⟨fun pair => (product_budget x (shift pair)).1.mul_left (coefficient x pair), outer⟩
  refine ⟨total, ?_⟩
  rw [total.tsum_prod]
  calc
    _ ≤ ∑' pair, coefficient x pair * wholeVorticityEuclideanMass x := by
      apply outer.tsum_le_tsum _ (coefficients.1.mul_right _)
      intro pair
      simp only [kernel, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (product_budget x (shift pair)).2 (coefficient_nonneg x pair)
    _ = wholeStateVelocityMajorant x ^ 2 * wholeVorticityEuclideanMass x := by
      rw [tsum_mul_right, coefficients.2]

end
end SaturationMonoid.NavierStokes.HeatQuartetBudget

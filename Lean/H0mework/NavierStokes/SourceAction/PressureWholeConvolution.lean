import H0mework.NavierStokes.FourWave.WholeKernelBudget

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.HeatQuartetBudget

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin

noncomputable section

def convolution (x : ComplexVorticityHilbertState) (k : IntegerWavevector) : Real :=
  ∑' p, velocityAmplitude x p * vorticityRowAmplitude x (k - p)

theorem convolution_summable (x : ComplexVorticityHilbertState)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (x k))
    (k : IntegerWavevector) :
    Summable fun p => velocityAmplitude x p * vorticityRowAmplitude x (k - p) := by
  have velocity : Summable (velocityAmplitude x) := summable_wholeStateVelocityAmplitude x gradient
  apply (velocity.mul_right (Real.sqrt (wholeVorticityEuclideanMass x))).of_nonneg_of_le
  · intro p
    exact mul_nonneg (Real.sqrt_nonneg _) (vorticityRowAmplitude_nonneg _ _)
  · intro p
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.le_sqrt_of_sq_le
    exact (summable_vorticityRowAmplitude_sq x).le_tsum (k - p) (fun _ _ => sq_nonneg _)

private def centerOutput : (IntegerWavevector × (IntegerWavevector × IntegerWavevector)) ≃
    ((IntegerWavevector × IntegerWavevector) × IntegerWavevector) where
  toFun index := (index.2, index.1 - index.2.1)
  invFun index := (index.2 + index.1.1, index.1)
  left_inv index := by ext <;> simp
  right_inv index := by ext <;> simp

private def squareRow (x : ComplexVorticityHilbertState) (k : IntegerWavevector)
    (pair : IntegerWavevector × IntegerWavevector) : Real :=
  (velocityAmplitude x pair.1 * vorticityRowAmplitude x (k - pair.1)) *
    (velocityAmplitude x pair.2 * vorticityRowAmplitude x (k - pair.2))

private theorem centered_row (x : ComplexVorticityHilbertState) (k p q : IntegerWavevector) :
    kernel x (fun pair => pair.1 - pair.2) (p, q) (k - p) = squareRow x k (p, q) := by
  have incidence : (p - q) + (k - p) = k - q := by abel
  simp only [kernel, coefficient, squareRow, incidence]
  ring

/-- The complete scalar convolution is square-summable by the same quartet occurrence budget. -/
theorem convolution_square_budget (x : ComplexVorticityHilbertState)
    (gradient : Summable fun k => integerWaveNormSq k * complexCoordinateAmplitudeSq (x k)) :
    (Summable fun k => convolution x k ^ 2) ∧
      (∑' k, convolution x k ^ 2) ≤ wholeStateVelocityMajorant x ^ 2 * wholeVorticityEuclideanMass x := by
  have original := kernel_budget x gradient (fun pair => pair.1 - pair.2)
  have centered : Summable fun index : IntegerWavevector × (IntegerWavevector × IntegerWavevector) =>
      squareRow x index.1 index.2 := by
    have generated := centerOutput.summable_iff.mpr original.1
    apply generated.congr
    intro index
    exact centered_row x index.1 index.2.1 index.2.2
  have nonnegative (index : IntegerWavevector × (IntegerWavevector × IntegerWavevector)) :
      0 ≤ squareRow x index.1 index.2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vorticityRowAmplitude_nonneg _ _))
      (mul_nonneg (Real.sqrt_nonneg _) (vorticityRowAmplitude_nonneg _ _))
  have slices := (summable_prod_of_nonneg nonnegative).1 centered
  have square (k : IntegerWavevector) : (∑' pair, squareRow x k pair) = convolution x k ^ 2 := by
    have generated := (convolution_summable x gradient k).tsum_mul_tsum
      (convolution_summable x gradient k) (slices.1 k)
    simpa only [squareRow, convolution, pow_two] using generated.symm
  have squares : Summable fun k => convolution x k ^ 2 := slices.2.congr square
  refine ⟨squares, ?_⟩
  have sourceSum := centerOutput.tsum_eq
    (fun index => kernel x (fun pair => pair.1 - pair.2) index.1 index.2)
  have recognized : (fun index : IntegerWavevector × (IntegerWavevector × IntegerWavevector) =>
      kernel x (fun pair => pair.1 - pair.2) (centerOutput index).1 (centerOutput index).2) =
        (fun index => squareRow x index.1 index.2) := by
    funext index
    exact centered_row x index.1 index.2.1 index.2.2
  rw [recognized, centered.tsum_prod] at sourceSum
  simp_rw [square] at sourceSum
  rw [sourceSum]
  exact original.2

end
end SaturationMonoid.NavierStokes.HeatQuartetBudget

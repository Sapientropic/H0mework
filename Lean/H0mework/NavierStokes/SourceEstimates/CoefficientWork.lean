import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow
import H0mework.NavierStokes.Galerkin.StretchingCriticalBound

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.CoefficientWork

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound

noncomputable section

def value (left right : ComplexVorticityHilbertState) : Real :=
  ∑' wave, complexCoordinateRealInner (left wave) (right wave)

theorem row_abs_le (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    |complexCoordinateRealInner (left wave) (right wave)| ≤
      vorticityRowAmplitude left wave * vorticityRowAmplitude right wave := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
    (vorticityRowAmplitude_nonneg left wave) (vorticityRowAmplitude_nonneg right wave))).mp
  rw [sq_abs, mul_pow, vorticityRowAmplitude_sq, vorticityRowAmplitude_sq]
  exact complexCoordinateRealInner_sq_le _ _

private theorem product_bound (left right : ComplexVorticityHilbertState) :
    Summable (fun wave => vorticityRowAmplitude left wave * vorticityRowAmplitude right wave) ∧
      (∑' wave, vorticityRowAmplitude left wave * vorticityRowAmplitude right wave) ≤
        Real.sqrt (wholeVorticityEuclideanMass left) * Real.sqrt (wholeVorticityEuclideanMass right) := by
  have bound := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (vorticityRowAmplitude_nonneg left) (vorticityRowAmplitude_nonneg right)
    (by simpa only [Real.rpow_two] using summable_vorticityRowAmplitude_sq left)
    (by simpa only [Real.rpow_two] using summable_vorticityRowAmplitude_sq right)
  refine ⟨bound.1, ?_⟩
  simpa [Real.rpow_two, one_div, Real.sqrt_eq_rpow, wholeVorticityEuclideanMass] using bound.2

theorem summable (left right : ComplexVorticityHilbertState) :
    Summable fun wave => complexCoordinateRealInner (left wave) (right wave) := by
  have absolute := (product_bound left right).1.of_nonneg_of_le
    (fun wave => abs_nonneg _) (row_abs_le left right)
  exact summable_abs_iff.mp absolute

theorem abs_le (left right : ComplexVorticityHilbertState) :
    |value left right| ≤ Real.sqrt (wholeVorticityEuclideanMass left) *
      Real.sqrt (wholeVorticityEuclideanMass right) := by
  have absolute := summable_abs_iff.mpr (summable left right)
  have triangle : |value left right| ≤ ∑' wave, |complexCoordinateRealInner (left wave) (right wave)| := by
    simpa only [value, Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (f := fun wave => complexCoordinateRealInner (left wave) (right wave))
      (by simpa only [Real.norm_eq_abs] using absolute)
  exact triangle.trans ((absolute.tsum_le_tsum (row_abs_le left right)
    (product_bound left right).1).trans (product_bound left right).2)

theorem square_le_product_split {x y z epsilon : Real} (xNonneg : 0 ≤ x) (yNonneg : 0 ≤ y)
    (zNonneg : 0 ≤ z) (epsilonPos : 0 < epsilon) (bound : x ^ 2 ≤ y * z) :
    x ≤ epsilon * y + z / (4 * epsilon) := by
  apply (sq_le_sq₀ xNonneg (by positivity : 0 ≤ epsilon * y + z / (4 * epsilon))).mp
  apply bound.trans
  have identity : y * z = 4 * (epsilon * y) * (z / (4 * epsilon)) := by
    field_simp
  rw [identity]
  nlinarith [sq_nonneg (epsilon * y - z / (4 * epsilon))]


end
end SaturationMonoid.NavierStokes.CoefficientWork

import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.TranslatedDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.PhysicsCore.Stage10.StaticGreen
open MeasureTheory Filter
open scoped Topology
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb GlobalSource SourceFiniteData ContinuousGradient
noncomputable section

def bilinearLinear (left right : MultiIndex) (point : Point) : Point →L[ℝ] ℝ :=
  ∑ axis : Fin 3, firstBilinear sourceTerms densityMatrix left right axis point • ContinuousLinearMap.proj axis

theorem source_bilinear_hasFDerivAt (left right : MultiIndex) (point : Point) :
    HasFDerivAt (bilinear sourceTerms densityMatrix left right) (bilinearLinear left right point) point := by
  have regular := (bilinear_contDiff sourceTerms densityMatrix left right 1).differentiable (by norm_num) point
  have derivative : fderiv ℝ (bilinear sourceTerms densityMatrix left right) point = bilinearLinear left right point := by
    apply ContinuousLinearMap.ext
    intro vector
    rw [linear_apply_coordinates]
    simp only [bilinearLinear, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro axis _
    rw [fderiv_coordinate _ point axis regular _ (bilinear_coordinate_derivative sourceTerms densityMatrix left right point axis)]
  rw [← derivative]
  exact regular.hasFDerivAt

theorem translated_source_nonnegative (left right : MultiIndex) (radius : ℝ) (point : Point) :
    0 ≤ translatedSourceEnvelope left right radius point := by
  unfold translatedSourceEnvelope
  apply Finset.sum_nonneg
  intro first _
  apply Finset.sum_nonneg
  intro second _
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (sourceOrbitalBound left first).coe_nonneg)
    (translated_orbital_nonnegative _ _ _ _)

def translatedDerivativeEnvelope (left right : MultiIndex) (radius : ℝ) (point : Point) : ℝ :=
  ∑ axis : Fin 3, (translatedSourceEnvelope (raise left axis) right radius point +
    translatedSourceEnvelope left (raise right axis) radius point)

theorem translated_first_bound (left right : MultiIndex) (radius : ℝ) (position point : Point)
    (inside : ‖position‖ ≤ radius) (axis : Fin 3) :
    |firstBilinear sourceTerms densityMatrix left right axis (position-point)| ≤
      translatedSourceEnvelope (raise left axis) right radius point +
        translatedSourceEnvelope left (raise right axis) radius point :=
  (abs_add_le _ _).trans (add_le_add
    (translated_source_bound (raise left axis) right radius position point inside)
    (translated_source_bound left (raise right axis) radius position point inside))

theorem translated_derivative_bound (left right : MultiIndex) (radius : ℝ) (position point : Point)
    (inside : ‖position‖ ≤ radius) :
    ‖bilinearLinear left right (position-point)‖ ≤ translatedDerivativeEnvelope left right radius point := by
  have nonnegative (axis : Fin 3) : 0 ≤ translatedSourceEnvelope (raise left axis) right radius point +
      translatedSourceEnvelope left (raise right axis) radius point :=
    add_nonneg (translated_source_nonnegative _ _ _ _) (translated_source_nonnegative _ _ _ _)
  unfold translatedDerivativeEnvelope
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun axis _ => nonnegative axis))
  intro vector
  simp only [bilinearLinear, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ axis : Fin 3, (translatedSourceEnvelope (raise left axis) right radius point +
        translatedSourceEnvelope left (raise right axis) radius point)*‖vector‖ := by
      apply Finset.sum_le_sum
      intro axis _
      rw [abs_mul]
      exact mul_le_mul (translated_first_bound left right radius position point inside axis)
        (norm_le_pi_norm vector axis) (abs_nonneg _) (nonnegative axis)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem translated_derivative_kernel_integrable (left right : MultiIndex) (radius : ℝ) :
    Integrable (fun point => translatedDerivativeEnvelope left right radius point*kernel point) := by
  unfold translatedDerivativeEnvelope
  simp_rw [Finset.sum_mul, add_mul]
  exact integrable_finsetSum _ (fun axis _ =>
    (translated_source_kernel_integrable (raise left axis) right radius).add
      (translated_source_kernel_integrable left (raise right axis) radius))

end
end SaturationMonoid.PhysicsCore.Stage10.StaticGreen

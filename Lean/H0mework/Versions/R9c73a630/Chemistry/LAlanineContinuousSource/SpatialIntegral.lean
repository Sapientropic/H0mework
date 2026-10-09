import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSource.ChartInjectivity
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart

open SourceGaussianModel SourceSignedEvaluator SourceRK4Replay SourceCellGeometry IntervalParameterMap
open ContinuousParameterMap Set MeasureTheory

noncomputable section
attribute [local irreducible] parameterJacobian parameterMap

def spatialPatch : Set Point := parameterMap 0 4 '' cellDomain
def spatialLaplacianIntegral : ℝ :=
  ∫ x in spatialPatch, laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix x

theorem linearDet_eq_matrixDet (p : Point) :
    (parameterJacobian 0 4 p).det = (jacobianMatrix 0 4 p).det :=
  (LinearMap.det_toMatrix' (parameterJacobian 0 4 p).toLinearMap).symm

theorem source_determinant_lower : (1 / 100000 : ℚ) < reportedTargetDeterminant.1 := by decide +kernel

theorem actual_jacobian_positive (fields : SourceFieldLaw) (p : Point) (inside : p ∈ cellDomain) :
    0 < (jacobianMatrix 0 4 p).det := by
  have range := (final_jacobian_contains fields p inside).1
  rw [target_determinant_recomputed] at range
  have positive : (0 : ℝ) < (reportedTargetDeterminant.1 : ℝ) := by
    exact_mod_cast (by linarith [source_determinant_lower] : (0 : ℚ) < reportedTargetDeterminant.1)
  exact positive.trans_le range

/-- Injectivity and the Jacobian sign are derived from the same generated stage enclosures. -/
theorem spatial_integral_eq_parameter_integral (fields : SourceFieldLaw) :
    spatialLaplacianIntegral = ∫ p in cellDomain, signedLaplacian 0 4 p := by
  unfold spatialLaplacianIntegral spatialPatch
  have measured : MeasurableSet cellDomain := measurableSet_Icc
  refine (integral_image_eq_integral_abs_det_fderiv_smul volume measured
    (fun p _ => (parameterMap_hasFDerivAt 0 4 p).hasFDerivWithinAt) (actual_chart_injOn fields) _).trans ?_
  apply setIntegral_congr_fun measurableSet_Icc
  intro p hp
  dsimp only
  rw [linearDet_eq_matrixDet, abs_of_pos (actual_jacobian_positive fields p hp)]
  simp only [signedLaplacian, smul_eq_mul, mul_comm]

theorem spatial_integral_enclosure (fields : SourceFieldLaw) :
    Holds (integralPair generatedTargetIntegrand cellLowerQ cellUpperQ) spatialLaplacianIntegral := by
  rw [spatial_integral_eq_parameter_integral fields]
  exact cell_integral_from_source_fields fields

theorem source_integral_lower :
    (-112 / 100000000000 : ℚ) < (integralPair reportedTargetIntegrand cellLowerQ cellUpperQ).1 := by
  decide +kernel

theorem source_integral_upper :
    (integralPair reportedTargetIntegrand cellLowerQ cellUpperQ).2 < (-25 / 100000000000 : ℚ) := by
  decide +kernel

theorem spatial_integral_strictly_negative (fields : SourceFieldLaw) :
    (-112 / 100000000000 : ℝ) < spatialLaplacianIntegral ∧
      spatialLaplacianIntegral < (-25 / 100000000000 : ℝ) := by
  have h := spatial_integral_enclosure fields
  rw [target_integrand_recomputed] at h
  have lower : (-112 / 100000000000 : ℝ) <
      ((integralPair reportedTargetIntegrand cellLowerQ cellUpperQ).1 : ℝ) := by
    exact_mod_cast source_integral_lower
  have upper : ((integralPair reportedTargetIntegrand cellLowerQ cellUpperQ).2 : ℝ) <
      (-25 / 100000000000 : ℝ) := by exact_mod_cast source_integral_upper
  constructor
  · exact lower.trans_le h.1
  · exact h.2.trans_lt upper

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceChart

import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixAllFields
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSource.SpatialIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

open SourceGaussianModel SourceRK4Replay SourceCellGeometry SourceChart
open ContinuousParameterMap Set MeasureTheory

noncomputable section

theorem actual_spatial_injOn : InjOn (parameterMap 0 4) cellDomain :=
  actual_chart_injOn all_actual_fields

theorem actual_spatial_jacobian_positive (p : Point) (inside : p ∈ cellDomain) :
    0 < (jacobianMatrix 0 4 p).det :=
  actual_jacobian_positive all_actual_fields p inside

theorem actual_spatial_integral_commutes :
    spatialLaplacianIntegral = ∫ p in cellDomain, signedLaplacian 0 4 p :=
  spatial_integral_eq_parameter_integral all_actual_fields

theorem actual_spatial_integral_bounds :
    (-112 / 100000000000 : ℝ) < spatialLaplacianIntegral ∧
      spatialLaplacianIntegral < (-25 / 100000000000 : ℝ) :=
  spatial_integral_strictly_negative all_actual_fields

theorem actual_spatial_volume_positive : 0 < volume spatialPatch := by
  apply pos_iff_ne_zero.mpr
  intro zero
  have erased : spatialLaplacianIntegral = 0 := setIntegral_measure_zero _ zero
  have negative := actual_spatial_integral_bounds.2
  rw [erased] at negative
  norm_num at negative

def actualSpatialPatchClosure : Prop :=
  SourceFieldLaw ∧
    InjOn (parameterMap 0 4) cellDomain ∧
    (∀ p ∈ cellDomain, 0 < (jacobianMatrix 0 4 p).det) ∧
    spatialLaplacianIntegral = (∫ p in cellDomain, signedLaplacian 0 4 p) ∧
    ((-112 / 100000000000 : ℝ) < spatialLaplacianIntegral ∧
      spatialLaplacianIntegral < (-25 / 100000000000 : ℝ)) ∧
    0 < volume spatialPatch

/-- The original source generates the whole four-step spatial patch certificate without a field-law input. -/
theorem sourceGeneratedActualSpatialPatch : actualSpatialPatchClosure :=
  ⟨all_actual_fields, actual_spatial_injOn, actual_spatial_jacobian_positive,
    actual_spatial_integral_commutes, actual_spatial_integral_bounds, actual_spatial_volume_positive⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFieldMatrices

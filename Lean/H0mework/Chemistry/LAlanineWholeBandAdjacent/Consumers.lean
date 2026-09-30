import H0mework.Chemistry.LAlanineWholeBandAdjacent.Additivity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel SourceFiniteData WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter Set MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem joint_laplacian_integrable : IntegrableOn (laplacian sourceTerms densityMatrix) jointImage :=
  continuous_joint_integrable _ (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn

theorem joint_laplacian_no_double_count :
    (∫ x in jointImage,laplacian sourceTerms densityMatrix x) =
      (∫ x in sourceParameterMap 0 '' cellDomain 0,laplacian sourceTerms densityMatrix x) +
        ∫ x in sourceParameterMap 1 '' cellDomain 1,laplacian sourceTerms densityMatrix x :=
  joint_integral_eq_sum _ joint_laplacian_integrable

theorem joint_bilinear_integrable (left right : MultiIndex) :
    IntegrableOn (bilinear sourceTerms densityMatrix left right) jointImage :=
  continuous_joint_integrable _ (bilinear_contDiff sourceTerms densityMatrix left right 0).continuous.continuousOn

theorem joint_bilinear_no_double_count (left right : MultiIndex) :
    (∫ x in jointImage,bilinear sourceTerms densityMatrix left right x) =
      (∫ x in sourceParameterMap 0 '' cellDomain 0,bilinear sourceTerms densityMatrix left right x) +
        ∫ x in sourceParameterMap 1 '' cellDomain 1,bilinear sourceTerms densityMatrix left right x :=
  joint_integral_eq_sum _ (joint_bilinear_integrable left right)

theorem rightImage_volume_pos : 0 < volume (sourceParameterMap 1 '' cellDomain 1) := by
  have measuredDomain : MeasurableSet (cellDomain 1) := (domain_eq_Icc 1).symm ▸ measurableSet_Icc
  have derivative (p : Point) (_ : p ∈ cellDomain 1) :
      HasFDerivWithinAt (sourceParameterMap 1) (jointJacobian p) (cellDomain 1) p :=
    (jointMap_hasFDerivWithinAt p).mono subset_union_right
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume measuredDomain derivative
    WholeBandCell1Actual.cell1_map_injOn]
  apply pos_iff_ne_zero.mpr
  intro zero
  have measured := aemeasurable_ofReal_abs_det_fderivWithin volume measuredDomain derivative
  have aeZero := (lintegral_eq_zero_iff' measured).mp zero
  have outside : ∀ᵐ p ∂(volume : Measure Point), p ∉ cellDomain 1 := by
    filter_upwards [(ae_restrict_iff' measuredDomain).mp aeZero] with p hp
    intro inside
    have positive : 0 < ENNReal.ofReal |(jointJacobian p).det| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr (jointJacobian_det_ne_zero p (Or.inr inside)))
    exact positive.ne' (hp inside)
  have null : volume (cellDomain 1) = 0 := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using outside
  exact (Measure.measure_pos_of_nonempty_interior volume (domain_interior_nonempty 1)).ne' null

theorem joint_volume_strictly_exceeds_left :
    volume (sourceParameterMap 0 '' cellDomain 0) < volume jointImage := by
  rw [joint_volume_eq_sum]
  exact ENNReal.lt_add_right leftImage_compact.measure_lt_top.ne rightImage_volume_pos.ne'

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

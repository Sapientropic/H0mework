import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.Seam

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandGeometry WholeBandContinuation WholeBandContinuationParameter Set MeasureTheory
noncomputable section

theorem leftImage_compact : IsCompact (sourceParameterMap 0 '' cellDomain 0) :=
  ((domain_eq_Icc 0).symm ▸ isCompact_Icc).image_of_continuousOn
    (jointMap_continuousOn.mono subset_union_left)

theorem rightImage_compact : IsCompact (sourceParameterMap 1 '' cellDomain 1) :=
  ((domain_eq_Icc 1).symm ▸ isCompact_Icc).image_of_continuousOn
    (jointMap_continuousOn.mono subset_union_right)

theorem actual_images_aeDisjoint :
    AEDisjoint volume (sourceParameterMap 0 '' cellDomain 0) (sourceParameterMap 1 '' cellDomain 1) :=
  actual_intersection_volume_zero

theorem joint_volume_eq_sum : volume jointImage =
    volume (sourceParameterMap 0 '' cellDomain 0) + volume (sourceParameterMap 1 '' cellDomain 1) := by
  rw [jointImage_eq_union]
  exact measure_union₀ rightImage_compact.isClosed.measurableSet.nullMeasurableSet actual_images_aeDisjoint

theorem joint_integral_eq_sum (g : Point → ℝ) (integrable : IntegrableOn g jointImage) :
    (∫ x in jointImage,g x) =
      (∫ x in sourceParameterMap 0 '' cellDomain 0,g x) +
        ∫ x in sourceParameterMap 1 '' cellDomain 1,g x := by
  rw [jointImage_eq_union] at integrable ⊢
  exact setIntegral_union₀ actual_images_aeDisjoint
    rightImage_compact.isClosed.measurableSet.nullMeasurableSet
    (integrable.mono_set subset_union_left) (integrable.mono_set subset_union_right)

theorem continuous_joint_integrable (g : Point → ℝ) (continuous : ContinuousOn g jointImage) :
    IntegrableOn g jointImage := continuous.integrableOn_compact jointImage_compact

theorem continuous_joint_integral_eq_sum (g : Point → ℝ) (continuous : ContinuousOn g jointImage) :
    (∫ x in jointImage,g x) =
      (∫ x in sourceParameterMap 0 '' cellDomain 0,g x) +
        ∫ x in sourceParameterMap 1 '' cellDomain 1,g x :=
  joint_integral_eq_sum g (continuous_joint_integrable g continuous)

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

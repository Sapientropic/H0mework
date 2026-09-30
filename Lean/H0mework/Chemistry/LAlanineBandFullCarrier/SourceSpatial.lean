import H0mework.Chemistry.LAlanineBandFullCarrier.SourceFlow
import H0mework.Chemistry.LAlanineBandSpatial.AtlasInverse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry WholeBandContinuationParameter
open WholeBandAtlas Set MeasureTheory
noncomputable section

theorem complete_parameter_carrier : material.parameterCarrier = Icc (cellLower 0) (cellUpper 31) := bandDomain_eq_Icc

theorem original_map_restrictions (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c) :
    material.parameterMap p = material.maps c p := bandMap_on_cell c p inside

theorem same_physical_carrier : material.parameterMap '' material.parameterCarrier = material.physicalCarrier := bandMap_image

theorem whole_carrier_continuous : ContinuousOn material.parameterMap material.parameterCarrier :=
  bandMap_continuousOn fields bounds

theorem whole_carrier_no_fold : InjOn material.parameterMap material.parameterCarrier := bandMap_injOn fields positive

def physical_carrier_homeomorph : material.parameterCarrier ≃ₜ material.physicalCarrier :=
  carrierHomeomorph fields bounds positive

theorem physical_inverse_preserves_occurrence (p : material.parameterCarrier) :
    (physical_carrier_homeomorph p).val = material.parameterMap p.val ∧
    physical_carrier_homeomorph.symm (physical_carrier_homeomorph p) = p :=
  ⟨carrierHomeomorph_is_actual fields bounds positive p,physical_carrier_homeomorph.symm_apply_apply p⟩

theorem positive_finite_volume : 0 < volume material.physicalCarrier ∧ volume material.physicalCarrier < ⊤ :=
  ⟨band_volume_pos fields bounds positive,bandImage_volume_lt_top fields bounds⟩

theorem complete_volume_account : volume material.physicalCarrier =
    ∑ c : FullBandCell,∫⁻ p in material.domains c, ENNReal.ofReal |(material.jacobians c p).det| :=
  band_volume_eq_jacobians fields bounds positive

theorem complete_spatial_integral (g : Point → ℝ) (integrable : IntegrableOn g material.physicalCarrier) :
    (∫ x in material.physicalCarrier,g x) = ∑ c : FullBandCell,
      ∫ p in material.domains c, |(material.jacobians c p).det| • g (material.maps c p) :=
  band_integral_commutes fields bounds positive g integrable

theorem full_D3_bilinear_additivity (left right : MultiIndex) :
    (∫ x in material.physicalCarrier,bilinear sourceTerms material.density left right x) =
      ∑ c : FullBandCell,∫ x in cellImage c,bilinear sourceTerms material.density left right x :=
  band_bilinear_additivity fields bounds positive left right

theorem actual_overlap_no_double_count (c d : FullBandCell) (different : c ≠ d) :
    volume ((material.maps c '' material.domains c) ∩ (material.maps d '' material.domains d)) = 0 :=
  cellImage_overlap_null fields bounds positive c d different

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

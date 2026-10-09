import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.MatrixAllFields
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.SpatialVolume

/-! The complete 65-field source family discharges every input of the full-cell spatial consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSpatial

open SourceGaussianModel SourceSignedEvaluator WholeCellPartition WholeCellReplay
open ContinuousParameterMap Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- Generated analytic facts for the fixed original cell, not caller-supplied admission conditions. -/
structure WholeCellClosure : Prop where
  fields : SourceFieldLaw
  coverage : fullDomain = ⋃ q : Quarter, quarterDomain q
  quartersNonempty : ∀ q : Quarter, (quarterDomain q).Nonempty
  chart : InjOn (parameterMap 0 4) fullDomain
  jacobianPositive : ∀ p ∈ fullDomain, 0 < (jacobianMatrix 0 4 p).det
  spatialCommuting : fullLaplacianIntegral = fullSignedIntegral
  signedPartition : fullLaplacianIntegral = ∑ q : Quarter, quarterSignedIntegral q
  signedEnclosure : Holds fullIntegralInterval fullLaplacianIntegral
  signedStrict : (-623 / 10000000000 : ℝ) < fullLaplacianIntegral ∧
    fullLaplacianIntegral < (-39 / 10000000000 : ℝ)
  volumeEnclosure : Holds fullVolumeInterval (volume.real fullPatch)
  volumeStrict : (293 / 10000000000 : ℝ) < volume.real fullPatch ∧
    volume.real fullPatch < (741 / 10000000000 : ℝ)
  sourceSupport : fullPatch ⊆ ContinuousGradient.sourceCube
  oldPatchRetained : SourceChart.spatialPatch ⊆ fullPatch
  compact : IsCompact fullPatch
  nonempty : fullPatch.Nonempty
  integrable : IntegrableOn (laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix) fullPatch

/-- No field, chart, integral, volume or endpoint certificate is an input to this producer. -/
theorem sourceGeneratedWholeCellClosure : WholeCellClosure where
  fields := WholeCellMatrix.all_actual_fields
  coverage := fullDomain_eq_iUnion_quarters
  quartersNonempty := quarter_nonempty
  chart := actual_chart_injOn WholeCellMatrix.all_actual_fields
  jacobianPositive := full_jacobian_positive WholeCellMatrix.all_actual_fields
  spatialCommuting := full_spatial_integral_commutes WholeCellMatrix.all_actual_fields
  signedPartition := full_spatial_integral_eq_four WholeCellMatrix.all_actual_fields
  signedEnclosure := full_spatial_integral_enclosure WholeCellMatrix.all_actual_fields
  signedStrict := full_spatial_integral_strict WholeCellMatrix.all_actual_fields
  volumeEnclosure := full_volume_enclosure WholeCellMatrix.all_actual_fields
  volumeStrict := full_volume_strict WholeCellMatrix.all_actual_fields
  sourceSupport := fullPatch_subset_sourceCube WholeCellMatrix.all_actual_fields
  oldPatchRetained := old_spatial_patch_subset
  compact := fullPatch_compact
  nonempty := fullPatch_nonempty
  integrable := fullPatch_laplacian_integrable

end
end LAlanine40K2025.BasinRefinement.WholeCellSpatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

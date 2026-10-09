import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowQuantitative.ActualBounds
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowConservation.SourceSpatialBalance

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel SourceFiniteData TrueFlowGeometry TrueFlowConservation WholeCellBoundary
open Set MeasureTheory
noncomputable section

theorem true_spatial_laplacian_integrable :
    IntegrableOn (laplacian sourceTerms densityMatrix) truePatch :=
  (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact
    truePatch_compact

theorem true_spatial_laplacian_bounds :
    (-(3 / 4) : ℝ) * volume.real truePatch ≤
        (∫ x in truePatch, laplacian sourceTerms densityMatrix x) ∧
      (∫ x in truePatch, laplacian sourceTerms densityMatrix x) ≤
        (-(1 / 4) : ℝ) * volume.real truePatch := by
  constructor
  · exact setIntegral_ge_of_const_le_real truePatch_measurable truePatch_volume_lt_top.ne
      (fun x hx => (truePatch_laplacian_bounds x hx).1.le) true_spatial_laplacian_integrable
  · have bound := setIntegral_mono_on true_spatial_laplacian_integrable
      (integrableOn_const (C := (-(1 / 4) : ℝ)) truePatch_volume_lt_top.ne)
      truePatch_measurable (fun x hx => (truePatch_laplacian_bounds x hx).2.le)
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using bound

theorem true_spatial_laplacian_neg :
    (∫ x in truePatch, laplacian sourceTerms densityMatrix x) < 0 := by
  have positive : 0 < volume.real truePatch :=
    ENNReal.toReal_pos truePatch_volume_pos.ne' truePatch_volume_lt_top.ne
  exact true_spatial_laplacian_bounds.2.trans_lt (mul_neg_of_neg_of_pos (by norm_num) positive)

theorem true_net_cap_flux_bounds :
    (-(3 / 4) : ℝ) * volume.real truePatch ≤
        (∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p) ∧
      (∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p) ≤
        (-(1 / 4) : ℝ) * volume.real truePatch := by
  rw [← true_spatial_laplacian_eq_cap_flux]
  exact true_spatial_laplacian_bounds

theorem true_net_cap_flux_neg :
    (∫ p in faceDomain 2, actualCapFlux true p + actualCapFlux false p) < 0 := by
  rw [← true_spatial_laplacian_eq_cap_flux]
  exact true_spatial_laplacian_neg

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

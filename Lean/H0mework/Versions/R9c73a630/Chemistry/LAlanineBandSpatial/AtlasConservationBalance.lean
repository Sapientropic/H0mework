import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasConservationSlices
import H0mework.Chemistry.LAlanineTrueFlowConservation.CalculusBoxFubini

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter WholeBandConservation WholeCellBoundary Set MeasureTheory
noncomputable section

theorem capFlux_sum_integrable (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) : IntegrableOn (fun p => flux c (2,true) p + flux c (2,false) p) (domain c 2) := by
  have inner := _root_.LAlanineTrueFlowConservation.integrable_box_time (cellLower c) (cellUpper c) (laplacianPullback c)
    (domain_eq_Icc c ▸ laplacianPullback_integrable fields bounds positive c)
  change IntegrableOn (fun p => ∫ t in Icc (-(1/2 : ℝ)) (1/2),laplacianPullback c ((2 : Fin 3).insertNth t p)) (domain c 2) at inner
  exact inner.congr_fun (actual_slice_integral_eq_caps fields bounds c) measurableSet_Icc

theorem cell_spatial_laplacian_eq_cap_flux (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) :
    (∫ x in cellImage c,laplacian sourceTerms densityMatrix x) =
      ∫ p in domain c 2,flux c (2,true) p + flux c (2,false) p := by
  rw [cell_integral_commutes fields bounds positive]
  have orientation : (∫ p in cellDomain c,|(trueJacobian c p).det| • laplacian sourceTerms densityMatrix (sourceParameterMap c p)) =
      ∫ p in cellDomain c,laplacianPullback c p :=
    setIntegral_congr_fun (domain_measurable c) fun p inside => by
      simp only [laplacianPullback,abs_of_pos (actualJacobian_det_pos c (fields c) (bounds c) (positive c) p inside),smul_eq_mul]
  rw [orientation,domain_eq_Icc]
  rw [_root_.LAlanineTrueFlowConservation.integral_box_time (cellLower c) (cellUpper c) (laplacianPullback c)
    (domain_eq_Icc c ▸ laplacianPullback_integrable fields bounds positive c)]
  exact setIntegral_congr_fun measurableSet_Icc (actual_slice_integral_eq_caps fields bounds c)

/-- The full original physical carrier pays its spatial balance through its actual cap patches. -/
theorem band_spatial_laplacian_eq_cap_flux (fields : Fields) (bounds : Bounds) (positive : Normals) :
    (∫ x in bandImage,laplacian sourceTerms densityMatrix x) =
      ∑ c : FullBandCell,∫ p in domain c 2,flux c (2,true) p + flux c (2,false) p := by
  rw [band_integral_sum fields bounds positive _ (band_laplacian_integrable fields bounds)]
  simp_rw [cell_spatial_laplacian_eq_cap_flux fields bounds positive]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Faces
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

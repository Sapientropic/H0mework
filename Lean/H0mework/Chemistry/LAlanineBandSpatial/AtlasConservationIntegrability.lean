import H0mework.Chemistry.LAlanineBandSpatial.AtlasIntegrals
import H0mework.Chemistry.LAlanineBandContinuation.ConservationOrientation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter WholeBandConservation Set MeasureTheory
noncomputable section

theorem band_laplacian_integrable (fields : Fields) (bounds : Bounds) :
    IntegrableOn (laplacian sourceTerms densityMatrix) bandImage :=
  (laplacian_contDiff sourceTerms densityMatrix 0).continuous.continuousOn.integrableOn_compact
    (bandImage_compact fields bounds)

theorem band_bilinear_integrable (fields : Fields) (bounds : Bounds) (left right : MultiIndex) :
    IntegrableOn (bilinear sourceTerms densityMatrix left right) bandImage :=
  (bilinear_contDiff sourceTerms densityMatrix left right 0).continuous.continuousOn.integrableOn_compact
    (bandImage_compact fields bounds)

theorem band_bilinear_additivity (fields : Fields) (bounds : Bounds) (positive : Normals)
    (left right : MultiIndex) :
    (∫ x in bandImage,bilinear sourceTerms densityMatrix left right x) =
      ∑ c : FullBandCell,∫ x in cellImage c,bilinear sourceTerms densityMatrix left right x :=
  band_integral_sum fields bounds positive _ (band_bilinear_integrable fields bounds left right)

def laplacianPullback (c : FullBandCell) (p : Point) : ℝ :=
  (trueJacobian c p).det * laplacian sourceTerms densityMatrix (sourceParameterMap c p)

theorem laplacianPullback_integrable (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) : IntegrableOn (laplacianPullback c) (cellDomain c) := by
  have original := (band_laplacian_integrable fields bounds).mono_set (cellImage_subset_band c)
  have changed := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (domain_measurable c)
    (WholeBandContinuationParameter.actualMap_hasFDerivWithinAt c (fields c) (bounds c))
    (sourceParameterMap_injOn c (fields c) (positive c)) (laplacian sourceTerms densityMatrix)).mp original
  apply changed.congr_fun _ (domain_measurable c)
  intro p inside
  simp only [laplacianPullback,abs_of_pos (actualJacobian_det_pos c (fields c) (bounds c) (positive c) p inside),smul_eq_mul]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

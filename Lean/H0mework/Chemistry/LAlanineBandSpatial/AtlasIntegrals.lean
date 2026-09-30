import H0mework.Chemistry.LAlanineBandSpatial.AtlasImages
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter Set MeasureTheory Filter
open scoped ENNReal BigOperators
noncomputable section

theorem cell_integral_commutes (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (g : Point → ℝ) :
    (∫ x in cellImage c, g x) = ∫ p in cellDomain c, |(trueJacobian c p).det| • g (sourceParameterMap c p) :=
  integral_image_eq_integral_abs_det_fderiv_smul volume (domain_measurable c)
    (actualMap_hasFDerivWithinAt c (fields c) (bounds c))
    (sourceParameterMap_injOn c (fields c) (positive c)) g

theorem cell_lintegral_commutes (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) (g : Point → ℝ≥0∞) :
    (∫⁻ x in cellImage c, g x) =
      ∫⁻ p in cellDomain c, ENNReal.ofReal |(trueJacobian c p).det| * g (sourceParameterMap c p) :=
  lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (domain_measurable c)
    (actualMap_hasFDerivWithinAt c (fields c) (bounds c))
    (sourceParameterMap_injOn c (fields c) (positive c)) g

theorem cell_volume_eq_jacobian (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) :
    volume (cellImage c) = ∫⁻ p in cellDomain c, ENNReal.ofReal |(trueJacobian c p).det| :=
  (lintegral_abs_det_fderiv_eq_addHaar_image volume (domain_measurable c)
    (actualMap_hasFDerivWithinAt c (fields c) (bounds c))
    (sourceParameterMap_injOn c (fields c) (positive c))).symm

theorem band_volume_sum (fields : Fields) (bounds : Bounds) (positive : Normals) :
    volume bandImage = ∑ c : FullBandCell, volume (cellImage c) := by
  simpa only [bandImage,tsum_fintype] using
    measure_iUnion₀ (cellImages_ae_disjoint fields bounds positive)
      (fun c => (cellImage_measurable fields bounds c).nullMeasurableSet)

theorem band_lintegral_sum (fields : Fields) (bounds : Bounds) (positive : Normals)
    (g : Point → ℝ≥0∞) : (∫⁻ x in bandImage, g x) = ∑ c : FullBandCell, ∫⁻ x in cellImage c, g x := by
  simpa only [bandImage,tsum_fintype] using
    lintegral_iUnion₀ (fun c => (cellImage_measurable fields bounds c).nullMeasurableSet)
      (cellImages_ae_disjoint fields bounds positive) g

theorem band_integral_sum (fields : Fields) (bounds : Bounds) (positive : Normals)
    (g : Point → ℝ) (integrable : IntegrableOn g bandImage) :
    (∫ x in bandImage, g x) = ∑ c : FullBandCell, ∫ x in cellImage c, g x := by
  rw [bandImage,Measure.restrict_iUnion_ae (cellImages_ae_disjoint fields bounds positive)
    (fun c => (cellImage_measurable fields bounds c).nullMeasurableSet),Measure.sum_fintype]
  exact integral_finsetSum_measure (fun c _ => integrable.mono_set (cellImage_subset_band c))

theorem band_integral_commutes (fields : Fields) (bounds : Bounds) (positive : Normals)
    (g : Point → ℝ) (integrable : IntegrableOn g bandImage) :
    (∫ x in bandImage, g x) = ∑ c : FullBandCell,
      ∫ p in cellDomain c, |(trueJacobian c p).det| • g (sourceParameterMap c p) := by
  rw [band_integral_sum fields bounds positive g integrable]
  simp_rw [cell_integral_commutes fields bounds positive]

theorem band_volume_eq_jacobians (fields : Fields) (bounds : Bounds) (positive : Normals) :
    volume bandImage = ∑ c : FullBandCell,
      ∫⁻ p in cellDomain c, ENNReal.ofReal |(trueJacobian c p).det| := by
  rw [band_volume_sum fields bounds positive]
  simp_rw [cell_volume_eq_jacobian fields bounds positive]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

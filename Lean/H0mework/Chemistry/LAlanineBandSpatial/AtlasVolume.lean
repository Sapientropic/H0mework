import H0mework.Chemistry.LAlanineBandSpatial.AtlasIntegrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter Set MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem cell_volume_pos (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c : FullBandCell) : 0 < volume (cellImage c) := by
  rw [cell_volume_eq_jacobian fields bounds positive c]
  apply pos_iff_ne_zero.mpr
  intro zero
  have measured := aemeasurable_ofReal_abs_det_fderivWithin volume (domain_measurable c)
    (actualMap_hasFDerivWithinAt c (fields c) (bounds c))
  have aeZero := (lintegral_eq_zero_iff' measured).mp zero
  have outside : ∀ᵐ p ∂(volume : Measure Point), p ∉ cellDomain c := by
    filter_upwards [(ae_restrict_iff' (domain_measurable c)).mp aeZero] with p hp
    intro inside
    have positiveDet : 0 < ENNReal.ofReal |(trueJacobian c p).det| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr (trueJacobian_det_ne_zero c (fields c) (bounds c) (positive c) p inside))
    exact positiveDet.ne' (hp inside)
  have null : volume (cellDomain c) = 0 := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using outside
  exact (Measure.measure_pos_of_nonempty_interior volume (domain_interior_nonempty c)).ne' null

theorem band_volume_pos (fields : Fields) (bounds : Bounds) (positive : Normals) : 0 < volume bandImage :=
  (cell_volume_pos fields bounds positive 0).trans_le (measure_mono (cellImage_subset_band 0))

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

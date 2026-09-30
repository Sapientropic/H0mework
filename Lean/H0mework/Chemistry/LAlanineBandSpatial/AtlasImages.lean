import H0mework.Chemistry.LAlanineBandSpatial.AtlasSource
import H0mework.Chemistry.LAlanineBandContinuation.ParameterNondegenerate
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter WholeBandContinuationDifferential Set MeasureTheory
noncomputable section

abbrev Fields := ∀ c : FullBandCell, ∀ d, DirectionFields c d
abbrev Bounds := ∀ c : FullBandCell, CellBounds c
abbrev Normals := ∀ c : FullBandCell, PositiveNormalReports c

def cellImage (c : FullBandCell) : Set Point := sourceParameterMap c '' cellDomain c
/-- Every chart lands in the original physical Point carrier, including actual shared seams. -/
def bandImage : Set Point := ⋃ c : FullBandCell, cellImage c

theorem cellMap_continuousOn (fields : Fields) (bounds : Bounds) (c : FullBandCell) :
    ContinuousOn (sourceParameterMap c) (cellDomain c) :=
  fun p hp => (actualMap_hasFDerivWithinAt c (fields c) (bounds c) p hp).continuousWithinAt

theorem cellImage_compact (fields : Fields) (bounds : Bounds) (c : FullBandCell) : IsCompact (cellImage c) :=
  (domain_compact c).image_of_continuousOn (cellMap_continuousOn fields bounds c)

theorem cellImage_measurable (fields : Fields) (bounds : Bounds) (c : FullBandCell) :
    MeasurableSet (cellImage c) := (cellImage_compact fields bounds c).isClosed.measurableSet

theorem cellImage_nonempty (c : FullBandCell) : (cellImage c).Nonempty :=
  (cellDomain_nonempty c).image (sourceParameterMap c)

theorem cellImage_subset_band (c : FullBandCell) : cellImage c ⊆ bandImage := subset_iUnion cellImage c

theorem bandImage_compact (fields : Fields) (bounds : Bounds) : IsCompact bandImage :=
  isCompact_iUnion (cellImage_compact fields bounds)

theorem bandImage_measurable (fields : Fields) (bounds : Bounds) : MeasurableSet bandImage :=
  (bandImage_compact fields bounds).isClosed.measurableSet

theorem bandImage_nonempty : bandImage.Nonempty := (cellImage_nonempty 0).mono (cellImage_subset_band 0)

theorem bandImage_volume_lt_top (fields : Fields) (bounds : Bounds) : volume bandImage < ⊤ :=
  (bandImage_compact fields bounds).measure_lt_top

theorem cellImage_intersection (fields : Fields) (positive : Normals) (c d : FullBandCell) :
    cellImage c ∩ cellImage d = sourceParameterMap c '' (cellDomain c ∩ cellDomain d) :=
  actual_images_intersection c d (fields c) (fields d) (positive c) (positive d)

theorem cellImage_overlap_null (fields : Fields) (bounds : Bounds) (positive : Normals)
    (c d : FullBandCell) (different : c ≠ d) : volume (cellImage c ∩ cellImage d) = 0 := by
  rw [cellImage_intersection fields positive c d]
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun p hp => ((actualMap_hasFDerivWithinAt c (fields c) (bounds c) p hp.1).differentiableWithinAt.mono
      inter_subset_left)) (source_overlap_volume_zero c d different)

theorem cellImages_ae_disjoint (fields : Fields) (bounds : Bounds) (positive : Normals) :
    Pairwise (fun c d => AEDisjoint volume (cellImage c) (cellImage d)) :=
  cellImage_overlap_null fields bounds positive

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

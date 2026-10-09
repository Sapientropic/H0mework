import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFullCarrier.SourceSpatial
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasSeamRegular

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
open SourceGaussianModel SourceFiniteData WholeBandSource WholeBandAtlas WholeCellBoundary Set MeasureTheory
noncomputable section

theorem regular_actual_faces (c : FullBandCell) (face : Face) (u : FacePoint) (inside : u ∈ Faces.domain c face.1) :
    Module.finrank ℝ (LinearMap.range (Faces.derivative c face u).toLinearMap) = 2 ∧ Faces.orientedArea c face u ≠ 0 :=
  ⟨Faces.derivative_rank_two fields bounds positive c face u inside,Faces.area_ne_zero fields bounds positive c face u inside⟩

theorem actual_side_flux_zero (c : FullBandCell) (face : Face) (u : FacePoint)
    (inside : u ∈ Faces.domain c face.1) (side : face.1 ≠ 2) : Faces.flux c face u = 0 :=
  Faces.side_flux_zero fields bounds c face u inside side

theorem actual_caps_oriented (c : FullBandCell) (u : FacePoint) (inside : u ∈ Faces.domain c 2) :
    0 < Faces.flux c (2,true) u ∧ Faces.flux c (2,false) u < 0 :=
  ⟨Faces.upper_cap_positive fields bounds positive c u inside,Faces.lower_cap_negative fields bounds positive c u inside⟩

theorem whole_spatial_conservation :
    (∫ x in material.physicalCarrier,laplacian sourceTerms material.density x) =
      ∑ c : FullBandCell,∫ p in Faces.domain c 2,Faces.flux c (2,true) p + Faces.flux c (2,false) p :=
  Faces.band_spatial_laplacian_eq_cap_flux fields bounds positive

theorem original_seams_are_actual (s : Seams.Seam) :
    cellImage (Seams.leftCell s) ∩ cellImage (Seams.rightCell s) = Seams.actualImage s ∧
    (Seams.actualImage s).Nonempty ∧ volume (Seams.actualImage s) = 0 :=
  ⟨Seams.actual_intersection fields positive s,Seams.actualImage_nonempty s,Seams.actualImage_volume_zero fields bounds positive s⟩

theorem original_seam_tangents (s : Seams.Seam) (u : FacePoint) (inside : u ∈ Seams.domain) :
    Seams.leftDerivative s u = Seams.rightDerivative s u ∧
    Module.finrank ℝ (LinearMap.range (Seams.leftDerivative s u).toLinearMap) = 2 :=
  ⟨Seams.actual_tangential_derivatives_agree fields bounds s u inside,Seams.actual_rank_two fields bounds positive s u inside⟩

theorem actual_seam_area_cancellation (s : Seams.Seam) (u : FacePoint) (inside : u ∈ Seams.domain) :
    Faces.orientedArea (Seams.leftCell s) (1,true) u + Faces.orientedArea (Seams.rightCell s) (1,false) u = 0 :=
  Seams.actual_face_area_cancellation fields bounds s u inside

theorem actual_seam_flux_cancellation (s : Seams.Seam) (u : FacePoint) (inside : u ∈ Seams.domain) :
    Faces.flux (Seams.leftCell s) (1,true) u + Faces.flux (Seams.rightCell s) (1,false) u = 0 :=
  Seams.actual_face_flux_cancellation fields bounds s u inside

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

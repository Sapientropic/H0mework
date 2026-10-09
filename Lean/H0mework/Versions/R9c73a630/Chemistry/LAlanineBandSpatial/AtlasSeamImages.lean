import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandSpatial.AtlasSeamDerivative

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation WholeCellBoundary Set MeasureTheory
noncomputable section

theorem cells_ordered (s : Seam) : leftCell s < rightCell s := by
  change s.val < s.val+1
  omega

theorem parameter_image_eq_source_overlap (s : Seam) :
    parameter s '' domain = cellDomain (leftCell s) ∩ cellDomain (rightCell s) := by
  ext p
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨parameter_left s u hu,parameter_right s u hu⟩
  · intro hp
    have v : p 1 = coordinate s := overlap_on_original_face _ _ (cells_ordered s) p hp
    refine ⟨![p 0,p 2],?_,?_⟩
    · constructor <;> intro i <;> fin_cases i
      · exact hp.1.1.1
      · exact hp.1.2.2.1
      · exact hp.1.1.2
      · exact hp.1.2.2.2
    · funext i
      fin_cases i
      · rfl
      · exact v.symm
      · rfl

def actualImage (s : Seam) : Set Point := leftMap s '' domain

theorem actual_intersection (fields : Fields) (positive : Normals) (s : Seam) :
    cellImage (leftCell s) ∩ cellImage (rightCell s) = actualImage s := by
  rw [cellImage_intersection fields positive,← parameter_image_eq_source_overlap,image_image]
  rfl

theorem actualImage_nonempty (s : Seam) : (actualImage s).Nonempty := domain_nonempty.image (leftMap s)

theorem actualImage_volume_zero (fields : Fields) (bounds : Bounds) (positive : Normals) (s : Seam) :
    volume (actualImage s) = 0 := by
  rw [← actual_intersection fields positive]
  exact cellImage_overlap_null fields bounds positive _ _ (ne_of_lt (cells_ordered s))

theorem actualImage_in_carrier (s : Seam) : actualImage s ⊆ bandImage := by
  rintro p ⟨u,hu,rfl⟩
  apply cellImage_subset_band (leftCell s)
  exact ⟨parameter s u,parameter_left s u hu,rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

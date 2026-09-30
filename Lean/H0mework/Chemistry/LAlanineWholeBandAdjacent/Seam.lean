import H0mework.Chemistry.LAlanineWholeBandAdjacent.Spatial

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentFlow

open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandCell1Actual WholeBandAdjacentGeometry Set MeasureTheory
noncomputable section

def sourceSeam : Set Point := cellDomain 0 ∩ cellDomain 1
def actualSeam : Set Point := jointMap '' sourceSeam

theorem sourceSeam_nonempty : sourceSeam.Nonempty := cell0_cell1_seam_nonempty
theorem actualSeam_nonempty : actualSeam.Nonempty := sourceSeam_nonempty.image jointMap

theorem sourceSeam_volume_zero : volume sourceSeam = 0 := by
  have subset : sourceSeam ⊆ Icc (![0,(cellV 0 1 : ℝ),-(1/2 : ℝ)] : Point)
      ![1,(cellV 0 1 : ℝ),(1/2 : ℝ)] := by
    intro p hp
    rcases (cell0_cell1_domain_intersection p).mp hp with ⟨alpha,v,time⟩
    constructor <;> intro i <;> fin_cases i
    · exact alpha.1
    · exact v.ge
    · exact time.1
    · exact alpha.2
    · exact v.le
    · exact time.2
  apply measure_mono_null subset
  rw [Real.volume_Icc_pi]
  exact Finset.prod_eq_zero_iff.mpr ⟨(1 : Fin 3), Finset.mem_univ _, by simp⟩

theorem actualSeam_volume_zero : volume actualSeam = 0 := by
  apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun p _ => ((jointMap_hasFDerivWithinAt p).differentiableWithinAt.mono
      (inter_subset_left.trans subset_union_left))) sourceSeam_volume_zero

theorem actual_intersection_eq_seam :
    (sourceParameterMap 0 '' cellDomain 0) ∩ (sourceParameterMap 1 '' cellDomain 1) = actualSeam :=
  actual_images_intersection 0 1 cell0_source_fields cell1_source_fields
    cell0_positive_reports cell1_positive_reports

theorem actual_intersection_volume_zero :
    volume ((sourceParameterMap 0 '' cellDomain 0) ∩ (sourceParameterMap 1 '' cellDomain 1)) = 0 := by
  rw [actual_intersection_eq_seam]
  exact actualSeam_volume_zero

end
end LAlanine40K2025.BasinRefinement.AdjacentFlow
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

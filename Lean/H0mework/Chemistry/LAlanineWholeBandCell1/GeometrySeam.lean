import H0mework.Chemistry.LAlanineBandGeometry.Cells
import H0mework.Chemistry.LAlanineWholeBandCell0.GeometryCell0

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAdjacentGeometry

open SourceGaussianModel WholeBandSource WholeBandGeometry Set
noncomputable section

theorem cell0_cell1_literal_seam : cellV 0 1 = cellV 1 0 := by decide +kernel

theorem cell1_seed_same_formula : cellSeed 1 = cellSeed 0 := rfl

theorem cell0_cell1_domain_intersection (p : Point) :
    p ∈ cellDomain 0 ∩ cellDomain 1 ↔
      p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = (cellV 0 1 : ℝ) ∧ p 2 ∈ Icc (-(1/2 : ℝ)) (1/2) := by
  constructor
  · intro both
    refine ⟨both.1.1, le_antisymm both.1.2.1.2 ?_, both.1.2.2⟩
    rw [cell0_cell1_literal_seam]
    exact both.2.2.1.1
  · rintro ⟨alpha, seam, time⟩
    have leftWidth : (cellV 0 0 : ℝ) < cellV 0 1 := Rat.cast_lt.mpr (source_cells_in_segments 0).2.1
    have rightWidth : (cellV 1 0 : ℝ) < cellV 1 1 := Rat.cast_lt.mpr (source_cells_in_segments 1).2.1
    constructor
    · exact ⟨alpha, by simpa only [seam, Set.mem_Icc] using And.intro leftWidth.le le_rfl, time⟩
    · refine ⟨alpha, ?_, time⟩
      rw [seam, cell0_cell1_literal_seam]
      exact ⟨le_rfl, rightWidth.le⟩

theorem cell0_cell1_seam_nonempty : (cellDomain 0 ∩ cellDomain 1).Nonempty := by
  refine ⟨![0, (cellV 0 1 : ℝ), 0], (cell0_cell1_domain_intersection _).mpr ?_⟩
  exact ⟨by change (0 : ℝ) ∈ Icc (0 : ℝ) 1; norm_num,
    rfl, by change (0 : ℝ) ∈ Icc (-(1/2 : ℝ)) (1/2); norm_num⟩

theorem cell1_rawMap_same_formula (p : Point) :
    TrueFlowDifferential.rawFlow (cellSeed 1 p) (p 2) = WholeBandCell0Geometry.cell0ParameterMap p := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandAdjacentGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

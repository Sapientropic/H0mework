import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.ActualFull
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.GeometryTransverse
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell1.GeometrySeam
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandRegression.ContinuationPaid

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Actual

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandTransverse WholeBandAdjacentGeometry TrueFlowDifferential Set
noncomputable section

theorem cell1_positive_reports : PositiveNormalReports 1 := by
  intro d i
  exact (by norm_num : (0 : ℚ) < 1/20).trans (all_cell1_normal_lower d i).2

theorem cell1_map_injOn : InjOn (sourceParameterMap 1) (cellDomain 1) :=
  sourceParameterMap_injOn 1 cell1_source_fields cell1_positive_reports

theorem cell0_cell1_actual_meeting (p : WholeBandActual.Cell0Point) (q : Cell1Point) (a b : Time) :
    rawFlow (cellSeed 0 p.val) a = rawFlow (cellSeed 1 q.val) b ↔
      p.val 0 = q.val 0 ∧ p.val 1 = q.val 1 ∧ (a : ℝ) = b :=
  actual_meeting_classification 0 1 cell0_source_fields cell1_source_fields
    cell0_positive_reports cell1_positive_reports p.val q.val p.property q.property a b

def cell1_actualImage : Set Point := sourceParameterMap 1 '' cellDomain 1

theorem cell1_actualImage_nonempty : cell1_actualImage.Nonempty :=
  (cellDomain_nonempty 1).image (sourceParameterMap 1)

theorem cell0_cell1_actual_intersection :
    (WholeBandCell0Geometry.cell0ParameterMap '' cellDomain 0) ∩ cell1_actualImage =
      WholeBandCell0Geometry.cell0ParameterMap ''
        {p : Point | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = (cellV 0 1 : ℝ) ∧ p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)} := by
  have generated := actual_images_intersection 0 1 cell0_source_fields cell1_source_fields
    cell0_positive_reports cell1_positive_reports
  have sourceSeam : cellDomain 0 ∩ cellDomain 1 =
      {p : Point | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = (cellV 0 1 : ℝ) ∧ p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)} :=
    Set.ext cell0_cell1_domain_intersection
  simpa only [cell0_same_actual_map, sourceSeam, cell1_actualImage] using generated

theorem cell0_cell1_actual_intersection_nonempty :
    ((WholeBandCell0Geometry.cell0ParameterMap '' cellDomain 0) ∩ cell1_actualImage).Nonempty := by
  have generated := actual_images_intersection 0 1 cell0_source_fields cell1_source_fields
    cell0_positive_reports cell1_positive_reports
  change ((sourceParameterMap 0 '' cellDomain 0) ∩ (sourceParameterMap 1 '' cellDomain 1)).Nonempty
  rw [generated]
  exact cell0_cell1_seam_nonempty.image (sourceParameterMap 0)

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Actual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

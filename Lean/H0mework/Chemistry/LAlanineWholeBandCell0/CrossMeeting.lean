import H0mework.Chemistry.LAlanineWholeBandCell0.GeometryCell0
import H0mework.Chemistry.LAlanineTrueFlowGeometry.SpatialImage

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCrossGeometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandActual WholeBandCell0Geometry
open TrueFlowGeometry TrueFlowDifferential TrueTubeActual TrueTubeWholeActual WholeCellPartition Set
noncomputable section

theorem cell16_source_bounds :
    fullLowerQ = ![0, cellV 16 0, -(1/2)] ∧ fullUpperQ = ![1, cellV 16 1, 1/2] := by
  constructor <;> funext i <;> fin_cases i <;> decide +kernel

theorem cell16_domain_is_original : cellDomain 16 = fullDomain := by
  ext p
  change (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV 16 0 : ℝ) (cellV 16 1) ∧
    p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)) ↔
    (∀ i, (fullLowerQ i : ℝ) ≤ p i) ∧ (∀ i, p i ≤ (fullUpperQ i : ℝ))
  rw [cell16_source_bounds.1, cell16_source_bounds.2]
  constructor
  · intro h
    constructor <;> intro i <;> fin_cases i
    · simpa using h.1.1
    · simpa using h.2.1.1
    · simpa using h.2.2.1
    · simpa using h.1.2
    · simpa using h.2.1.2
    · simpa using h.2.2.2
  · intro h
    exact ⟨⟨by simpa using h.1 0, by simpa using h.2 0⟩,
      ⟨by simpa using h.1 1, by simpa using h.2 1⟩,
      ⟨by simpa using h.1 2, by simpa using h.2 2⟩⟩

theorem cell0_cell16_actual_meeting_classification (p : Cell0Point) (q : BandPoint) (a b : Time) :
    rawFlow (cellSeed 0 p.val) a = fullFlow q b ↔
      p.val 0 = q.val 0 ∧ p.val 1 = q.val 1 ∧ (a : ℝ) = b := by
  have original : q.val ∈ cellDomain 16 := cell16_domain_is_original.symm ▸ q.property
  change rawFlow (cellSeed 0 p.val) a = rawFlow (cellSeed 16 q.val) b ↔ _
  rw [rawFlow_meeting_classification _ _ (cell_seed_plane_zero 0 p.val)
    (cell_seed_plane_zero 16 q.val) (cell0_plane_strictMono p) (fullFlow_plane_strictMono q) a b,
    cell_seed_eq_iff_coordinates 0 16 p.val q.val p.property original]
  exact and_assoc

theorem cell0_cell16_source_separation : cellV 0 1 < cellV 16 0 := by decide +kernel

theorem cell0_cell16_actual_ne (p : Cell0Point) (q : BandPoint) (a b : Time) :
    rawFlow (cellSeed 0 p.val) a ≠ fullFlow q b := by
  intro meeting
  have coordinates := (cell0_cell16_actual_meeting_classification p q a b).mp meeting
  have original : q.val ∈ cellDomain 16 := cell16_domain_is_original.symm ▸ q.property
  have gap : (cellV 0 1 : ℝ) < cellV 16 0 := Rat.cast_lt.mpr cell0_cell16_source_separation
  have separated := lt_of_le_of_lt p.property.2.1.2 (gap.trans_le original.2.1.1)
  exact separated.ne coordinates.2.1

end
end LAlanine40K2025.BasinRefinement.WholeBandCrossGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

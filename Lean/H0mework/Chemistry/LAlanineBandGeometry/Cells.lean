import H0mework.Chemistry.LAlanineBandGeometry.Seed
import H0mework.Chemistry.LAlanineBandSource.Restriction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeometry

open SourceGaussianModel ContinuousSeed WholeBandSource Set
noncomputable section

theorem source_cells_in_segments : ∀ c : FullBandCell,
    knotCoordinate (firstKnot (cellSegment c)) ≤ cellV c 0 ∧
    cellV c 0 < cellV c 1 ∧ cellV c 1 ≤ knotCoordinate (lastKnot (cellSegment c)) := by
  decide +kernel

def cellDomain (c : FullBandCell) : Set Point :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (cellV c 0 : ℝ) (cellV c 1) ∧
    p 2 ∈ Icc (-(1/2 : ℝ)) (1/2)}

def cellSeed (c : FullBandCell) : Point → Point :=
  bandSeed (cellSegment c) (Geometry.Source.epsilon 0)

theorem cell_parameter_in_segment (c : FullBandCell) (p : Point) (inside : p ∈ cellDomain c) :
    p 1 ∈ Icc (knotCoordinate (firstKnot (cellSegment c)) : ℝ)
      (knotCoordinate (lastKnot (cellSegment c))) :=
  ⟨(Rat.cast_le.mpr (source_cells_in_segments c).1).trans inside.2.1.1,
    inside.2.1.2.trans (Rat.cast_le.mpr (source_cells_in_segments c).2.2)⟩

theorem cellDomain_nonempty (c : FullBandCell) : (cellDomain c).Nonempty := by
  refine ⟨![0, (cellV c 0 : ℝ), 0], ?_⟩
  change 0 ∈ Icc (0 : ℝ) 1 ∧ (cellV c 0 : ℝ) ∈ Icc (cellV c 0 : ℝ) (cellV c 1) ∧
    0 ∈ Icc (-(1/2 : ℝ)) (1/2)
  refine ⟨by norm_num, ⟨le_rfl, Rat.cast_le.mpr (source_cells_in_segments c).2.1.le⟩, by norm_num⟩

/-- Exact classification on all 32 source cells, including their shared seams. -/
theorem cell_seed_eq_iff_coordinates (c d : FullBandCell) (p q : Point)
    (hp : p ∈ cellDomain c) (hq : q ∈ cellDomain d) :
    cellSeed c p = cellSeed d q ↔ p 0 = q 0 ∧ p 1 = q 1 :=
  seed_eq_iff_coordinates (cellSegment c) (cellSegment d) p q
    (cell_parameter_in_segment c p hp) (cell_parameter_in_segment d q hq)

theorem seam_seed_agrees (c d : FullBandCell) (p : Point)
    (hc : p ∈ cellDomain c) (hd : p ∈ cellDomain d) : cellSeed c p = cellSeed d p :=
  (cell_seed_eq_iff_coordinates c d p p hc hd).mpr ⟨rfl,rfl⟩

theorem distinct_coordinates_not_folded (c d : FullBandCell) (p q : Point)
    (hp : p ∈ cellDomain c) (hq : q ∈ cellDomain d)
    (different : p 0 ≠ q 0 ∨ p 1 ≠ q 1) : cellSeed c p ≠ cellSeed d q := by
  intro same
  have coordinates := (cell_seed_eq_iff_coordinates c d p q hp hq).mp same
  rcases different with h | h
  · exact h coordinates.1
  · exact h coordinates.2

theorem cell16_seed_is_original : cellSeed 16 = ContinuousParameterMap.initialMap 0 4 := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

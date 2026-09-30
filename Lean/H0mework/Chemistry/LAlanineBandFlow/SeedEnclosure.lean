import H0mework.Chemistry.LAlanineBandFlow.SeedSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandSeed

open SourceGaussianModel SourceSignedEvaluator ContinuousSeed WholeBandSource WholeBandGeometry Set
noncomputable section

def cellFraction (c : FullBandCell) (v : ℝ) : ℝ :=
  (v - cellV c 0) / ((cellV c 1 : ℝ) - cellV c 0)

theorem cellFraction_mem (c : FullBandCell) (v : ℝ) (hv : v ∈ Icc (cellV c 0 : ℝ) (cellV c 1)) :
    cellFraction c v ∈ Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (cellV c 1 : ℝ) - cellV c 0 :=
    sub_pos.mpr (Rat.cast_lt.mpr (source_cells_in_segments c).2.1)
  exact ⟨div_nonneg (sub_nonneg.mpr hv.1) hpos.le,
    (div_le_one hpos).mpr (sub_le_sub_right hv.2 _)⟩

theorem subcell_interpolate (values : Geometry.Data.Knot → ℚ) (c : FullBandCell) (v : ℝ) :
    interpolate values (cellSegment c) v =
      (1-cellFraction c v)*interpolate values (cellSegment c) (cellV c 0) +
        cellFraction c v*interpolate values (cellSegment c) (cellV c 1) := by
  have hne : (cellV c 1 : ℝ) - cellV c 0 ≠ 0 :=
    (sub_pos.mpr (Rat.cast_lt.mpr (source_cells_in_segments c).2.1)).ne'
  have reconstruct : (1-cellFraction c v)*(cellV c 0 : ℝ) +
      cellFraction c v*(cellV c 1 : ℝ) = v := by
    dsimp [cellFraction]
    field_simp
    ring
  have affine : ∀ t : ℝ,
      interpolate values (cellSegment c) ((1-t)*(cellV c 0 : ℝ)+t*(cellV c 1 : ℝ)) =
        (1-t)*interpolate values (cellSegment c) (cellV c 0) +
          t*interpolate values (cellSegment c) (cellV c 1) := by
    intro t
    dsimp [interpolate, knotFraction]
    ring
  simpa only [reconstruct] using affine (cellFraction c v)

theorem lower_curve_in_u (c : FullBandCell) (v : ℝ)
    (hv : v ∈ Icc (cellV c 0 : ℝ) (cellV c 1)) :
    Holds (uRange c) (interpolate Geometry.Source.lower (cellSegment c) v - (Geometry.Source.epsilon 0 : ℝ)) := by
  have corner (side : Fin 2) : Holds (uRange c) ((cellLowerCurve c side : ℝ) - (Geometry.Source.epsilon 0 : ℝ)) := by
    have h := source_u_corners c side
    unfold Holds
    exact_mod_cast And.intro h.1 h.2.1
  have bound := SourceCellGeometry.holds_lerp _ _ _ _ (corner 0) (corner 1) (cellFraction_mem c v hv)
  have first := interpolateQ_cast Geometry.Source.lower (cellSegment c) (cellV c 0)
  have last := interpolateQ_cast Geometry.Source.lower (cellSegment c) (cellV c 1)
  rw [(source_corners c 0).1] at first
  rw [(source_corners c 1).1] at last
  rw [subcell_interpolate, ← first, ← last]
  convert bound using 1
  ring

theorem upper_curve_in_u (c : FullBandCell) (v : ℝ)
    (hv : v ∈ Icc (cellV c 0 : ℝ) (cellV c 1)) :
    Holds (uRange c) (interpolate Geometry.Source.upper (cellSegment c) v + (Geometry.Source.epsilon 0 : ℝ)) := by
  have corner (side : Fin 2) : Holds (uRange c) ((cellUpperCurve c side : ℝ) + (Geometry.Source.epsilon 0 : ℝ)) := by
    have h := source_u_corners c side
    unfold Holds
    exact_mod_cast And.intro h.2.2.1 h.2.2.2
  have bound := SourceCellGeometry.holds_lerp _ _ _ _ (corner 0) (corner 1) (cellFraction_mem c v hv)
  have first := interpolateQ_cast Geometry.Source.upper (cellSegment c) (cellV c 0)
  have last := interpolateQ_cast Geometry.Source.upper (cellSegment c) (cellV c 1)
  rw [(source_corners c 0).2] at first
  rw [(source_corners c 1).2] at last
  rw [subcell_interpolate, ← first, ← last]
  convert bound using 1
  ring

theorem bandU_in_source (c : FullBandCell) (p : Point) (hp : p ∈ cellDomain c) :
    Holds (uRange c) (bandU (cellSegment c) (Geometry.Source.epsilon 0) p) := by
  have h := SourceCellGeometry.holds_lerp _ _ _ _
    (lower_curve_in_u c (p 1) hp.2.1) (upper_curve_in_u c (p 1) hp.2.1) hp.1
  convert h using 1
  simp only [bandU,bandWidth]
  ring

theorem cell_seed_in_initial (c : FullBandCell) (p : Point) (hp : p ∈ cellDomain c) :
    InRectangle (initialBox c 0 0) (cellSeed c p) := by
  have hu := bandU_in_source c p hp
  have hv : Holds (vRange c) (p 1) := hp.2.1
  intro a
  rw [← source_initial_box c a]
  have bound := add_holds _ _ _ _
    (add_holds _ _ _ _ (point_holds (SourceFiniteData.boxCentre a))
      (mul_holds _ _ _ _ (point_holds (Geometry.Source.basis a 0)) hu))
    (mul_holds _ _ _ _ (point_holds (Geometry.Source.basis a 1)) hv)
  simpa only [positionBox, cellSeed, bandSeed, centre, basisVector,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using bound

end
end LAlanine40K2025.BasinRefinement.WholeBandSeed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

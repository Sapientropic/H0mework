import H0mework.Versions.AB.Chemistry.LAlanineParametric.Seed

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGeometry

open ContinuousSeed SourceGaussianModel Set
noncomputable section

theorem source_knots_strictMono : StrictMono knotCoordinate := by decide +kernel

theorem interpolate_first (values : Geometry.Data.Knot → ℚ) (s : Segment) :
    interpolate values s (knotCoordinate (firstKnot s)) = values (firstKnot s) := by
  simp [interpolate, knotFraction]

theorem interpolate_last (values : Geometry.Data.Knot → ℚ) (s : Segment) :
    interpolate values s (knotCoordinate (lastKnot s)) = values (lastKnot s) := by
  have order : (knotCoordinate (firstKnot s) : ℝ) < knotCoordinate (lastKnot s) :=
    Rat.cast_lt.mpr (source_knot_geometry.1 s)
  simp [interpolate, knotFraction, (sub_pos.mpr order).ne']

private theorem interpolate_overlap_lt (values : Geometry.Data.Knot → ℚ) (s t : Segment)
    (st : s < t) (v : ℝ)
    (hs : v ∈ Icc (knotCoordinate (firstKnot s) : ℝ) (knotCoordinate (lastKnot s)))
    (ht : v ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t))) :
    interpolate values s v = interpolate values t v := by
  have indices : lastKnot s ≤ firstKnot t := by
    change s.val + 1 ≤ t.val
    exact st
  have ordered : (knotCoordinate (lastKnot s) : ℝ) ≤ knotCoordinate (firstKnot t) :=
    Rat.cast_le.mpr (source_knots_strictMono.monotone indices)
  have left : v = (knotCoordinate (lastKnot s) : ℝ) := le_antisymm hs.2 (ordered.trans ht.1)
  have right : v = (knotCoordinate (firstKnot t) : ℝ) := le_antisymm (hs.2.trans ordered) ht.1
  have same : lastKnot s = firstKnot t := by
    apply source_knots_strictMono.injective
    exact_mod_cast (left.symm.trans right)
  calc
    interpolate values s v = values (lastKnot s) := by rw [left, interpolate_last]
    _ = values (firstKnot t) := by rw [same]
    _ = interpolate values t v := by rw [right, interpolate_first]

/-- Different source segments agree exactly where their closed source intervals meet. -/
theorem interpolate_overlap (values : Geometry.Data.Knot → ℚ) (s t : Segment) (v : ℝ)
    (hs : v ∈ Icc (knotCoordinate (firstKnot s) : ℝ) (knotCoordinate (lastKnot s)))
    (ht : v ∈ Icc (knotCoordinate (firstKnot t) : ℝ) (knotCoordinate (lastKnot t))) :
    interpolate values s v = interpolate values t v := by
  rcases lt_trichotomy s t with h | h | h
  · exact interpolate_overlap_lt values s t h v hs ht
  · rw [h]
  · exact (interpolate_overlap_lt values t s h v ht hs).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

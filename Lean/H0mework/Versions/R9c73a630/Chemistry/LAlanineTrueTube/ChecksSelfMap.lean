import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ChecksArithmetic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeChecks

open TrueTubeSource TrueTubeTrace SourceGaussianModel SourceSignedEvaluator IntervalParameterMap Set
noncomputable section

theorem lower_holds (box : Rectangle) (ordered : ∀ axis, (box axis).1 ≤ (box axis).2) :
    VectorHolds box (lowerPoint box) :=
  fun axis => ⟨le_rfl, Rat.cast_le.mpr (ordered axis)⟩

theorem upper_holds (box : Rectangle) (ordered : ∀ axis, (box axis).1 ≤ (box axis).2) :
    VectorHolds box (upperPoint box) :=
  fun axis => ⟨Rat.cast_le.mpr (ordered axis), le_rfl⟩

theorem first_selfmap (d : Direction) (t : ℝ) (inside : t ∈ Icc 0 (stepSize : ℝ)) :
    lowerPoint (tubeBox d 0) ≤ lowerPoint (initialBox d 0) + t • lowerPoint (signedTubeGradient d) ∧
      upperPoint (initialBox d 0) + t • upperPoint (signedTubeGradient d) ≤ upperPoint (tubeBox d 0) := by
  have timeBound : Holds (0, stepSize) t := by
    simpa only [Holds, Rat.cast_zero, Set.mem_Icc] using inside
  have lowerImage : VectorHolds (picardImage d)
      (lowerPoint (initialBox d 0) + t • lowerPoint (signedTubeGradient d)) :=
    vectorAdd_contains _ _ _ _ (lower_holds _ (initial_ordered d 0))
      (vectorScale_contains _ _ _ _ timeBound (lower_holds _ (signed_tube_ordered d)))
  have upperImage : VectorHolds (picardImage d)
      (upperPoint (initialBox d 0) + t • upperPoint (signedTubeGradient d)) :=
    vectorAdd_contains _ _ _ _ (upper_holds _ (initial_ordered d 0))
      (vectorScale_contains _ _ _ _ timeBound (upper_holds _ (signed_tube_ordered d)))
  constructor
  · intro axis
    exact (Rat.cast_le.mpr (first_picard_selfmap d axis).1).trans (lowerImage axis).1
  · intro axis
    exact (upperImage axis).2.trans (Rat.cast_le.mpr (first_picard_selfmap d axis).2)

theorem endpoint_intersection_contains (d : Direction) (x : Point)
    (euler : VectorHolds (eulerEndpoint d) x) (second : VectorHolds (secondEndpoint d) x) :
    InRectangle (endpointBox d 0) x := by
  intro axis
  rw [← first_endpoint_recomputed d axis]
  change ((max (eulerEndpoint d axis).1 (secondEndpoint d axis).1 : ℚ) : ℝ) ≤ x axis ∧
    x axis ≤ ((min (eulerEndpoint d axis).2 (secondEndpoint d axis).2 : ℚ) : ℝ)
  rw [Rat.cast_max, Rat.cast_min]
  exact ⟨max_le (euler axis).1 (second axis).1, le_min (euler axis).2 (second axis).2⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

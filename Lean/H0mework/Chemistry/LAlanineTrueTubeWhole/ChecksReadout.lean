import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksArithmetic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks

open TrueTubeSource TrueTubeTrace SourceGaussianModel SourceSignedEvaluator IntervalParameterMap Set
noncomputable section

theorem selfmap (d : Direction) (i : Step) (t : ℝ) (inside : t ∈ Icc 0 (stepSize : ℝ)) :
    lowerPoint (tubeBox d i) ≤ lowerPoint (initialBox d i) + t • lowerPoint (signedTubeGradient d i) ∧
      upperPoint (initialBox d i) + t • upperPoint (signedTubeGradient d i) ≤ upperPoint (tubeBox d i) := by
  have timeBound : Holds (0, stepSize) t := by
    simpa only [Holds, Rat.cast_zero, Set.mem_Icc] using inside
  have lowerImage : VectorHolds (picardImage d i)
      (lowerPoint (initialBox d i) + t • lowerPoint (signedTubeGradient d i)) :=
    vectorAdd_contains _ _ _ _ (TrueTubeChecks.lower_holds _ (TrueTubeChecks.initial_ordered d i))
      (vectorScale_contains _ _ _ _ timeBound
        (TrueTubeChecks.lower_holds _ (signed_tube_ordered d i)))
  have upperImage : VectorHolds (picardImage d i)
      (upperPoint (initialBox d i) + t • upperPoint (signedTubeGradient d i)) :=
    vectorAdd_contains _ _ _ _ (TrueTubeChecks.upper_holds _ (TrueTubeChecks.initial_ordered d i))
      (vectorScale_contains _ _ _ _ timeBound
        (TrueTubeChecks.upper_holds _ (signed_tube_ordered d i)))
  constructor
  · intro axis
    exact (Rat.cast_le.mpr (all_picard_selfmaps d i axis).1).trans (lowerImage axis).1
  · intro axis
    exact (upperImage axis).2.trans (Rat.cast_le.mpr (all_picard_selfmaps d i axis).2)

/-- The actual second-order source enclosure is strictly selected on every axis. -/
theorem endpoint_from_dynamics (d : Direction) (i : Step) (initial target velocity : Point)
    (initialInside : InRectangle (initialBox d i) initial)
    (velocityInside : VectorHolds (signedInitialGradient d i) velocity)
    (second : initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        lowerPoint (rowAcceleration d i) ≤ target ∧
      target ≤ initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        upperPoint (rowAcceleration d i)) : InRectangle (endpointBox d i) target := by
  have initialEuler : VectorHolds
      (vectorAdd (initialBox d i) (vectorScale (point stepSize) (signedInitialGradient d i)))
      (initial + (stepSize : ℝ) • velocity) :=
    vectorAdd_contains _ _ _ _ initialInside
      (vectorScale_contains _ _ _ _ (point_holds stepSize) velocityInside)
  have coefficient : Holds (point (stepSize ^ 2 / 2)) ((stepSize : ℝ) ^ 2 / 2) := by
    convert! point_holds (stepSize ^ 2 / 2) using 1
    norm_num [TrueTubeChecks.step_value]
  have lower : VectorHolds (secondEndpoint d i)
      (initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) • lowerPoint (rowAcceleration d i)) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient
        (TrueTubeChecks.lower_holds _ (acceleration_ordered d i)))
  have upper : VectorHolds (secondEndpoint d i)
      (initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) • upperPoint (rowAcceleration d i)) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient
        (TrueTubeChecks.upper_holds _ (acceleration_ordered d i)))
  rw [← second_endpoint_eq d i]
  exact fun axis => ⟨(lower axis).1.trans (second.1 axis), (second.2 axis).trans (upper axis).2⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

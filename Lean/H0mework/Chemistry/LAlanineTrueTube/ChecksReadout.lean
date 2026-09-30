import H0mework.Chemistry.LAlanineTrueTube.ChecksSelfMap

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeChecks

open TrueTubeSource TrueTubeTrace SourceGaussianModel SourceSignedEvaluator IntervalParameterMap Set
noncomputable section

private theorem interval_sandwich (box : VectorPair) (lower upper target : Point)
    (hl : VectorHolds box lower) (hu : VectorHolds box upper) (bounds : lower ≤ target ∧ target ≤ upper) :
    VectorHolds box target :=
  fun axis => ⟨(hl axis).1.trans (bounds.1 axis), (bounds.2 axis).trans (hu axis).2⟩

/-- Both dynamical estimates constrain the same target; source arithmetic generates their exact meet. -/
theorem endpoint_from_dynamics (d : Direction) (initial target velocity : Point)
    (initialInside : InRectangle (initialBox d 0) initial)
    (velocityInside : VectorHolds (signedInitialGradient d) velocity)
    (once : initial + (stepSize : ℝ) • lowerPoint (signedTubeGradient d) ≤ target ∧
      target ≤ initial + (stepSize : ℝ) • upperPoint (signedTubeGradient d))
    (second : initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        lowerPoint (accelerationPair (recordedField (firstTubeField d))) ≤ target ∧
      target ≤ initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        upperPoint (accelerationPair (recordedField (firstTubeField d)))) :
    InRectangle (endpointBox d 0) target := by
  have eulerLower : VectorHolds (eulerEndpoint d)
      (initial + (stepSize : ℝ) • lowerPoint (signedTubeGradient d)) :=
    vectorAdd_contains _ _ _ _ initialInside
      (vectorScale_contains _ _ _ _ (point_holds stepSize) (lower_holds _ (signed_tube_ordered d)))
  have eulerUpper : VectorHolds (eulerEndpoint d)
      (initial + (stepSize : ℝ) • upperPoint (signedTubeGradient d)) :=
    vectorAdd_contains _ _ _ _ initialInside
      (vectorScale_contains _ _ _ _ (point_holds stepSize) (upper_holds _ (signed_tube_ordered d)))
  have initialEuler : VectorHolds
      (vectorAdd (initialBox d 0) (vectorScale (point stepSize) (signedInitialGradient d)))
      (initial + (stepSize : ℝ) • velocity) :=
    vectorAdd_contains _ _ _ _ initialInside
      (vectorScale_contains _ _ _ _ (point_holds stepSize) velocityInside)
  have coefficient : Holds (point (stepSize ^ 2 / 2)) ((stepSize : ℝ) ^ 2 / 2) := by
    convert! point_holds (stepSize ^ 2 / 2) using 1
    norm_num [step_value]
  have secondLower : VectorHolds (secondEndpoint d)
      (initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        lowerPoint (accelerationPair (recordedField (firstTubeField d)))) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient (lower_holds _ (acceleration_ordered d)))
  have secondUpper : VectorHolds (secondEndpoint d)
      (initial + (stepSize : ℝ) • velocity + ((stepSize : ℝ) ^ 2 / 2) •
        upperPoint (accelerationPair (recordedField (firstTubeField d)))) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient (upper_holds _ (acceleration_ordered d)))
  exact endpoint_intersection_contains d target
    (interval_sandwich _ _ _ _ eulerLower eulerUpper once)
    (interval_sandwich _ _ _ _ secondLower secondUpper second)

end
end LAlanine40K2025.BasinRefinement.TrueTubeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

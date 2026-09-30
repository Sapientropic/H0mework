import H0mework.Chemistry.LAlanineTrueTube.ActualSeeds
import H0mework.Chemistry.LAlanineTrueTube.ChecksReadout
import H0mework.Chemistry.LAlanineTrueTube.TraceSignedField
import H0mework.Chemistry.LAlanineTrueTube.DynamicsEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeActual

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
open TrueTubeSource TrueTubeChecks TrueTubeTrace Set
noncomputable section

/-- This is the splice mouth: the two actual continuous field certificates are supplied by the
    original Gaussian producer, while geometry and endpoint arithmetic are already discharged. -/
theorem firstStep_from_fields (d : Direction)
    (initialField : ∀ x, InRectangle (initialBox d 0) x → FieldHolds (recordedField 0) x)
    (tubeField : ∀ x, InRectangle (tubeBox d 0) x → FieldHolds (recordedField (firstTubeField d)) x)
    (initial : Point) (inside : InRectangle (initialBox d 0) initial) :
    ∃ curve : ℝ → Point, curve 0 = initial ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox d 0) (curve t)) ∧
      InRectangle (endpointBox d 0) (curve stepSize) ∧
      InRectangle (initialBox d 1) (curve stepSize) := by
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (direction_units d).1
  have square : (sign d : ℝ) * (sign d : ℝ) = 1 := by exact_mod_cast (direction_units d).2
  have ordered : lowerPoint (tubeBox d 0) ≤ upperPoint (tubeBox d 0) :=
    fun i => Rat.cast_le.mpr (tube_ordered d 0 i)
  have gradientBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox d 0)) (upperPoint (tubeBox d 0))) :
      signedGradient (sign d) x ∈ Icc (lowerPoint (signedTubeGradient d)) (upperPoint (signedTubeGradient d)) :=
    (inRectangle_iff _ _).mp
      (signed_gradient_contains (sign d) _ x (tubeField x ((inRectangle_iff _ _).mpr hx)))
  have accelerationBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox d 0)) (upperPoint (tubeBox d 0))) :
      signedHessian (sign d) x (signedGradient (sign d) x) ∈
        Icc (lowerPoint (accelerationPair (recordedField (firstTubeField d))))
          (upperPoint (accelerationPair (recordedField (firstTubeField d)))) :=
    (inRectangle_iff _ _).mp
      (signed_acceleration_contains _ x (tubeField x ((inRectangle_iff _ _).mpr hx)) (sign d) square)
  obtain ⟨curve, starts, evolves, once, second⟩ := LAlanineTrueTube.Dynamics.exists_step_secondOrder
    (lowerPoint (tubeBox d 0)) (upperPoint (tubeBox d 0))
    (lowerPoint (initialBox d 0)) (upperPoint (initialBox d 0)) ordered
    (signedGradient (sign d)) (fieldLipschitz (recordedField (firstTubeField d)))
    (signed_field_lipschitz _ _ tubeField (sign d) unit)
    (lowerPoint (signedTubeGradient d)) (upperPoint (signedTubeGradient d)) gradientBounds
    stepSize (Rat.cast_pos.mpr step_positive) (first_selfmap d)
    (signedHessian (sign d)) (fun x _ => signedGradient_hasFDerivAt (sign d) x)
    (lowerPoint (accelerationPair (recordedField (firstTubeField d))))
    (upperPoint (accelerationPair (recordedField (firstTubeField d)))) accelerationBounds
    initial ((inRectangle_iff _ _).mp inside)
  have endpoint : InRectangle (endpointBox d 0) (curve stepSize) :=
    endpoint_from_dynamics d initial _ _ inside
      (signed_gradient_contains (sign d) _ initial (initialField initial inside)) once second
  refine ⟨curve, starts, fun t ht => ⟨(evolves t ht).1, (inRectangle_iff _ _).mpr (evolves t ht).2⟩,
    endpoint, ?_⟩
  have next : endpointBox d 0 = initialBox d 1 := by
    convert endpoint_next_initial d (0 : Fin 15) using 1 <;> rfl
  rw [← next]
  exact endpoint

end
end LAlanine40K2025.BasinRefinement.TrueTubeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

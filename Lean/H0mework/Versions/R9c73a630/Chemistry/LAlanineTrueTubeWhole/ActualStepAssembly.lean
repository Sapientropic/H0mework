import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ChecksReadout
import H0mework.Chemistry.LAlanineTrueTube.DynamicsEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap
open TrueTubeSource TrueTubeWholeSource TrueTubeWholeChecks TrueTubeTrace Set
noncomputable section

def LocalStepLaw (d : Direction) (i : Step) : Prop :=
  ∀ initial : Point, InRectangle (initialBox d i) initial →
    ∃ curve : ℝ → Point, curve 0 = initial ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox d i) (curve t)) ∧
      InRectangle (endpointBox d i) (curve stepSize)

theorem step_from_source_fields (d : Direction) (i : Step)
    (initialField : ∀ x, InRectangle (initialBox d i) x → FieldHolds (recordedCallField (initialCallAt d i)) x)
    (tubeField : ∀ x, InRectangle (tubeBox d i) x → FieldHolds (recordedCallField (tubeCallAt d i)) x) :
    LocalStepLaw d i := by
  intro initial inside
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).1
  have square : (sign d : ℝ) * (sign d : ℝ) = 1 := by exact_mod_cast (TrueTubeChecks.direction_units d).2
  have ordered : lowerPoint (tubeBox d i) ≤ upperPoint (tubeBox d i) :=
    fun axis => Rat.cast_le.mpr (TrueTubeChecks.tube_ordered d i axis)
  have gradientBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox d i)) (upperPoint (tubeBox d i))) :
      signedGradient (sign d) x ∈ Icc (lowerPoint (signedTubeGradient d i)) (upperPoint (signedTubeGradient d i)) :=
    (inRectangle_iff _ _).mp
      (signed_gradient_contains (sign d) _ x (tubeField x ((inRectangle_iff _ _).mpr hx)))
  have accelerationBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox d i)) (upperPoint (tubeBox d i))) :
      signedHessian (sign d) x (signedGradient (sign d) x) ∈
        Icc (lowerPoint (rowAcceleration d i)) (upperPoint (rowAcceleration d i)) :=
    (inRectangle_iff _ _).mp
      (signed_acceleration_contains _ x (tubeField x ((inRectangle_iff _ _).mpr hx)) (sign d) square)
  obtain ⟨curve, starts, evolves, _, second⟩ := LAlanineTrueTube.Dynamics.exists_step_secondOrder
    (lowerPoint (tubeBox d i)) (upperPoint (tubeBox d i))
    (lowerPoint (initialBox d i)) (upperPoint (initialBox d i)) ordered
    (signedGradient (sign d)) (fieldLipschitz (recordedCallField (tubeCallAt d i)))
    (signed_field_lipschitz _ _ tubeField (sign d) unit)
    (lowerPoint (signedTubeGradient d i)) (upperPoint (signedTubeGradient d i)) gradientBounds
    stepSize (Rat.cast_pos.mpr TrueTubeChecks.step_positive) (selfmap d i)
    (signedHessian (sign d)) (fun x _ => signedGradient_hasFDerivAt (sign d) x)
    (lowerPoint (rowAcceleration d i)) (upperPoint (rowAcceleration d i)) accelerationBounds
    initial ((inRectangle_iff _ _).mp inside)
  refine ⟨curve, starts, fun t ht => ⟨(evolves t ht).1, (inRectangle_iff _ _).mpr (evolves t ht).2⟩, ?_⟩
  exact endpoint_from_dynamics d i initial _ _ inside
    (signed_gradient_contains (sign d) _ initial (initialField initial inside)) second

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

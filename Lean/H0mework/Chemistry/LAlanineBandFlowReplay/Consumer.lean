import H0mework.Chemistry.LAlanineBandFlowReplay.Model
import H0mework.Chemistry.LAlanineGradient.Bounds
import H0mework.Chemistry.LAlanineTrueTube.DynamicsEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandReplay

open WholeBandSource SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeTrace Set
noncomputable section

theorem selfmap {r : Inputs} {i : Step} (h : InputArithmetic r i)
    (t : ℝ) (inside : t ∈ Icc 0 (r.step : ℝ)) :
    lowerPoint r.tube ≤ lowerPoint r.initial + t • lowerPoint (signedTube r) ∧
      upperPoint r.initial + t • upperPoint (signedTube r) ≤ upperPoint r.tube := by
  have timeBound : Holds (0, r.step) t := by
    simpa only [Holds, Rat.cast_zero, Set.mem_Icc] using inside
  have lowerImage : VectorHolds (picardImage r)
      (lowerPoint r.initial + t • lowerPoint (signedTube r)) :=
    vectorAdd_contains _ _ _ _ (TrueTubeChecks.lower_holds _ h.initial_ordered)
      (vectorScale_contains _ _ _ _ timeBound (TrueTubeChecks.lower_holds _ h.signed_ordered))
  have upperImage : VectorHolds (picardImage r)
      (upperPoint r.initial + t • upperPoint (signedTube r)) :=
    vectorAdd_contains _ _ _ _ (TrueTubeChecks.upper_holds _ h.initial_ordered)
      (vectorScale_contains _ _ _ _ timeBound (TrueTubeChecks.upper_holds _ h.signed_ordered))
  exact ⟨fun axis => (Rat.cast_le.mpr (h.strict_picard axis).1.le).trans (lowerImage axis).1,
    fun axis => (upperImage axis).2.trans (Rat.cast_le.mpr (h.strict_picard axis).2.le)⟩

theorem endpoint_from_dynamics {r : Inputs} {i : Step} (h : InputArithmetic r i)
    (initial target velocity : Point) (initialInside : InRectangle r.initial initial)
    (velocityInside : VectorHolds (signedInitial r) velocity)
    (second : initial + (r.step : ℝ) • velocity + ((r.step : ℝ)^2/2) •
        lowerPoint (acceleration r) ≤ target ∧
      target ≤ initial + (r.step : ℝ) • velocity + ((r.step : ℝ)^2/2) •
        upperPoint (acceleration r)) : InRectangle r.endpoint target := by
  have initialEuler : VectorHolds
      (vectorAdd r.initial (vectorScale (point r.step) (signedInitial r)))
      (initial + (r.step : ℝ) • velocity) :=
    vectorAdd_contains _ _ _ _ initialInside
      (vectorScale_contains _ _ _ _ (point_holds r.step) velocityInside)
  have coefficient : Holds (point (r.step ^ 2 / 2)) ((r.step : ℝ)^2/2) := by
    convert! point_holds (r.step ^ 2 / 2) using 1
    norm_num
  have lower : VectorHolds (secondEndpoint r)
      (initial + (r.step : ℝ) • velocity + ((r.step : ℝ)^2/2) • lowerPoint (acceleration r)) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient (TrueTubeChecks.lower_holds _ h.acceleration_ordered))
  have upper : VectorHolds (secondEndpoint r)
      (initial + (r.step : ℝ) • velocity + ((r.step : ℝ)^2/2) • upperPoint (acceleration r)) :=
    vectorAdd_contains _ _ _ _ initialEuler
      (vectorScale_contains _ _ _ _ coefficient (TrueTubeChecks.upper_holds _ h.acceleration_ordered))
  rw [← second_endpoint_eq h]
  exact fun axis => ⟨(lower axis).1.trans (second.1 axis), (second.2 axis).trans (upper axis).2⟩

private theorem in_sourceCube_of_bounds (box : Rectangle)
    (bounds : ∀ axis, SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius ≤ (box axis).1 ∧
      (box axis).2 ≤ SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius)
    (x : Point) (inside : InRectangle box x) : x ∈ ContinuousGradient.sourceCube := by
  intro axis
  have lower : (SourceFiniteData.boxCentre axis : ℝ) - (SourceFiniteData.boxRadius : ℝ) ≤ (box axis).1 := by
    exact_mod_cast (bounds axis).1
  have upper : ((box axis).2 : ℝ) ≤ (SourceFiniteData.boxCentre axis : ℝ) + (SourceFiniteData.boxRadius : ℝ) := by
    exact_mod_cast (bounds axis).2
  apply abs_le.mpr
  constructor <;> linarith [(inside axis).1, (inside axis).2]

theorem initial_in_sourceCube {r : Inputs} {i : Step} (h : InputArithmetic r i)
    (x : Point) (inside : InRectangle r.initial x) : x ∈ ContinuousGradient.sourceCube :=
  in_sourceCube_of_bounds _ h.initial_cube x inside

theorem tube_in_sourceCube {r : Inputs} {i : Step} (h : InputArithmetic r i)
    (x : Point) (inside : InRectangle r.tube x) : x ∈ ContinuousGradient.sourceCube :=
  in_sourceCube_of_bounds _ h.tube_cube x inside

def LocalStepLaw (c : FullBandCell) (d : Direction) (i : Step) : Prop :=
  ∀ initial : Point, InRectangle (initialBox c d i) initial →
    ∃ curve : ℝ → Point, curve 0 = initial ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox c d i) (curve t)) ∧
      InRectangle (endpointBox c d i) (curve stepSize)

/-- Arithmetic is paid here; the two source field laws remain the genuine analytic feed. -/
theorem step_from_arithmetic_and_fields (c : FullBandCell) (d : Direction) (i : Step)
    (h : RowArithmetic c d i)
    (initialField : ∀ x, InRectangle (callBox (initialCallAt c d i)) x →
      FieldHolds (recordedCallField (initialCallAt c d i)) x)
    (tubeField : ∀ x, InRectangle (callBox (tubeCallAt c d i)) x →
      FieldHolds (recordedCallField (tubeCallAt c d i)) x) : LocalStepLaw c d i := by
  have initialFields : ∀ x, InRectangle (initialBox c d i) x →
      FieldHolds (recordedCallField (initialCallAt c d i)) x := by
    intro x hx
    apply initialField x
    simpa only [show callBox (initialCallAt c d i) = initialBox c d i from funext h.initial_join] using hx
  have tubeFields : ∀ x, InRectangle (tubeBox c d i) x →
      FieldHolds (recordedCallField (tubeCallAt c d i)) x := by
    intro x hx
    apply tubeField x
    simpa only [show callBox (tubeCallAt c d i) = tubeBox c d i from funext h.tube_join] using hx
  intro initial inside
  have unit : |(sign d : ℝ)| = 1 := by exact_mod_cast h.unit.1
  have square : (sign d : ℝ) * (sign d : ℝ) = 1 := by exact_mod_cast h.unit.2
  have ordered : lowerPoint (tubeBox c d i) ≤ upperPoint (tubeBox c d i) :=
    fun axis => Rat.cast_le.mpr (h.tube_ordered axis)
  have gradientBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox c d i)) (upperPoint (tubeBox c d i))) :
      signedGradient (sign d) x ∈ Icc (lowerPoint (signedTube (rowInput c d i)))
        (upperPoint (signedTube (rowInput c d i))) :=
    (inRectangle_iff _ _).mp
      (signed_gradient_contains (sign d) _ x (tubeFields x ((inRectangle_iff _ _).mpr hx)))
  have accelerationBounds (x : Point) (hx : x ∈ Icc (lowerPoint (tubeBox c d i)) (upperPoint (tubeBox c d i))) :
      signedHessian (sign d) x (signedGradient (sign d) x) ∈
        Icc (lowerPoint (acceleration (rowInput c d i))) (upperPoint (acceleration (rowInput c d i))) :=
    (inRectangle_iff _ _).mp
      (signed_acceleration_contains _ x (tubeFields x ((inRectangle_iff _ _).mpr hx)) (sign d) square)
  obtain ⟨curve, starts, evolves, _, second⟩ := LAlanineTrueTube.Dynamics.exists_step_secondOrder
    (lowerPoint (tubeBox c d i)) (upperPoint (tubeBox c d i))
    (lowerPoint (initialBox c d i)) (upperPoint (initialBox c d i)) ordered
    (signedGradient (sign d)) (fieldLipschitz (recordedCallField (tubeCallAt c d i)))
    (signed_field_lipschitz _ _ tubeFields (sign d) unit)
    _ _ gradientBounds stepSize (Rat.cast_pos.mpr h.positive_step) (selfmap h)
    (signedHessian (sign d)) (fun x _ => signedGradient_hasFDerivAt (sign d) x)
    _ _ accelerationBounds initial ((inRectangle_iff _ _).mp inside)
  refine ⟨curve, starts, fun t ht => ⟨(evolves t ht).1, (inRectangle_iff _ _).mpr (evolves t ht).2⟩, ?_⟩
  exact endpoint_from_dynamics h initial _ _ inside
    (signed_gradient_contains (sign d) _ initial (initialFields initial inside)) second

end
end LAlanine40K2025.BasinRefinement.WholeBandReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

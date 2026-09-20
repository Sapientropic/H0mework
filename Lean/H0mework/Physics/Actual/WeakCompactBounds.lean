import H0mework.Physics.Actual.FieldsHistoryBounds
import H0mework.Physics.Actual.WeakUniqueness

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Weak

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Set

/-- The original faithful recovery transfers the same bound to every lawful
recovered actual; no candidate-dependent norm budget is supplied. -/
theorem actuals_compact_jet_bound (order : Nat)
    {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ (configuration : StageNineHolonomicConfiguration)
      (smooth : configuration.Smooth),
      (∃ candidate : Candidate,
        density candidate = Fields.compactCoordinates configuration smooth) →
      ∀ coordinate : Fields.Coordinate, ∀ point ∈ domain,
        ‖iteratedFDeriv ℝ order (Fields.realCoordinate configuration coordinate) point‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := Fields.history_compact_jet_bound order compact
  refine ⟨bound, ?_⟩
  intro configuration smooth admitted
  rw [configuration_eq_firstWrite_of_candidate smooth admitted]
  exact bounded 7

end SaturationMonoid.PhysicsCore.Stage9CU.Weak

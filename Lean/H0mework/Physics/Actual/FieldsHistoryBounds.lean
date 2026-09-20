import H0mework.Physics.Actual.FieldsCompactL2
import H0mework.Physics.Actual.HistoryOnShell

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource Set
open scoped ContDiff

/-- One bound covers every original history stage and all nine-field real
coordinates on a compact spacetime domain, at any given finite derivative order. -/
theorem history_compact_jet_bound (order : Nat)
    {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ index : Nat, ∀ coordinate : Coordinate, ∀ point ∈ domain,
      ‖iteratedFDeriv ℝ order
        (realCoordinate (History.configuration index) coordinate) point‖ ≤ bound := by
  let jets (point : BasePoint) :
      (Fin 8 × Coordinate) → ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun item => iteratedFDeriv ℝ order
      (realCoordinate (History.configuration item.1) item.2) point
  have continuity : Continuous jets :=
    continuous_pi fun item =>
      ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
        (realCoordinate_contDiff (History.configuration_smooth item.1) item.2)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity.continuousOn
  refine ⟨bound, ?_⟩
  intro index coordinate point pointMem
  by_cases early : index < 8
  · exact (norm_le_pi_norm (jets point) (⟨index, early⟩, coordinate)).trans (bounded point pointMem)
  · have same := History.configuration_add_seven_eq_firstWrite (index - 7)
    have recover : index - 7 + 7 = index := by omega
    rw [recover] at same
    rw [same]
    exact (norm_le_pi_norm (jets point) ((7 : Fin 8), coordinate)).trans (bounded point pointMem)

end SaturationMonoid.PhysicsCore.Stage9CU.Fields

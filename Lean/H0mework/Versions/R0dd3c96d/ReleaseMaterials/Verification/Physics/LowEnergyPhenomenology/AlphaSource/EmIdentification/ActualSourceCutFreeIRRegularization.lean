import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceEventCutElimination
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRReturn

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceEMEventFeed

open ActualDressedFullCoulomb ActualDressedSylvester ActualDressedCubicIRReturn
open Filter Set
open scoped Topology Matrix.Norms.Elementwise

/-- The same fourth-order analytic representative works for every cut index
on one right-half-plane neighborhood of the original dressed event. -/
theorem actual_cut_free_fourth_ir_regularization (event : DressedEvent) :
    ∃ G : ℂ → Matrix (Fin 289) (Fin 289) ℂ, AnalyticAt ℂ G 0 ∧
      ∀ᶠ z : ℂ in 𝓝 0, 0 < z.re → ∀ cut : ℕ,
        z^4 • dressedStaticPolarization {event with cut := cut} 0 z = G z := by
  obtain ⟨G, hG, hagrees⟩ := actual_fourth_ir_regularization event
  refine ⟨G, hG, ?_⟩
  filter_upwards [hagrees] with z hz
  intro hpos cut
  rw [actual_cut_free_static event cut 0 z]
  exact hz hpos

theorem actual_cut_free_sixth_ir_zero_return (event : DressedEvent) (cut : ℕ) :
    Tendsto (fun z : ℂ => z^6 • dressedStaticPolarization {event with cut := cut} 0 z)
      (nhdsWithin 0 {z : ℂ | 0 < z.re}) (𝓝 0) := by
  simpa only [actual_cut_free_static] using actual_sixth_ir_zero_return event

end LowEnergy.GaussComposite.ActualSourceEMEventFeed

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity

/-! Material coldness survives timed words under every generated epoch law.
Scope changes and refused requests cannot manufacture physical exit supplies. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

def continuation (before : Current) : List (Epoch × List Action) → Current
  | [] => before
  | (epoch,word) :: tail => continuation ((Mandate.law base epoch.scope).next before word) tail

theorem below_envelope_survives_every_timed_scope_word (epoch : Epoch) (before : Current)
    (word : List Action) (healthy : Nonnegative before) (cold : ¬ Envelope before) :
    Nonnegative ((Mandate.law base epoch.scope).next before word) ∧
      ¬ Envelope ((Mandate.law base epoch.scope).next before word) :=
  below_envelope_preserved_by_every_raw_word epoch before word 0 healthy cold

theorem below_envelope_survives_every_finite_scope_continuation (before : Current)
    (history : List (Epoch × List Action)) (healthy : Nonnegative before) (cold : ¬ Envelope before) :
    Nonnegative (continuation before history) ∧ ¬ Envelope (continuation before history) := by
  induction history generalizing before with
  | nil => exact ⟨healthy,cold⟩
  | cons step tail ih =>
      have kept := below_envelope_survives_every_timed_scope_word step.1 before step.2 healthy cold
      exact ih _ kept.1 kept.2

theorem below_envelope_forbids_exit_after_every_finite_scope_continuation (before : Current)
    (history : List (Epoch × List Action)) (healthy : Nonnegative before) (cold : ¬ Envelope before)
    (epoch : Epoch) (actor : Bool) :
    ¬ (Mandate.law base epoch.scope).Valid (continuation before history)
      (request epoch.scope (continuation before history) actor .exit) := by
  have kept := below_envelope_survives_every_finite_scope_continuation before history healthy cold
  exact below_envelope_forbids_every_later_exit epoch (continuation before history) [] kept.1 kept.2 actor

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity

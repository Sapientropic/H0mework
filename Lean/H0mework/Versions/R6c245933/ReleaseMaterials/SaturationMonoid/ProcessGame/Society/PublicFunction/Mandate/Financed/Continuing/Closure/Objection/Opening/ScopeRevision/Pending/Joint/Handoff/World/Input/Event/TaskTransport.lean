import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.TaskTransport

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

/-- Actual source changes transport task slots, rather than equating histories. -/
def along {first last : Packet} : Evolution first last → first.1.source.Slot → last.1.source.Slot
  | .same _, index => index
  | .submit _ _, index => index
  | .handoff _ fresh, index => Handoff.homologous fresh index
  | .handoffAt _ fresh _, index => Handoff.homologous fresh index
  | .append earlier later, index => along later (along earlier index)

theorem content {first last : Packet} (path : Evolution first last) (index : first.1.source.Slot) :
    last.1.source.seed.slot (along path index) = first.1.source.seed.slot index := by
  induction path with
  | same packet => rfl
  | submit inventory word => rfl
  | handoff inventory fresh => exact Handoff.original_slot_content_is_preserved fresh index
  | handoffAt inventory fresh actualInputs => exact Handoff.original_slot_content_is_preserved fresh index
  | append earlier later before after => exact (after (along earlier index)).trans (before index)

theorem index_preserved {first last : Packet} (path : Evolution first last) (index : first.1.source.Slot) :
    (along path index).val = index.val := by
  induction path with
  | same packet => rfl
  | submit inventory word => rfl
  | handoff inventory fresh => rfl
  | handoffAt inventory fresh actualInputs => rfl
  | append earlier later before after => exact (after (along earlier index)).trans (before index)

theorem injective {first last : Packet} (path : Evolution first last) : Function.Injective (along path) := by
  intro left right same
  apply Fin.ext
  exact (index_preserved path left).symm.trans ((congrArg Fin.val same).trans (index_preserved path right))

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.TaskTransport

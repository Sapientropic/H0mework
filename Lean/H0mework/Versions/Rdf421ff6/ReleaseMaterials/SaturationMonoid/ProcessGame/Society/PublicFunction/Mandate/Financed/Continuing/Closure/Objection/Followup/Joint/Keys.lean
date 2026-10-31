import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Admission

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

variable {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs}

def KeyBefore (boundary key : PositionKey) : Prop :=
  key.1 < boundary.1 ∨ (key.1 = boundary.1 ∧ key.2 < boundary.2)

def Frame.KeysBefore (frame : Frame cut) (boundary : PositionKey) : Prop :=
  ∀ key ∈ frame.seen, KeyBefore boundary key

theorem Decision.keys_before {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) (boundary : PositionKey)
    (old : ∀ key ∈ seen, KeyBefore boundary key) (new : KeyBefore boundary (eventKey event)) :
    ∀ key ∈ decision.nextSeen, KeyBefore boundary key := by
  cases decision <;> intro key present
  · exact old key present
  · exact old key present
  · rcases List.mem_append.mp present with inside | same
    · exact old key inside
    · cases List.mem_singleton.mp same; exact new
  · rcases List.mem_append.mp present with inside | same
    · exact old key inside
    · cases List.mem_singleton.mp same; exact new

theorem Frame.fold_keys_before (frame : Frame cut) (boundary : PositionKey) (old : frame.KeysBefore boundary)
    (events : List (Event cut)) (ordered : ∀ event ∈ events, KeyBefore boundary (eventKey event)) :
    (frame.fold events).KeysBefore boundary := by
  induction events generalizing frame with
  | nil => exact old
  | cons event tail ih =>
    exact ih (frame.step event)
      ((decide frame.rows frame.seen event).keys_before boundary old (ordered event (List.mem_cons_self)))
      (fun later inside => ordered later (List.mem_cons_of_mem _ inside))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

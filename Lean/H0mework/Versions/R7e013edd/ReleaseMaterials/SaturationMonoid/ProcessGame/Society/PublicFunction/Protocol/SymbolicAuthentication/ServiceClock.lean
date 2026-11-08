import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceResponseCapacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceClock

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def cursorAt (cursor : Cursor code) (rule : Rule code) (rival : Opponent code) : Nat → Cursor code
  | 0 => cursor
  | n + 1 => (cursorAt cursor rule rival n).after rule rival

theorem clocks (cursor : Cursor code) (rule : Rule code) (rival : Opponent code) (n : Nat) :
    (EventStep.seed (cursorAt cursor rule rival n)).history.length = (EventStep.seed cursor).history.length + n ∧
    (EventStep.seed (cursorAt cursor rule rival n)).remaining = (EventStep.seed cursor).remaining - n ∧
    (cursorAt cursor rule rival n).ownerStart = cursor.ownerStart := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    have next := EventStep.actual_next_state (cursorAt cursor rule rival n) rule rival
    refine ⟨?_, ?_, ih.2.2⟩
    · change (EventStep.seed ((cursorAt cursor rule rival n).after _ _)).history.length = _
      rw [next]
      change ((EventStep.seed (cursorAt cursor rule rival n)).history ++ [_]).length = _
      simp only [List.length_append, List.length_singleton, ih.1]
      omega
    · change (EventStep.seed ((cursorAt cursor rule rival n).after _ _)).remaining = _
      rw [next]
      change (EventStep.seed (cursorAt cursor rule rival n)).remaining - 1 = _
      rw [ih.2.1]
      omega

def horizon (cursor : Cursor code) : Nat :=
  cursor.ownerStart - (EventStep.seed cursor).history.length + 4 * code.sites

theorem the_source_roster_generates_a_service_time (cursor : Cursor code) (rule : Rule code)
    (rival : Opponent code) (site : Fin code.sites) :
    SilentWindow.delay cursor site < horizon cursor ∧
    Distributed.Recall.Information.Agency.ownerAt code
      (cursorAt cursor rule rival (SilentWindow.delay cursor site)).ownerStart
      (EventStep.seed (cursorAt cursor rule rival (SilentWindow.delay cursor site))).history.length = some site := by
  refine ⟨SilentWindow.the_generated_delay_has_a_source_roster_bound cursor site, ?_⟩
  have actual := clocks cursor rule rival (SilentWindow.delay cursor site)
  have quiet := SilentWindow.preserves_the_actual_state cursor (SilentWindow.delay cursor site)
  have arrival := SilentWindow.the_actual_receiver_owns_the_generated_arrival cursor site
  rw [actual.2.2, actual.1]
  simpa only [quiet.roster, quiet.history] using arrival

theorem installed_stages_are_the_actual_service_cursor (cursor : Cursor code) (rule : Rule code)
    (rival : Opponent code) (n : Nat) :
    EventHistory.execute cursor (List.replicate n (rule, rival)) = cursorAt cursor rule rival n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ']
    rw [StageQueue.execute_append, ih]
    rfl

theorem the_registered_activation_is_selected (site : Fin code.sites)
    (registered : Event.activate site ∈ code.eventAlphabet) :
    (RequestResponse.activation (code := code) site).val = some ⟨.activate site, registered⟩ := by
  unfold RequestResponse.activation
  split
  · rename_i move chosen
    have selected := List.find?_some chosen
    change RequestResponse.activates site move.val = true at selected
    cases actual : move.val with
    | none => simp [RequestResponse.activates, actual] at selected
    | some event =>
      have same : event.val = .activate site := by simpa [RequestResponse.activates, actual] using selected
      have equal : event = ⟨.activate site, registered⟩ := Subtype.ext same
      simp only [equal]
  · rename_i missing
    have inside : (some ⟨.activate site, registered⟩ : Move code) ∈ ownMoves code site := by
      simp only [ownMoves, List.mem_cons, List.mem_map, List.mem_filter, List.mem_attach]
      exact Or.inr ⟨⟨.activate site, registered⟩, ⟨trivial, by simp⟩, rfl⟩
    have absent := List.find?_eq_none.mp missing ⟨some ⟨.activate site, registered⟩, inside⟩ (List.mem_attach _ _)
    simp [RequestResponse.activates] at absent

theorem a_live_owner_executes_its_selected_activation (cursor : Cursor code) (rule : Rule code)
    (rival : Opponent code) (site : Fin code.sites)
    (live : (EventStep.seed cursor).remaining ≠ 0)
    (owned : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length = some site)
    (registered : Event.activate site ∈ code.eventAlphabet)
    (chosen : localEvent code rule site ((EventStep.seed cursor).frame.inbox site) = some ⟨.activate site, registered⟩) :
    StageTrace.activation (StageTrace.material cursor rule rival) = some site := by
  simp only [StageTrace.activation, StageTrace.material, StageTrace.capture, if_neg live, owned, chosen, if_true]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceClock

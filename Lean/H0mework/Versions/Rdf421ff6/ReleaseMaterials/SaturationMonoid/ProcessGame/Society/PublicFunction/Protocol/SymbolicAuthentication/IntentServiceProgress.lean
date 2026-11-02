import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetainedIntent

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceProgress

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (rival : Opponent code)

abbrev rule := RetainedIntent.protocol vocabulary encoding law start past
abbrev cursorAt := ServiceClock.cursorAt (RetainedIntent.origin start past) (rule vocabulary encoding law start past) rival
abbrev row (n : Nat) := StageTrace.material (cursorAt vocabulary encoding law start past rival n)
  (rule vocabulary encoding law start past) rival

theorem no_step_creates_a_new_packet (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (cursor : Cursor code) :
    (EventStep.seed (cursor.after (rule vocabulary encoding law start past) rival)).frame.sent =
      (EventStep.seed cursor).frame.sent := by
  rw [EventStep.actual_next_state]
  cases chosen : decision code (EventStep.applied cursor (rule vocabulary encoding law start past) rival) (EventStep.seed cursor) with
  | none => simp [Reaction.Feedback.advance, chosen]
  | some event =>
    have shape := RetainedIntent.actual_event_shape vocabulary encoding law start past accepted cursor rival event chosen
    cases kind : event.val with
    | send sender recipient => simp only [kind] at shape
    | adversary request => simp [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step]
    | activate site => simp [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step]
    | deliver address =>
      simp only [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step]
      split <;> simp

theorem the_entire_window_keeps_the_entry_packet_list
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true) (n : Nat) :
    (EventStep.seed (cursorAt vocabulary encoding law start past rival n)).frame.sent =
      (EventStep.seed (RetainedIntent.origin start past)).frame.sent := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (no_step_creates_a_new_packet vocabulary encoding law start past rival accepted
      (cursorAt vocabulary encoding law start past rival n)).trans ih

theorem an_unserved_intent_keeps_its_own_reading_for_one_actual_step
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (cursor : Cursor code) (site : Fin code.sites)
    (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ [])
    (packets : (EventStep.seed cursor).frame.sent = (EventStep.seed (RetainedIntent.origin start past)).frame.sent)
    (unserved : (EventStep.seed cursor).frame.inbox site = RetainedIntent.memory start past site) :
    StageTrace.activation (StageTrace.material cursor (rule vocabulary encoding law start past) rival) = some site ∨
      (EventStep.seed (cursor.after (rule vocabulary encoding law start past) rival)).frame.inbox site =
        RetainedIntent.memory start past site := by
  cases chosen : decision code (EventStep.applied cursor (rule vocabulary encoding law start past) rival) (EventStep.seed cursor) with
  | none =>
    right
    rw [EventStep.actual_next_state]
    simpa only [Reaction.Feedback.advance, chosen] using unserved
  | some event =>
    have shape := RetainedIntent.actual_event_shape vocabulary encoding law start past accepted cursor rival event chosen
    cases kind : event.val with
    | send sender recipient => simp only [kind] at shape
    | adversary request =>
      right
      rw [EventStep.actual_next_state]
      simpa only [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step] using unserved
    | activate worker =>
      simp only [kind] at shape
      by_cases same : site = worker
      · subst worker
        exact Or.inl shape
      · right
        rw [EventStep.actual_next_state]
        simpa only [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step, if_neg same] using unserved
    | deliver address =>
      right
      rw [EventStep.actual_next_state]
      simp only [Reaction.Feedback.advance, chosen, stepLocal, kind, Code.step]
      split
      · exact unserved
      · rename_i packet found
        have member : packet ∈ (EventStep.seed (RetainedIntent.origin start past)).frame.sent := by
          rw [← packets]
          exact List.mem_of_getElem? found
        split
        · dsimp only
          split
          · rename_i recipient
            rw [unserved]
            rw [← recipient]
            exact (RetainedIntent.source_checks vocabulary encoding law start past accepted).2.2 site packet member needed recipient.symm
          · exact unserved
        · exact unserved

theorem every_initial_intent_is_served_or_still_locally_present
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (site : Fin code.sites) (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ []) (n : Nat) :
    (∃ index < n, StageTrace.activation (row vocabulary encoding law start past rival index) = some site) ∨
      (EventStep.seed (cursorAt vocabulary encoding law start past rival n)).frame.inbox site = RetainedIntent.memory start past site := by
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
    rcases ih with ⟨index, bounded, owned⟩ | unserved
    · exact Or.inl ⟨index, by omega, owned⟩
    · rcases an_unserved_intent_keeps_its_own_reading_for_one_actual_step vocabulary encoding law start past rival accepted
        (cursorAt vocabulary encoding law start past rival n) site needed
        (the_entire_window_keeps_the_entry_packet_list vocabulary encoding law start past rival accepted n) unserved with owned | retained
      · exact Or.inl ⟨n, by omega, owned⟩
      · exact Or.inr retained

theorem the_source_roster_services_every_initial_intent_within_its_generated_window
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (budget : ServiceClock.horizon (RetainedIntent.origin start past) ≤ (EventStep.seed (RetainedIntent.origin start past)).remaining)
    (site : Fin code.sites) (needed : RetainedIntent.intent vocabulary encoding law start past site ≠ []) :
    ∃ index < ServiceClock.horizon (RetainedIntent.origin start past),
      StageTrace.activation (row vocabulary encoding law start past rival index) = some site := by
  let arrival := SilentWindow.delay (RetainedIntent.origin start past) site
  have deadline := ServiceClock.the_source_roster_generates_a_service_time (RetainedIntent.origin start past)
    (rule vocabulary encoding law start past) rival site
  rcases every_initial_intent_is_served_or_still_locally_present vocabulary encoding law start past rival accepted site needed arrival with
    ⟨index, earlier, served⟩ | unchanged
  · exact ⟨index, by dsimp only [arrival] at earlier; omega, served⟩
  · have fuel := (ServiceClock.clocks (RetainedIntent.origin start past) (rule vocabulary encoding law start past) rival arrival).2.1
    have within : arrival < ServiceClock.horizon (RetainedIntent.origin start past) := deadline.1
    change (EventStep.seed (cursorAt vocabulary encoding law start past rival arrival)).remaining = _ at fuel
    have live : (EventStep.seed (cursorAt vocabulary encoding law start past rival arrival)).remaining ≠ 0 := by omega
    have registered := (RetainedIntent.source_checks vocabulary encoding law start past accepted).2.1 site needed
    have selected : localEvent code (rule vocabulary encoding law start past) site
        ((EventStep.seed (cursorAt vocabulary encoding law start past rival arrival)).frame.inbox site) = some ⟨.activate site, registered⟩ := by
      rw [RetainedIntent.local_selection vocabulary encoding law start past site _ registered, unchanged]
      simp only [RetainedIntent.work, if_true, if_neg needed]
    exact ⟨arrival, deadline.1, ServiceClock.a_live_owner_executes_its_selected_activation
      (cursorAt vocabulary encoding law start past rival arrival) (rule vocabulary encoding law start past) rival site live deadline.2 registered selected⟩

theorem consumed_memory_stays_consumed_to_the_end
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (site : Fin code.sites) (first last : Nat) (later : first ≤ last)
    (spent : code.memoryReady ((EventStep.seed (cursorAt vocabulary encoding law start past rival first)).frame.inbox site) = false) :
    code.memoryReady ((EventStep.seed (cursorAt vocabulary encoding law start past rival last)).frame.inbox site) = false := by
  induction last, later using Nat.le_induction with
  | base => exact spent
  | succ last _ ih =>
    exact ResponseCapacity.every_actual_cut_preserves_consumed_memory
      (RetainedIntent.source_checks vocabulary encoding law start past accepted).1
      (cursorAt vocabulary encoding law start past rival last) (rule vocabulary encoding law start past) rival site ih

theorem the_generated_window_closes_every_retained_intent
    (accepted : RetainedIntent.inspect vocabulary encoding law start past = true)
    (budget : ServiceClock.horizon (RetainedIntent.origin start past) ≤ (EventStep.seed (RetainedIntent.origin start past)).remaining)
    (site : Fin code.sites) :
    RetainedIntent.work vocabulary encoding law start past site
      ((EventStep.seed (cursorAt vocabulary encoding law start past rival
        (ServiceClock.horizon (RetainedIntent.origin start past)))).frame.inbox site) = [] := by
  by_cases empty : RetainedIntent.intent vocabulary encoding law start past site = []
  · simp [RetainedIntent.work, empty]
  · obtain ⟨index, bounded, owned⟩ := the_source_roster_services_every_initial_intent_within_its_generated_window
      vocabulary encoding law start past rival accepted budget site empty
    have spent := ResponseCapacity.an_owned_action_consumes_its_source_capacity
      (RetainedIntent.source_checks vocabulary encoding law start past accepted).1
      (cursorAt vocabulary encoding law start past rival index) (rule vocabulary encoding law start past) rival site owned
    have final := consumed_memory_stays_consumed_to_the_end vocabulary encoding law start past rival accepted site
      (index + 1) (ServiceClock.horizon (RetainedIntent.origin start past)) (by omega) spent
    have ready := RetainedIntent.an_initial_intent_has_a_ready_local_record vocabulary encoding law start past site empty
    unfold RetainedIntent.work
    split
    · rename_i same
      rw [same, ready] at final
      contradiction
    · rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IntentServiceProgress

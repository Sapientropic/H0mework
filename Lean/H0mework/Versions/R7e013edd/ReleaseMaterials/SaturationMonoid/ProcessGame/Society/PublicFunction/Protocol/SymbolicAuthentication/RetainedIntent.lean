import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceClock

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetainedIntent

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
  (start : Cursor code) (past : List (EventHistory.Stage (code := code)))

abbrev origin := EventHistory.execute start past
abbrev memory (site : Fin code.sites) := (EventStep.seed (origin start past)).frame.inbox site
def intent (site : Fin code.sites) :=
  ReceivedStatementAuthentication.work vocabulary encoding law start (past.map Prod.fst) past.length
    (memory start past site) site (memory start past site)
def work (site : Fin code.sites) (signal : Fin code.signals) :=
  if signal = memory start past site then intent vocabulary encoding law start past site else []

theorem intent_supported (site : Fin code.sites) :
    intent vocabulary encoding law start past site ∈ words code.actions code.actionLimit :=
  ReceivedStatementAuthentication.work_supported vocabulary encoding law start (past.map Prod.fst) past.length
    (memory start past site) site (memory start past site)

theorem an_initial_intent_has_a_ready_local_record (site : Fin code.sites)
    (needed : intent vocabulary encoding law start past site ≠ []) :
    code.memoryReady (memory start past site) = true := by
  by_contra missing
  have noRead : RequestReadback.localRead (code := code) (memory start past site) = none := by
    simp [RequestReadback.localRead, missing]
  have noWork := RequestResponse.missing_local_content_produces_no_work site _ noRead
  simp only [intent, ReceivedStatementAuthentication.work, noWork, if_true] at needed
  exact needed rfl

def policy : code.Policy := fun key _ => work vocabulary encoding law start past key.1 key.2
theorem policy_generated : policy vocabulary encoding law start past ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  unfold policy work
  split
  · exact intent_supported vocabulary encoding law start past key.1
  · exact (mem_words_iff _ _ _).mpr (by simp)

def protocol : Rule code where
  work := ⟨policy vocabulary encoding law start past, policy_generated vocabulary encoding law start past⟩
  events := fun key _ => if work vocabulary encoding law start past key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

def activationCheck : Bool := (List.finRange code.sites).all fun site => decide
  (intent vocabulary encoding law start past site ≠ [] → Event.activate site ∈ code.eventAlphabet)

-- Only packets already present can be delivered: this installed rule never
-- sends, and the external admission filter cannot submit an owned send.
def deliveryCheck : Bool := (List.finRange code.sites).all fun site =>
  (EventStep.seed (origin start past)).frame.sent.all fun packet => decide
    (intent vocabulary encoding law start past site ≠ [] → packet.recipient = site →
      code.afterDelivery site packet.sender (memory start past site) packet.signal = memory start past site)

def inspect : Bool := SourceResponseCapacity.inspect code && activationCheck vocabulary encoding law start past &&
  deliveryCheck vocabulary encoding law start past

theorem source_checks (accepted : inspect vocabulary encoding law start past = true) :
    ResponseCapacity.Absorbing code ∧
    (∀ site, intent vocabulary encoding law start past site ≠ [] → Event.activate site ∈ code.eventAlphabet) ∧
    (∀ site packet, packet ∈ (EventStep.seed (origin start past)).frame.sent →
      intent vocabulary encoding law start past site ≠ [] → packet.recipient = site →
      code.afterDelivery site packet.sender (memory start past site) packet.signal = memory start past site) := by
  have checked : SourceResponseCapacity.inspect code = true ∧ activationCheck vocabulary encoding law start past = true ∧
      deliveryCheck vocabulary encoding law start past = true := by simpa [inspect, and_assoc] using accepted
  refine ⟨SourceResponseCapacity.checked_source_generates_its_absorption_law code checked.1, ?_, ?_⟩
  · intro site
    exact of_decide_eq_true ((List.all_eq_true.mp checked.2.1) site (List.mem_finRange _))
  · intro site packet member
    exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp checked.2.2)
      site (List.mem_finRange _))) packet member)

theorem local_selection (site : Fin code.sites) (signal : Fin code.signals)
    (registered : Event.activate site ∈ code.eventAlphabet) :
    localEvent code (protocol vocabulary encoding law start past) site signal =
      if work vocabulary encoding law start past site signal = [] then none else some ⟨.activate site, registered⟩ := by
  by_cases empty : work vocabulary encoding law start past site signal = []
  · simp only [localEvent, protocol, empty, if_true]
  · simp only [localEvent, protocol, empty, if_false]
    exact ServiceClock.the_registered_activation_is_selected site registered

theorem selection_shape (accepted : inspect vocabulary encoding law start past = true)
    (site : Fin code.sites) (signal : Fin code.signals) :
    localEvent code (protocol vocabulary encoding law start past) site signal = none ∨
      ∃ registered : Event.activate site ∈ code.eventAlphabet,
        localEvent code (protocol vocabulary encoding law start past) site signal = some ⟨.activate site, registered⟩ ∧
        work vocabulary encoding law start past site signal ≠ [] := by
  by_cases empty : work vocabulary encoding law start past site signal = []
  · exact Or.inl (by simp only [localEvent, protocol, empty, if_true])
  · have needed : intent vocabulary encoding law start past site ≠ [] := by
      intro missing
      simp [work, missing] at empty
    have registered := (source_checks vocabulary encoding law start past accepted).2.1 site needed
    exact Or.inr ⟨registered, by rw [local_selection vocabulary encoding law start past site signal registered, if_neg empty], empty⟩

theorem actual_event_shape (accepted : inspect vocabulary encoding law start past = true)
    (cursor : Cursor code) (rival : Opponent code) (event : Choice code)
    (chosen : decision code (EventStep.applied cursor (protocol vocabulary encoding law start past) rival)
      (EventStep.seed cursor) = some event) :
    match event.val with
    | .send _ _ => False
    | .activate site => StageTrace.activation
        (StageTrace.material cursor (protocol vocabulary encoding law start past) rival) = some site
    | .deliver _ | .adversary _ => True := by
  have live : (EventStep.seed cursor).remaining ≠ 0 := by
    intro stopped
    simp only [decision, stopped, if_true] at chosen
    contradiction
  have actual : driver code cursor.ownerStart (protocol vocabulary encoding law start past) rival
      (EventStep.seed cursor).history (EventStep.seed cursor).past (EventStep.seed cursor).frame = some event := by
    simpa only [decision, if_neg live] using chosen
  cases owned : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
  | none =>
    have admitted : Distributed.Recall.Information.Agency.externalChoice code
        (rival (EventStep.seed cursor).history (EventStep.seed cursor).past (EventStep.seed cursor).frame) = some event := by
      simpa only [driver, owned] using actual
    have external := Distributed.Recall.Information.Agency.external_input_cannot_impersonate_a_workers_event code _ event admitted
    cases kind : event.val <;> simp_all
  | some site =>
    have selected : localEvent code (protocol vocabulary encoding law start past) site
        ((EventStep.seed cursor).frame.inbox site) = some event := by simpa only [driver, owned] using actual
    rcases selection_shape vocabulary encoding law start past accepted site _ with empty | ⟨registered, activated, _⟩
    · rw [empty] at selected; contradiction
    · have same := Option.some.inj (selected.symm.trans activated)
      subst event
      exact ServiceClock.a_live_owner_executes_its_selected_activation cursor
        (protocol vocabulary encoding law start past) rival site live owned registered activated

theorem actual_owned_submission_is_the_retained_local_intent
    (cursor : Cursor code) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor (protocol vocabulary encoding law start past) rival) = some site) :
    (StageTrace.material cursor (protocol vocabulary encoding law start past) rival).submitted =
      work vocabulary encoding law start past site ((EventStep.seed cursor).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ _ site owned).2]
  change (if code.memoryReady _ then work vocabulary encoding law start past site _ else []) = _
  split
  · rfl
  · rename_i unreadable
    unfold work
    split
    · rename_i same
      by_cases empty : intent vocabulary encoding law start past site = []
      · exact empty.symm
      · have ready := an_initial_intent_has_a_ready_local_record vocabulary encoding law start past site empty
        rw [same, ready] at unreadable
        contradiction
    · rfl

theorem an_owned_service_submits_the_nonempty_entry_intent
    (cursor : Cursor code) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor (protocol vocabulary encoding law start past) rival) = some site) :
    (StageTrace.material cursor (protocol vocabulary encoding law start past) rival).submitted =
      intent vocabulary encoding law start past site ∧ intent vocabulary encoding law start past site ≠ [] := by
  have nonempty : work vocabulary encoding law start past site ((EventStep.seed cursor).frame.inbox site) ≠ [] := by
    intro empty
    have live := (StageTrace.an_owned_activation_submits_its_selected_work _ _ _ site owned).1
    change (EventStep.seed cursor).remaining ≠ 0 at live
    change (match StageTrace.capture cursor (protocol vocabulary encoding law start past) rival (EventStep.seed cursor) with
      | .own worker (some event) => if event.val = .activate worker then some worker else none
      | _ => none) = some site at owned
    simp only [StageTrace.capture, if_neg live] at owned
    cases owner : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart (EventStep.seed cursor).history.length with
    | none => simp only [owner] at owned; contradiction
    | some worker =>
      simp only [owner] at owned
      cases chosen : localEvent code (protocol vocabulary encoding law start past) worker ((EventStep.seed cursor).frame.inbox worker) with
      | none => simp only [chosen] at owned; contradiction
      | some event =>
        simp only [chosen] at owned
        split_ifs at owned with activated
        · have same := Option.some.inj owned
          subst site
          have absent : localEvent code (protocol vocabulary encoding law start past) worker ((EventStep.seed cursor).frame.inbox worker) = none := by
            simp only [localEvent, protocol, empty, if_true]
          rw [absent] at chosen
          contradiction
  have submitted := actual_owned_submission_is_the_retained_local_intent vocabulary encoding law start past cursor rival site owned
  unfold work at nonempty submitted
  split at nonempty
  · rename_i same
    simpa only [if_pos same] using And.intro submitted nonempty
  · contradiction

theorem retained_intent_has_its_original_paid_receipt (site : Fin code.sites)
    (needed : intent vocabulary encoding law start past site ≠ []) :
    ∃ body ∈ (ReceivedStatementAuthentication.generate vocabulary encoding law start (past.map Prod.fst) past.length
      (memory start past site) site (memory start past site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start past site past.length).receipts,
        receipt.statement = body := by
  have snapshot := ReceivedStatementAuthentication.the_entering_snapshot_is_an_actual_local_record start past [] site
  rw [List.append_nil] at snapshot
  have supported := ReceivedStatementAuthentication.nonempty_work_has_actual_paid_communication_support
    vocabulary encoding law start past past.length site
  rw [snapshot] at supported
  obtain ⟨body, known, receipt, received, same, _, _⟩ := supported needed
  exact ⟨body, known, receipt, received, same⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetainedIntent

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptAuthentication

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedStatementAuthentication

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code) (start : Cursor code) (installed : List (Rule code))

abbrev reading (trace : List (EventHistory.Stage (code := code))) (site : Fin code.sites) :=
  (EventStep.seed (EventHistory.execute start trace)).frame.inbox site

def remembered (trace : List (EventHistory.Stage (code := code))) (observedAt : Nat) (site : Fin code.sites) :=
  match (StageTrace.records start trace)[observedAt]? with
  | none => reading start trace site
  | some row => row.before.frame.inbox site

theorem the_entering_snapshot_is_an_actual_local_record
    (past more : List (EventHistory.Stage (code := code))) (site : Fin code.sites) :
    remembered start (past ++ more) past.length site = reading start past site := by
  cases more with
  | nil =>
    unfold remembered
    rw [List.append_nil, List.getElem?_eq_none_iff.mpr (by rw [StageTrace.record_count])]
  | cons stage tail =>
    unfold remembered
    rw [StageQueue.records_append, List.getElem?_append_right (by rw [StageTrace.record_count])]
    simp only [StageTrace.record_count, Nat.sub_self, StageTrace.records, List.getElem?_cons_zero]
    rfl

def fibre (observedAt : Nat) (memory : Fin code.signals) (site : Fin code.sites) (signal : Fin code.signals) :=
  (ReceivedLocalDomain.domain start installed).filter fun trace =>
    remembered start trace observedAt site == memory && reading start trace site == signal


def claims (count : Nat) (site : Fin code.sites) (trace : List (EventHistory.Stage (code := code))) :=
  (LocalReceiptAuthentication.claims vocabulary encoding law start count site trace).map RequestReadback.ReceiptData.statement

def shared (count : Nat) (site : Fin code.sites) : List (List (EventHistory.Stage (code := code))) →
    List (RequestAttestation.Statement (code := code))
  | [] => []
  | first :: rest => (claims vocabulary encoding law start count site first).eraseDups.filter fun body =>
      rest.all fun trace => decide (body ∈ claims vocabulary encoding law start count site trace)

abbrev Result := LocalRequestAuthentication.Result (code := code)

-- Each compatible history supplies its own real receipt. Only complete source
-- statements are compared across histories; receipt timestamps remain local facts.
def generate (observedAt : Nat) (memory : Fin code.signals) (site : Fin code.sites) (signal : Fin code.signals) : Result (code := code) :=
  let compatible := fibre start installed observedAt memory site signal
  let statements := shared vocabulary encoding law start installed.length site compatible
  ⟨if compatible = [] then .unseen else if statements = [] then .unauthenticated else .authenticated,
    compatible.length, statements⟩

theorem every_shared_statement_has_its_own_accepted_receipt_in_each_history
    (count : Nat) (site : Fin code.sites) (traces : List (List (EventHistory.Stage (code := code))))
    (body : RequestAttestation.Statement (code := code))
    (known : body ∈ shared vocabulary encoding law start count site traces)
    (trace : List (EventHistory.Stage (code := code))) (inside : trace ∈ traces) :
    ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start trace site count).receipts,
      receipt.statement = body ∧
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start trace)).frame.inbox site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start trace)).current := by
  have member : body ∈ claims vocabulary encoding law start count site trace := by
    cases traces with
    | nil => simp only [shared, List.not_mem_nil] at known
    | cons first rest =>
      obtain ⟨initial, uniform⟩ := List.mem_filter.mp known
      rcases List.mem_cons.mp inside with same | later
      · exact same ▸ List.mem_eraseDups.mp initial
      · exact of_decide_eq_true ((List.all_eq_true.mp uniform) trace later)
  obtain ⟨receipt, received, same⟩ := List.mem_map.mp member
  obtain ⟨actual, properties⟩ := List.mem_filter.mp received
  obtain ⟨read, scope⟩ := of_decide_eq_true properties
  exact ⟨receipt, actual, same, by simpa only [same] using read, by simpa only [same] using scope⟩

theorem locally_known_statements_generate_an_actual_receipt_without_shared_delivery_metadata
    (stages : List (EventHistory.Stage (code := code))) (observedAt : Nat) (site : Fin code.sites)
    (body : RequestAttestation.Statement (code := code))
    (known : body ∈ (generate vocabulary encoding law start (stages.map Prod.fst) observedAt (remembered start stages observedAt site) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site)).statements) :
    ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start stages site stages.length).receipts,
      receipt.statement = body ∧
      RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some body.request ∧
      body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  obtain ⟨trace, inside, matched, rows⟩ := ReceivedLocalDomain.actual_prefix_coverage start stages
  have receipts := ReceiptObservation.produce_equal vocabulary encoding law start trace stages rows
  have memory : remembered start trace observedAt site = remembered start stages observedAt site := by
    unfold remembered
    rw [show reading start trace site = reading start stages site by simp only [reading, matched.state]]
    apply CommunicationObservation.lookup_congr rows observedAt (reading start stages site)
    intro left right same
    exact congrArg (fun state : State code => state.frame.inbox site) same.before
  have member : trace ∈ fibre start (stages.map Prod.fst) observedAt (remembered start stages observedAt site) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) :=
    List.mem_filter.mpr ⟨inside, by simp only [memory, reading, matched.state, beq_self_eq_true, Bool.and_self]⟩
  obtain ⟨receipt, received, same, read, scope⟩ := every_shared_statement_has_its_own_accepted_receipt_in_each_history
    vocabulary encoding law start (stages.map Prod.fst).length site _ body known trace member
  refine ⟨receipt, ?_, same, ?_, ?_⟩
  · simpa only [List.length_map, receipts] using received
  · simpa only [matched.state] using read
  · simpa only [matched.state] using scope

def work (observedAt : Nat) (memory : Fin code.signals) (site : Fin code.sites) (signal : Fin code.signals) :=
  if RequestResponse.work site signal = [] then []
  else if (generate vocabulary encoding law start installed observedAt memory site signal).statements = [] then []
  else RequestResponse.work site signal

theorem work_supported (observedAt : Nat) (memory : Fin code.signals) (site : Fin code.sites) (signal : Fin code.signals) :
    work vocabulary encoding law start installed observedAt memory site signal ∈ words code.actions code.actionLimit := by
  unfold work
  split
  · exact (mem_words_iff _ _ _).mpr (by simp)
  · split
    · exact (mem_words_iff _ _ _).mpr (by simp)
    · exact RequestResponse.work_supported _ _

theorem local_work_factors_through_the_public_prefix_and_own_two_records
    (left right : List (EventHistory.Stage (code := code))) (observedAt : Nat) (site : Fin code.sites)
    (sameRules : left.map Prod.fst = right.map Prod.fst)
    (memory : remembered start left observedAt site = remembered start right observedAt site)
    (current : reading start left site = reading start right site) :
    work vocabulary encoding law start (left.map Prod.fst) observedAt (remembered start left observedAt site) site (reading start left site) =
      work vocabulary encoding law start (right.map Prod.fst) observedAt (remembered start right observedAt site) site (reading start right site) := by
  rw [sameRules, memory, current]

def policy (observedAt : Nat) (memory : Fin code.sites → Fin code.signals) : code.Policy :=
  fun key _ => work vocabulary encoding law start installed observedAt (memory key.1) key.1 key.2

theorem policy_generated (observedAt : Nat) (memory : Fin code.sites → Fin code.signals) :
    policy vocabulary encoding law start installed observedAt memory ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact work_supported vocabulary encoding law start installed observedAt (memory key.1) key.1 key.2

def protocol (observedAt : Nat) (memory : Fin code.sites → Fin code.signals) : Rule code where
  work := ⟨policy vocabulary encoding law start installed observedAt memory, policy_generated vocabulary encoding law start installed observedAt memory⟩
  events := fun key _ => if work vocabulary encoding law start installed observedAt (memory key.1) key.1 key.2 = [] then
    ⟨none, List.mem_cons_self⟩ else RequestResponse.activation key.1

theorem an_owned_activation_submits_the_locally_authenticated_word
    (past : List (EventHistory.Stage (code := code))) (observedAt : Nat) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material (EventHistory.execute start past)
      (protocol vocabulary encoding law start (past.map Prod.fst) observedAt (remembered start past observedAt)) rival) = some site) :
    (StageTrace.material (EventHistory.execute start past) (protocol vocabulary encoding law start (past.map Prod.fst) observedAt (remembered start past observedAt)) rival).submitted =
      work vocabulary encoding law start (past.map Prod.fst) observedAt (remembered start past observedAt site) site
        ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) := by
  rw [(StageTrace.an_owned_activation_submits_its_selected_work _ _ rival site owned).2]
  change (if code.memoryReady _ then work vocabulary encoding law start _ observedAt (remembered start past observedAt site) site _ else []) = _
  split
  · rfl
  · rename_i unreadable
    have empty := RequestResponse.missing_local_content_produces_no_work site
      ((EventStep.seed (EventHistory.execute start past)).frame.inbox site) (by
      simp [RequestReadback.localRead, unreadable])
    simp [work, empty]

theorem nonempty_work_has_actual_paid_communication_support
    (stages : List (EventHistory.Stage (code := code))) (observedAt : Nat) (site : Fin code.sites)
    (needed : work vocabulary encoding law start (stages.map Prod.fst) observedAt (remembered start stages observedAt site) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) ≠ []) :
    ∃ body ∈ (generate vocabulary encoding law start (stages.map Prod.fst) observedAt (remembered start stages observedAt site) site
      ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site)).statements,
      ∃ receipt ∈ (RequestReadback.produce vocabulary encoding law start stages site stages.length).receipts,
        receipt.statement = body ∧
        RequestReadback.localRead (code := code) ((EventStep.seed (EventHistory.execute start stages)).frame.inbox site) = some body.request ∧
        body.ballot.scope = law.scope site (EventStep.seed (EventHistory.execute start stages)).current := by
  unfold work at needed
  split at needed
  · contradiction
  · split at needed
    · contradiction
    · rename_i present
      obtain ⟨body, inside⟩ := List.exists_mem_of_ne_nil _ present
      exact ⟨body, inside, locally_known_statements_generate_an_actual_receipt_without_shared_delivery_metadata
        vocabulary encoding law start stages observedAt site body inside⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedStatementAuthentication

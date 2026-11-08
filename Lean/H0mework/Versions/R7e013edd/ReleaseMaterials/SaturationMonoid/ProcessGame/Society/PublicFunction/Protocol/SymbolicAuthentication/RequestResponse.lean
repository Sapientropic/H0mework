import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadbackRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponse

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- An echo is a new actor's own resource request. Reading another actor's text
-- does not supply that actor's signature or authorize an inherited request.
def ownReply (actor : Party) (incoming : RequestAttestation.Request (Party := Party)
    (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Option (RequestAttestation.Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :=
  if RequestAttestation.protocolSyntax incoming then
    match incoming.operation with
    | .use _ goods .external => some {incoming with signer := actor, operation := .use actor goods .external}
    | _ => none
  else none

def selected (site : Fin code.sites) (reading : Fin code.signals) :=
  match RequestReadback.localRead (code := code) reading with
  | none => none
  | some incoming => match ownReply (code.siteParty site) incoming with
    | none => none
    | some reply => if reply ∈ code.actions then some reply else none

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem own_reply_uses_the_responding_actor
    (actor : Party) (incoming reply : RequestAttestation.Request (Party := Party)
      (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (made : ownReply actor incoming = some reply) : reply.signer = actor := by
  unfold ownReply at made
  split at made <;> try contradiction
  split at made <;> try contradiction
  cases Option.some.inj made
  rfl

theorem selection_retains_the_local_input_and_own_registered_reply
    (site : Fin code.sites) (reading : Fin code.signals)
    (reply : RequestAttestation.Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (made : selected (code := code) site reading = some reply) :
    ∃ incoming, RequestReadback.localRead (code := code) reading = some incoming ∧
      ownReply (code.siteParty site) incoming = some reply ∧ reply.signer = code.siteParty site ∧ reply ∈ code.actions := by
  unfold selected at made
  split at made <;> try contradiction
  rename_i incoming read
  split at made <;> try contradiction
  rename_i candidate authored
  split at made <;> try contradiction
  rename_i registered
  cases Option.some.inj made
  exact ⟨incoming, read, authored, own_reply_uses_the_responding_actor _ _ _ authored, registered⟩

theorem selected_is_in_the_original_action_alphabet
    (site : Fin code.sites) (reading : Fin code.signals)
    (reply : RequestAttestation.Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (made : selected (code := code) site reading = some reply) : reply ∈ code.actions := by
  unfold selected at made
  split at made <;> try contradiction
  split at made <;> try contradiction
  split at made <;> try contradiction
  cases Option.some.inj made
  assumption

def work (site : Fin code.sites) (reading : Fin code.signals) :=
  if code.actionLimit = 0 then [] else (selected (code := code) site reading).toList

theorem work_supported (site : Fin code.sites) (reading : Fin code.signals) :
    work (code := code) site reading ∈ words code.actions code.actionLimit := by
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split
  · simp
  · rename_i positive
    cases made : selected (code := code) site reading with
    | none => simp
    | some reply =>
      refine ⟨by simp; omega, ?_⟩
      simpa using selected_is_in_the_original_action_alphabet site reading reply made

def policy : code.Policy := fun key _ => work key.1 key.2

theorem every_submitted_reply_has_its_local_input_and_own_registered_signer
    (site : Fin code.sites) (reading : Fin code.signals)
    (reply : RequestAttestation.Request (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (inside : reply ∈ work (code := code) site reading) :
    ∃ incoming, RequestReadback.localRead (code := code) reading = some incoming ∧
      ownReply (code.siteParty site) incoming = some reply ∧ reply.signer = code.siteParty site ∧ reply ∈ code.actions := by
  unfold work at inside
  split at inside <;> try contradiction
  cases made : selected (code := code) site reading with
  | none => simp only [made, Option.toList_none, List.not_mem_nil] at inside
  | some candidate =>
    simp only [made, Option.toList_some, List.mem_singleton] at inside
    subst candidate
    exact selection_retains_the_local_input_and_own_registered_reply site reading reply made

theorem missing_local_content_produces_no_work
    (site : Fin code.sites) (reading : Fin code.signals)
    (absent : RequestReadback.localRead (code := code) reading = none) :
    work (code := code) site reading = [] := by
  simp only [work, selected, absent]
  split <;> rfl

theorem policy_generated : policy (code := code) ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact work_supported key.1 key.2

def activates (site : Fin code.sites) (move : Move code) : Bool :=
  match move with
  | some event => decide (event.val = .activate site)
  | none => false

def activation (site : Fin code.sites) : LocalMove code site :=
  match ((ownMoves code site).attach.find? fun move => activates site move.val) with
  | some move => move
  | none => ⟨none, List.mem_cons_self⟩

def protocol : Rule code where
  work := ⟨policy, policy_generated⟩
  events := fun key _ => if work key.1 key.2 = [] then ⟨none, List.mem_cons_self⟩ else activation key.1

theorem identical_local_records_generate_identical_responses
    (site : Fin code.sites) (first second : Fin code.signals) (same : first = second) :
    work (code := code) site first = work site second := congrArg (work site) same

theorem an_actual_owned_response_submits_only_its_current_local_word
    (cursor : Cursor code) (rival : Opponent code) (site : Fin code.sites)
    (owned : StageTrace.activation (StageTrace.material cursor protocol rival) = some site) :
    (StageTrace.material cursor protocol rival).submitted =
      work site ((EventStep.seed cursor).frame.inbox site) := by
  have actual := (StageTrace.an_owned_activation_submits_its_selected_work cursor protocol rival site owned).2
  rw [actual]
  change (if code.memoryReady _ then work site _ else []) = _
  split
  · rfl
  · rename_i unreadable
    simp only [work, selected, RequestReadback.localRead, unreadable]
    split <;> rfl

-- The original cursor executes the generated local rule at every remaining cut;
-- unrestricted external turns still use the actual adaptive opponent.
def run (start : Cursor code) (rival : Opponent code) : Nat →
    List (EventHistory.Stage (code := code)) → List (EventHistory.Stage (code := code))
  | 0, past => past
  | rounds + 1, past =>
    if (EventStep.seed (EventHistory.execute start past)).remaining = 0 then past
    else run start rival rounds (past ++ [(protocol, rival)])

def produce (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) :=
  run start rival (EventStep.seed (EventHistory.execute start past)).remaining past

theorem every_run_is_an_actual_local_protocol_suffix
    (start : Cursor code) (rival : Opponent code) (rounds : Nat)
    (past : List (EventHistory.Stage (code := code))) :
    ∃ count ≤ rounds, run start rival rounds past = past ++ List.replicate count (protocol, rival) := by
  induction rounds generalizing past with
  | zero => exact ⟨0, Nat.le_refl _, by simp [run]⟩
  | succ rounds ih =>
    simp only [run]
    split
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · obtain ⟨count, bounded, same⟩ := ih (past ++ [(protocol, rival)])
      refine ⟨count + 1, by omega, ?_⟩
      rw [same, List.append_assoc]
      simp [List.replicate_succ]

theorem the_producer_keeps_the_complete_actual_prefix
    (start : Cursor code) (past : List (EventHistory.Stage (code := code))) (rival : Opponent code) :
    past <+: produce start past rival := by
  obtain ⟨count, _, same⟩ := every_run_is_an_actual_local_protocol_suffix start rival
    (EventStep.seed (EventHistory.execute start past)).remaining past
  rw [produce, same]
  exact List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponse

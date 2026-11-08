import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorEnvelope

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorQuorum
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Repeated keys and repeated receipts of a single source owner contribute one identity.
def support (observed : StageReception.Receiver (code := code)) (scope : Scope) (value : Bool) : Finset Party :=
  (StageQuorum.support observed scope value).image code.siteParty

omit [DecidableEq Port] [DecidableEq Technology] in
theorem mem_support_iff (observed : StageReception.Receiver (code := code)) (scope : Scope) (value : Bool) (actor : Party) :
    actor ∈ support observed scope value ↔ ∃ key ∈ StageQuorum.support observed scope value, code.siteParty key = actor :=
  Finset.mem_image

def readout (observed : StageReception.Receiver (code := code)) (scope : Scope) (threshold : Nat) : Quorum.ReadoutData Bool :=
  if threshold = 0 then .blocked else
  match [false,true].find? (fun value => decide (threshold ≤ (support observed scope value).card)) with
  | none => .blocked
  | some value => .decided value

omit [DecidableEq Port] [DecidableEq Technology] in
theorem decision_has_positive_distinct_actor_support
    (observed : StageReception.Receiver (code := code)) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : readout observed scope threshold = .decided value) :
    0 < threshold ∧ threshold ≤ (support observed scope value).card := by
  unfold readout at done
  split at done <;> try contradiction
  rename_i positive
  split at done <;> try contradiction
  rename_i chosen found
  cases Quorum.ReadoutData.decided.inj done
  exact ⟨Nat.pos_of_ne_zero positive,of_decide_eq_true
    (List.find?_some (p := fun value => decide (threshold ≤ (support observed scope value).card)) found)⟩

variable (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev observed := InterfaceQuorum.observed start vocabulary

theorem actual_supporter_has_its_verified_native_origin
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (value : Bool) (actor : Party)
    (inside : actor ∈ support (observed start vocabulary encoding law stages receiver) scope value) :
    ∃ receipt ∈ (observed start vocabulary encoding law stages receiver).receipts,
      receipt.wire.ballot ∈ StageBudget.ledger vocabulary start stages ∧
      receipt.wire.ballot.actor = actor ∧ receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value := by
  obtain ⟨key,member,owner⟩ := (mem_support_iff _ scope value actor).mp inside
  obtain ⟨receipt,present,sameScope,choice,sameKey⟩ := (StageQuorum.mem_support_iff _ scope value key).mp member
  have origin := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law start stages
    receiver stages.length receipt present
  have exactActor := ActorEnvelope.actual_ballot_retains_the_original_actor vocabulary start stages _ origin
  exact ⟨receipt,present,origin,by rw [exactActor,sameKey,owner],sameScope,choice⟩

theorem every_received_identity_is_in_the_original_roster
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (value : Bool) :
    support (observed start vocabulary encoding law stages receiver) scope value ⊆ ActorEnvelope.roster start.source := by
  intro actor member
  obtain ⟨key,_,owner⟩ := (mem_support_iff _ scope value actor).mp member
  exact Finset.mem_image.mpr ⟨key,Finset.mem_univ _,owner⟩

theorem opposite_support_exposes_source_control_even_when_the_keys_differ
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (a b : Bool) (different : a ≠ b) :
    support (observed start vocabulary leftEncoding leftLaw leftStages left) scope a ∩
      support (observed start vocabulary rightEncoding rightLaw rightStages right) scope b ⊆
        ActorEnvelope.affected start.source vocabulary scope := by
  intro actor member
  obtain ⟨one,_,first,actorOne,scopeOne,valueOne⟩ := actual_supporter_has_its_verified_native_origin start vocabulary
    leftEncoding leftLaw leftStages left scope a actor (Finset.mem_inter.mp member).1
  obtain ⟨two,_,second,actorTwo,scopeTwo,valueTwo⟩ := actual_supporter_has_its_verified_native_origin start vocabulary
    rightEncoding rightLaw rightStages right scope b actor (Finset.mem_inter.mp member).2
  have exposed := ActorEnvelope.conflicting_actual_ballots_expose_an_affected_actor_even_across_distinct_keys vocabulary
    start leftStages rightStages scope one.wire.ballot two.wire.ballot first second (actorOne.trans actorTwo.symm)
    scopeOne scopeTwo (by intro same;exact different (valueOne.symm.trans (same.trans valueTwo)))
  simpa only [actorOne] using exposed

theorem supported_values_agree_across_actual_histories_encodings_and_reception_laws
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (first : threshold ≤ (support (observed start vocabulary leftEncoding leftLaw leftStages left) scope a).card)
    (second : threshold ≤ (support (observed start vocabulary rightEncoding rightLaw rightStages right) scope b).card)
    (safe : (ActorEnvelope.roster start.source).card + ActorEnvelope.budget start.source vocabulary scope < threshold + threshold) : a = b := by
  by_contra different
  have overlap := Finset.card_le_card (opposite_support_exposes_source_control_even_when_the_keys_differ start vocabulary
    leftEncoding rightEncoding leftLaw rightLaw leftStages rightStages left right scope a b different)
  have union := Finset.card_le_card (Finset.union_subset
    (every_received_identity_is_in_the_original_roster start vocabulary leftEncoding leftLaw leftStages left scope a)
    (every_received_identity_is_in_the_original_roster start vocabulary rightEncoding rightLaw rightStages right scope b))
  have count := Finset.card_union_add_card_inter
    (support (observed start vocabulary leftEncoding leftLaw leftStages left) scope a)
    (support (observed start vocabulary rightEncoding rightLaw rightStages right) scope b)
  unfold ActorEnvelope.budget at safe
  omega

-- The source fixes both the owner roster and the cross-key control budget before reception.
def produce (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) : ProspectiveQuorum.Result :=
  if ¬ (ActorEnvelope.roster start.source).card + ActorEnvelope.budget start.source vocabulary scope < threshold + threshold then
    .blocked .unsafeSourceBudget
  else match readout (observed start vocabulary encoding law stages receiver) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem produced_decision_consumes_the_source_budget_and_actual_distinct_actors
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : produce start vocabulary encoding law stages receiver scope threshold = .decided value) :
    (ActorEnvelope.roster start.source).card + ActorEnvelope.budget start.source vocabulary scope < threshold + threshold ∧
      readout (observed start vocabulary encoding law stages receiver) scope threshold = .decided value ∧
      0 < threshold ∧ threshold ≤ (support (observed start vocabulary encoding law stages receiver) scope value).card := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i answer found
  cases done
  exact ⟨of_not_not safe,found,decision_has_positive_distinct_actor_support _ _ _ _ found⟩

theorem all_source_generated_actor_decisions_agree
    (leftEncoding rightEncoding : StageTransport.Encoding (code := code))
    (leftLaw rightLaw : StageReception.Law code)
    (leftStages rightStages : List (EventHistory.Stage (code := code))) (left right : Fin code.sites)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (first : produce start vocabulary leftEncoding leftLaw leftStages left scope threshold = .decided a)
    (second : produce start vocabulary rightEncoding rightLaw rightStages right scope threshold = .decided b) : a = b := by
  obtain ⟨safe,_,_,one⟩ := produced_decision_consumes_the_source_budget_and_actual_distinct_actors start vocabulary _ _ _ _ _ _ _ first
  obtain ⟨_,_,_,two⟩ := produced_decision_consumes_the_source_budget_and_actual_distinct_actors start vocabulary _ _ _ _ _ _ _ second
  exact supported_values_agree_across_actual_histories_encodings_and_reception_laws start vocabulary
    leftEncoding rightEncoding leftLaw rightLaw leftStages rightStages left right scope threshold a b one two safe

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActorQuorum

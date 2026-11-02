import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ApplicationSubject

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SubjectQuorum

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

inductive Obstruction where
  | outsideBudgetWindow | unsafeBudget | missingSourceSubject | missingQuorum
  deriving DecidableEq

inductive ResultData (Subject : Type) where
  | blocked (reason : Obstruction)
  | decided (choice : Bool) (subject : Subject)
  deriving DecidableEq

abbrev Result := ResultData (ApplicationSubject.Subject source)
abbrev observed (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) :=
  ApplicationSubject.received source input cut protocol rival vocabulary encoding law receiver count scope

/-- Each counted vote binds the exact source-resolved subject. No subject,
receipt list, certificate, or completed decision is supplied to this producer. -/
def produce (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat) : Result source :=
  if ¬ count ≤ horizon then .blocked .outsideBudgetWindow
  else if ¬ source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold then
    .blocked .unsafeBudget
  else match ApplicationSubject.resolve source input cut protocol rival vocabulary scope with
    | none => .blocked .missingSourceSubject
    | some subject =>
      match BallotQuorum.readout source (observed source input cut protocol rival vocabulary encoding law receiver count scope) scope threshold with
      | .blocked => .blocked .missingQuorum
      | .decided choice => .decided choice subject

theorem decision_has_source_subject_budget_and_bound_quorum
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (value : Bool) (subject : ApplicationSubject.Subject source)
    (done : produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold = .decided value subject) :
    count ≤ horizon ∧
      source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold ∧
      ApplicationSubject.resolve source input cut protocol rival vocabulary scope = some subject ∧
      BallotQuorum.readout source (observed source input cut protocol rival vocabulary encoding law receiver count scope) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i bounded
  split at done <;> try contradiction
  rename_i budget
  split at done <;> try contradiction
  rename_i generated resolved
  split at done <;> try contradiction
  rename_i choice actual
  cases done
  exact ⟨of_not_not bounded, of_not_not budget, resolved, actual⟩

theorem supported_values_agree
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (leftBound : leftCount ≤ horizon) (rightBound : rightCount ≤ horizon)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : threshold ≤ (BallotQuorum.support source
      (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a).card)
    (two : threshold ≤ (BallotQuorum.support source
      (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold) : a = b := by
  by_contra different
  have exposed := Finset.card_le_card (BallotQuorum.conflicting_intersection_is_in_source_budget source input cut protocol rival
    vocabulary encoding law left right leftCount rightCount horizon leftBound rightBound scope a b different)
  have union : (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
      BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card ≤ source.code.sites := by
    simpa only [Fintype.card_fin] using (BallotQuorum.support source
      (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∪
        BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card_le_univ
  have count := Finset.card_union_add_card_inter
    (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a)
    (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b)
  change (BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law left leftCount) scope a ∩
    BallotQuorum.support source (BallotQuorum.observed source input cut protocol rival vocabulary encoding law right rightCount) scope b).card ≤
      DeviationBudget.budget source input cut protocol rival vocabulary horizon at exposed
  omega

theorem agreement_on_choice_and_entire_application_subject
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (first second : ApplicationSubject.Subject source)
    (one : produce source input cut protocol rival vocabulary encoding law left leftCount horizon scope threshold = .decided a first)
    (two : produce source input cut protocol rival vocabulary encoding law right rightCount horizon scope threshold = .decided b second) :
    a = b ∧ first = second := by
  obtain ⟨leftBound, budget, firstOrigin, firstQuorum⟩ := decision_has_source_subject_budget_and_bound_quorum
    source input cut protocol rival vocabulary encoding law left leftCount horizon scope threshold a first one
  obtain ⟨rightBound, _, secondOrigin, secondQuorum⟩ := decision_has_source_subject_budget_and_bound_quorum
    source input cut protocol rival vocabulary encoding law right rightCount horizon scope threshold b second two
  have firstEnough := le_trans (BallotQuorum.decided_has_positive_quorum source _ scope threshold a firstQuorum).2
    (Finset.card_le_card (ApplicationSubject.support_is_from_the_actual_receiver source input cut protocol rival vocabulary encoding law
      left leftCount scope a))
  have secondEnough := le_trans (BallotQuorum.decided_has_positive_quorum source _ scope threshold b secondQuorum).2
    (Finset.card_le_card (ApplicationSubject.support_is_from_the_actual_receiver source input cut protocol rival vocabulary encoding law
      right rightCount scope b))
  exact ⟨supported_values_agree source input cut protocol rival vocabulary encoding law left right leftCount rightCount horizon
    leftBound rightBound scope threshold a b firstEnough secondEnough budget, Option.some.inj (firstOrigin.symm.trans secondOrigin)⟩

theorem every_supporting_key_refers_to_the_same_actual_subject
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (value : Bool) (subject : ApplicationSubject.Subject source)
    (done : produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold = .decided value subject)
    (key : Fin source.code.sites)
    (inside : key ∈ BallotQuorum.support source
      (observed source input cut protocol rival vocabulary encoding law receiver count scope) scope value) :
    ∃ receipt ∈ (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count).receipts,
      receipt.wire.ballot.key = key ∧ receipt.wire.ballot.choice = value ∧
      ApplicationSubject.bindAt source input cut protocol rival vocabulary scope receipt.wire.ballot = some subject := by
  have resolved := (decision_has_source_subject_budget_and_bound_quorum source input cut protocol rival vocabulary encoding law
    receiver count horizon scope threshold value subject done).2.2.1
  obtain ⟨receipt, present, _, choice, sameKey⟩ := (BallotQuorum.mem_support_iff source _ scope value key).mp inside
  obtain ⟨actual, other, bound⟩ := ApplicationSubject.received_members_have_the_original_receipt_and_subject
    source input cut protocol rival vocabulary encoding law receiver count scope receipt present
  have otherOrigin := (ApplicationSubject.bound_vote_is_authenticated_causal_and_on_the_same_subject
    source input cut protocol rival vocabulary scope receipt.wire.ballot other bound).2.2.1
  have same := Option.some.inj (otherOrigin.symm.trans resolved)
  exact ⟨receipt, actual, sameKey, choice, same ▸ bound⟩

section NativeConsumer

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (actualInput : Input bound.source.code) (actualCut : Nat)
  (actualProtocol : Distributed.Recall.Information.Agency.Protocol.Rule bound.source.code)
  (actualRival : Opponent bound.source.code)
  (actualEncoding : AttestationTransport.Encoding bound.source)
  (actualLaw : AttestationReception.ReceptionLaw bound.source)
  (empty : bound.source.continuation = [])

theorem decision_consumes_the_original_subject_payment_responsibility_and_next
    (receiver : Fin bound.source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (value : Bool) (subject : ApplicationSubject.Subject bound.source)
    (done : produce bound.source actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw
      receiver count horizon scope threshold = .decided value subject) :
    let n := ApplicationSubject.originCut bound.source actualCut scope
    let consumed := ControlResponsibility.produce bound actualInput actualCut actualProtocol actualRival
      vocabulary actualEncoding actualLaw empty n
    let runtime := ControlResponsibility.runtime bound actualInput actualCut actualProtocol actualRival
      vocabulary actualEncoding actualLaw empty n
    n < count ∧
      (∃ item, (item, true) ∈ consumed.requests ∧ 0 < subject.2.amount ∧
        flowAt (bound.source.code.law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
        flowAt (bound.source.code.law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
        (bound.source.code.law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
          subject.2.priorClaim - subject.2.quantity) ∧
      consumed.responsibility.current = Native.Authority.fullGenerate
        (ControlResponsibility.actualBound bound actualInput actualCut actualProtocol actualRival)
        (ControlResponsibility.depth bound actualCut n) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade bound actualInput actualCut actualProtocol actualRival
        vocabulary actualEncoding actualLaw empty).process.stateAt
          ((CommunicationRuntime.facade bound actualInput actualCut actualProtocol actualRival
            vocabulary actualEncoding actualLaw empty).process.successor runtime.state) := by
  have info := decision_has_source_subject_budget_and_bound_quorum bound.source actualInput actualCut actualProtocol actualRival
    vocabulary actualEncoding actualLaw receiver count horizon scope threshold value subject done
  obtain ⟨positive, enough⟩ := BallotQuorum.decided_has_positive_quorum bound.source _ scope threshold value info.2.2.2
  obtain ⟨key, present⟩ := Finset.card_pos.mp (lt_of_lt_of_le positive enough)
  obtain ⟨receipt, received, _, _, boundVote⟩ := every_supporting_key_refers_to_the_same_actual_subject
    bound.source actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw
    receiver count horizon scope threshold value subject done key present
  have causal := (ApplicationSubject.bound_vote_is_authenticated_causal_and_on_the_same_subject bound.source actualInput actualCut actualProtocol
    actualRival vocabulary scope receipt.wire.ballot subject boundVote).2.2.2
  have earlier := (BallotQuorum.receipt_ballot_has_actual_origin bound.source actualInput actualCut actualProtocol actualRival
    vocabulary actualEncoding actualLaw receiver count receipt received).2
  have coordinates := ApplicationSubject.resolved_origin_coordinates bound.source actualInput actualCut actualProtocol actualRival
    vocabulary scope subject info.2.2.1
  have original := (ApplicationSubject.resolved_has_original_confirmation_and_exact_address bound.source actualInput actualCut actualProtocol actualRival
    vocabulary scope subject info.2.2.1).1
  obtain ⟨item, inventory, valid, _, _, positiveAmount, debit, credit, claims, _⟩ :=
    AttestationConsumer.confirmed_payment_enters_the_original_finance_inventory_and_next bound.source actualInput actualCut actualProtocol actualRival
      vocabulary (ApplicationSubject.originCut bound.source actualCut scope) scope.instanceId subject.1 subject.2 original
  have rooted := ControlResponsibility.original_native_histories_and_root_next_are_consumed_together
    bound actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw empty
      (ApplicationSubject.originCut bound.source actualCut scope)
  refine ⟨?_, ⟨item, ?_, positiveAmount, debit, credit, claims⟩, rooted.1, rooted.2.2.2.1, rooted.2.2.2.2⟩
  · unfold ApplicationSubject.precedes at causal
    omega
  · change (item, true) ∈ (ControlResponsibility.items bound actualInput actualCut actualProtocol actualRival
      (ApplicationSubject.originCut bound.source actualCut scope)).map _
    exact List.mem_map.mpr ⟨item, inventory, by simp [valid]⟩

end NativeConsumer

omit rival

def availableAt (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (horizon send : Nat) : Option (Fin source.code.sites) :=
  match ReceiptProgress.plan source input cut protocol vocabulary encoding law send with
  | .blocked _ => none
  | .ready wire =>
    if wire.recipient = receiver ∧ wire.ballot.scope = scope ∧ wire.ballot.choice = value ∧
        ReceiptProgress.deadline source send ≤ horizon ∧
        (ApplicationSubject.bindAt source input cut protocol (QueueScheduler.environment source input cut) vocabulary scope wire.ballot).isSome
    then some wire.ballot.key else none

def readySupport (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon : Nat) : Finset (Fin source.code.sites) :=
  ((List.range count).filterMap (availableAt source input cut protocol vocabulary encoding law receiver scope value horizon)).toFinset

theorem generated_support_is_received_and_content_bound
    (receiver : Fin source.code.sites) (scope : Scope) (value : Bool) (count horizon : Nat) :
    readySupport source input cut protocol vocabulary encoding law receiver scope value count horizon ⊆
      BallotQuorum.support source (observed source input cut protocol (QueueScheduler.environment source input cut)
        vocabulary encoding law receiver horizon scope) scope value := by
  intro key inside
  obtain ⟨send, _, selected⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inside)
  unfold availableAt at selected
  split at selected <;> try contradiction
  rename_i wire ready
  split at selected <;> try contradiction
  rename_i aligned
  have sameKey := Option.some.inj selected
  obtain ⟨_, receipt, actual, sameBallot⟩ := ReceiptProgress.ready_plan_generates_a_valid_receipt
    source input cut protocol vocabulary encoding law send wire ready
  have received := (ReceiptProgress.receipts_are_preserved source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding law wire.recipient (ReceiptProgress.deadline source send) horizon aligned.2.2.2.1).subset actual
  rw [aligned.1] at received
  apply (BallotQuorum.mem_support_iff source _ scope value key).mpr
  refine ⟨receipt, List.mem_filter.mpr ⟨received, ?_⟩, sameBallot ▸ aligned.2.1, sameBallot ▸ aligned.2.2.1,
    (congrArg OwnedAttestation.BallotData.key sameBallot).trans sameKey⟩
  simpa only [sameBallot] using aligned.2.2.2.2

theorem source_windows_terminate_on_the_entire_subject
    (receiver : Fin source.code.sites) (count horizon sends threshold : Nat) (scope : Scope) (value : Bool)
    (subject : ApplicationSubject.Subject source)
    (resolved : ApplicationSubject.resolve source input cut protocol (QueueScheduler.environment source input cut) vocabulary scope = some subject)
    (bounded : count ≤ horizon) (positive : 0 < threshold)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary horizon < threshold + threshold)
    (enough : threshold ≤ (readySupport source input cut protocol vocabulary encoding law receiver scope value sends count).card) :
    produce source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law
      receiver count horizon scope threshold = .decided value subject := by
  have supported := le_trans enough (Finset.card_le_card (generated_support_is_received_and_content_bound
    source input cut protocol vocabulary encoding law receiver scope value sends count))
  have readout : ∃ choice, BallotQuorum.readout source (observed source input cut protocol (QueueScheduler.environment source input cut)
      vocabulary encoding law receiver count scope) scope threshold = .decided choice := by
    unfold BallotQuorum.readout
    rw [if_neg (by omega)]
    cases found : [false, true].find? (fun choice => decide (threshold ≤ (BallotQuorum.support source
        (observed source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law receiver count scope) scope choice).card)) with
    | some choice => exact ⟨choice, rfl⟩
    | none => exact False.elim ((List.find?_eq_none.mp found value (by cases value <;> simp)) (decide_eq_true supported))
  obtain ⟨choice, decided⟩ := readout
  have first := le_trans (BallotQuorum.decided_has_positive_quorum source _ scope threshold choice decided).2
    (Finset.card_le_card (ApplicationSubject.support_is_from_the_actual_receiver source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary encoding law receiver count scope choice))
  have second := le_trans supported (Finset.card_le_card (ApplicationSubject.support_is_from_the_actual_receiver source input cut protocol
    (QueueScheduler.environment source input cut) vocabulary encoding law receiver count scope value))
  have same := supported_values_agree source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law
    receiver receiver count count horizon bounded bounded scope threshold choice value first second budget
  subst choice
  unfold produce
  rw [if_neg (by omega), if_neg (by omega), resolved, decided]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SubjectQuorum

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlResponsibility
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumProgress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedPayment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AccountableDecision

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
  | outsideBudgetWindow | unsafeBudget | missingQuorum | missingPayment
  deriving DecidableEq

inductive ResultData (Receipt Payment : Type) where
  | blocked (reason : Obstruction)
  | declined
  | paid (receipt : Receipt) (payment : Payment)
  deriving DecidableEq

abbrev Result := ResultData (AttestationReception.Receipt source)
  (Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))

def decision {Receipt Payment : Type} : ResultData Receipt Payment → Quorum.ReadoutData Bool
  | .blocked _ => .blocked
  | .declined => .decided false
  | .paid _ _ => .decided true

abbrev observed (receiver : Fin source.code.sites) (count : Nat) :=
  AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count

/-- The budget is generated from this actual source through a common comparison
window. A true protocol decision additionally consumes a same-occurrence settlement. -/
def produce (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat) : Result source :=
  if ¬ count ≤ horizon then .blocked .outsideBudgetWindow
  else if ¬ source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold then
    .blocked .unsafeBudget
  else match BallotQuorum.readout source (observed source input cut protocol rival vocabulary encoding law receiver count) scope threshold with
    | .blocked => .blocked .missingQuorum
    | .decided false => .declined
    | .decided true =>
      match ReceivedPayment.confirm source input cut protocol rival vocabulary encoding law receiver count scope threshold with
      | .blocked => .blocked .missingPayment
      | .confirmed receipt payment => .paid receipt payment

theorem decision_retains_actual_quorum_and_source_budget
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : decision (produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold) = .decided value) :
    count ≤ horizon ∧
      source.code.sites + DeviationBudget.budget source input cut protocol rival vocabulary horizon < threshold + threshold ∧
      BallotQuorum.readout source (observed source input cut protocol rival vocabulary encoding law receiver count) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i bounded
  split at done <;> try contradiction
  rename_i budget
  split at done <;> try contradiction
  · cases done
    exact ⟨of_not_not bounded, of_not_not budget, by assumption⟩
  · split at done <;> try contradiction
    cases done
    exact ⟨of_not_not bounded, of_not_not budget, by assumption⟩

theorem agreement
    (left right : Fin source.code.sites) (leftCount rightCount horizon : Nat)
    (scope : Scope) (threshold : Nat) (a b : Bool)
    (one : decision (produce source input cut protocol rival vocabulary encoding law left leftCount horizon scope threshold) = .decided a)
    (two : decision (produce source input cut protocol rival vocabulary encoding law right rightCount horizon scope threshold) = .decided b) : a = b := by
  obtain ⟨leftBound, budget, first⟩ := decision_retains_actual_quorum_and_source_budget
    source input cut protocol rival vocabulary encoding law left leftCount horizon scope threshold a one
  obtain ⟨rightBound, _, second⟩ := decision_retains_actual_quorum_and_source_budget
    source input cut protocol rival vocabulary encoding law right rightCount horizon scope threshold b two
  exact BallotQuorum.agreement_of_actual_source_budget source input cut protocol rival vocabulary encoding law
    left right leftCount rightCount horizon leftBound rightBound scope threshold a b first second budget

theorem source_budget_is_monotone (count horizon : Nat) (bounded : count ≤ horizon) :
    DeviationBudget.budget source input cut protocol rival vocabulary count ≤
      DeviationBudget.budget source input cut protocol rival vocabulary horizon := by
  apply Finset.card_le_card
  intro key inside
  obtain ⟨n, earlier, cause⟩ := (DeviationBudget.affected_iff_source_change_or_actual_work_hazard
    source input cut protocol rival vocabulary count key).mp inside
  exact (DeviationBudget.affected_iff_source_change_or_actual_work_hazard
    source input cut protocol rival vocabulary horizon key).mpr ⟨n, by omega, cause⟩

theorem paid_retains_the_original_application_confirmation
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (paid : produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold = .paid receipt payment) :
    ReceivedPayment.confirm source input cut protocol rival vocabulary encoding law receiver count scope threshold = .confirmed receipt payment := by
  unfold produce at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  cases paid
  assumption

theorem every_decision_has_an_actual_authenticated_origin
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat) (value : Bool)
    (done : decision (produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold) = .decided value) :
    ∃ receipt ∈ (observed source input cut protocol rival vocabulary encoding law receiver count).receipts,
      receipt.wire.ballot.scope = scope ∧ receipt.wire.ballot.choice = value ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary receipt.wire.ballot = true ∧
      receipt.wire.ballot.cut < count := by
  exact BallotQuorum.decided_has_source_authenticated_support source input cut protocol rival vocabulary encoding law
    receiver count scope threshold value
      (decision_retains_actual_quorum_and_source_budget source input cut protocol rival vocabulary encoding law
        receiver count horizon scope threshold value done).2.2

theorem blocked_is_not_a_decision {Receipt Payment : Type} (reason : Obstruction) (value : Bool) :
    decision (ResultData.blocked (Receipt := Receipt) (Payment := Payment) reason) ≠ .decided value := by
  simp [decision]

theorem paid_has_actual_financial_effects_and_literal_next
    (receiver : Fin source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (paid : produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold = .paid receipt payment) :
    let actual := OwnedAttestation.actual source input cut protocol rival
    let depth := source.history.length + 1 + (cut + receipt.wire.ballot.cut)
    ∃ item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument,
      item ∈ (Financial.inventoryAt actual.input (ProgrammeHistory.visitAt actual.input (depth + 1))).filterMap
        (Financial.InstructionOrigin.instruction? actual.input) ∧
      source.code.law.Valid item.before item.request ∧
      item.request.signer = receipt.wire.ballot.actor ∧ receipt.wire.ballot.actor = payment.debtor ∧
      0 < payment.amount ∧
      flowAt (source.code.law.actualDebit item.before item.request) payment.debtor payment.unit = payment.amount ∧
      flowAt (source.code.law.actualCredit item.before item.request) payment.creditor payment.unit = payment.amount ∧
      (source.code.law.step item.before item.request).claims payment.instrument payment.debtor payment.creditor =
        payment.priorClaim - payment.quantity ∧
      actual.currentAt (depth + 2) = source.code.law.next (actual.currentAt (depth + 1))
        (OwnedAttestation.execution source input cut protocol rival receipt.wire.ballot.cut).submitted := by
  have confirmed := paid_retains_the_original_application_confirmation source input cut protocol rival vocabulary encoding law
    receiver count horizon scope threshold receipt payment paid
  have origin := (ReceivedPayment.confirmation_requires_actual_receipt_quorum_and_the_same_payment
    source input cut protocol rival vocabulary encoding law receiver count scope threshold receipt payment confirmed).2.2.2.1
  exact AttestationConsumer.confirmed_payment_enters_the_original_finance_inventory_and_next
    source input cut protocol rival vocabulary receipt.wire.ballot.cut receipt.wire.ballot.position receipt.wire.ballot payment origin

/-- Receipt existence alone is insufficient: this consumer also requires the
original source's settlement classification at that receipt's exact occurrence. -/
theorem receipt_and_source_payment_generate_confirmation
    (receiver : Fin source.code.sites) (count : Nat) (scope : Scope) (threshold : Nat)
    (positive : 0 < threshold)
    (enough : threshold ≤ (ReceivedPayment.support source
      (observed source input cut protocol rival vocabulary encoding law receiver count) scope).card)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (inside : receipt ∈ (observed source input cut protocol rival vocabulary encoding law receiver count).receipts)
    (origin : AttestationConsumer.confirm source input cut protocol rival vocabulary receipt.wire.ballot.cut receipt.wire.ballot.position =
      .confirmed receipt.wire.ballot payment)
    (ballotScope : receipt.wire.ballot.scope = scope) (paymentScope : payment.scope = scope) :
    ∃ actualReceipt actualPayment, ReceivedPayment.confirm source input cut protocol rival vocabulary encoding law
      receiver count scope threshold = .confirmed actualReceipt actualPayment := by
  have member : (receipt, payment) ∈
      (observed source input cut protocol rival vocabulary encoding law receiver count).receipts.filterMap
        (ReceivedPayment.paymentAt source input cut protocol rival vocabulary scope) := by
    apply List.mem_filterMap.mpr
    exact ⟨receipt, inside, by simp only [ReceivedPayment.paymentAt, origin]; simp [ballotScope, paymentScope]⟩
  change threshold ≤ (ReceivedPayment.support source
    (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count) scope).card at enough
  unfold ReceivedPayment.confirm
  rw [if_neg (by omega), if_neg (by omega)]
  cases first : ((observed source input cut protocol rival vocabulary encoding law receiver count).receipts.filterMap
      (ReceivedPayment.paymentAt source input cut protocol rival vocabulary scope))[0]? with
  | some pair => exact ⟨pair.1, pair.2, rfl⟩
  | none =>
    have empty := List.getElem?_eq_none_iff.mp first
    have nonempty := List.length_pos_of_mem member
    omega

theorem a_paid_decision_remains_paid_within_its_source_budget_window
    (receiver : Fin source.code.sites) (count later horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (paid : produce source input cut protocol rival vocabulary encoding law receiver count horizon scope threshold = .paid receipt payment)
    (forward : count ≤ later) (bounded : later ≤ horizon) :
    ∃ laterReceipt laterPayment, produce source input cut protocol rival vocabulary encoding law
      receiver later horizon scope threshold = .paid laterReceipt laterPayment := by
  have original := decision_retains_actual_quorum_and_source_budget source input cut protocol rival vocabulary encoding law
    receiver count horizon scope threshold true (by rw [paid]; rfl)
  have confirmed := paid_retains_the_original_application_confirmation source input cut protocol rival vocabulary encoding law
    receiver count horizon scope threshold receipt payment paid
  obtain ⟨inside, positive, enough, origin, ballotScope, paymentScope⟩ :=
    ReceivedPayment.confirmation_requires_actual_receipt_quorum_and_the_same_payment source input cut protocol rival
      vocabulary encoding law receiver count scope threshold receipt payment confirmed
  have retained := ReceiptProgress.receipts_are_preserved source input cut protocol rival vocabulary encoding law
    receiver count later forward
  have subset : BallotQuorum.support source (observed source input cut protocol rival vocabulary encoding law receiver count) scope true ⊆
      BallotQuorum.support source (observed source input cut protocol rival vocabulary encoding law receiver later) scope true := by
    intro key present
    obtain ⟨body, member, aligned, choice, same⟩ := (BallotQuorum.mem_support_iff source _ scope true key).mp present
    exact (BallotQuorum.mem_support_iff source _ scope true key).mpr
      ⟨body, retained.subset member, aligned, choice, same⟩
  have enoughLater : threshold ≤ (BallotQuorum.support source
      (observed source input cut protocol rival vocabulary encoding law receiver later) scope true).card :=
    le_trans enough (Finset.card_le_card subset)
  have laterReadout : BallotQuorum.readout source
      (observed source input cut protocol rival vocabulary encoding law receiver later) scope threshold = .decided true := by
    by_cases conflict : threshold ≤ (BallotQuorum.support source
        (observed source input cut protocol rival vocabulary encoding law receiver later) scope false).card
    · have falseReadout : BallotQuorum.readout source
          (observed source input cut protocol rival vocabulary encoding law receiver later) scope threshold = .decided false := by
        simp [BallotQuorum.readout, Nat.ne_of_gt positive, conflict]
      have incompatible := BallotQuorum.agreement_of_actual_source_budget source input cut protocol rival vocabulary encoding law
        receiver receiver count later horizon original.1 bounded scope threshold true false original.2.2 falseReadout original.2.1
      contradiction
    · simp [BallotQuorum.readout, Nat.ne_of_gt positive, conflict, enoughLater]
  obtain ⟨laterReceipt, laterPayment, laterConfirmed⟩ := receipt_and_source_payment_generate_confirmation
    source input cut protocol rival vocabulary encoding law receiver later scope threshold positive enoughLater receipt payment
      (retained.subset inside) origin ballotScope paymentScope
  refine ⟨laterReceipt, laterPayment, ?_⟩
  unfold produce
  rw [if_neg (by omega), if_neg (by have budget := original.2.1; omega), laterReadout, laterConfirmed]

omit rival

/-- This plan reads a checked send window and the original owned settlement.
It accepts neither a receiver certificate nor an application decision. -/
def applicationAt (scope : Scope) (send : Nat) : Option (AttestationTransport.Wire source ×
    Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument)) :=
  match ReceiptProgress.plan source input cut protocol vocabulary encoding law send with
  | .blocked _ => none
  | .ready wire =>
    match AttestationConsumer.confirm source input cut protocol (QueueScheduler.environment source input cut) vocabulary
        wire.ballot.cut wire.ballot.position with
    | .blocked _ => none
    | .confirmed ballot payment =>
      if ballot = wire.ballot ∧ ballot.scope = scope ∧ payment.scope = scope then some (wire, payment) else none

theorem source_windows_terminate_decline
    (receiver : Fin source.code.sites) (count horizon sends threshold : Nat) (scope : Scope)
    (bounded : count ≤ horizon) (positive : 0 < threshold)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary horizon < threshold + threshold)
    (enough : threshold ≤ (QuorumProgress.readySupport source input cut protocol vocabulary encoding law receiver scope false sends count).card) :
    produce source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding law
      receiver count horizon scope threshold = .declined := by
  have smaller := source_budget_is_monotone source input cut protocol
    (QueueScheduler.environment source input cut) vocabulary count horizon bounded
  have decided := QuorumProgress.generated_windows_and_source_budget_decide_the_supported_value
    source input cut protocol vocabulary encoding law receiver scope false sends count threshold positive enough (by omega)
  unfold produce
  rw [if_neg (by omega), if_neg (by omega), decided]

theorem source_windows_and_original_payment_terminate
    (receiver : Fin source.code.sites) (count horizon sends threshold : Nat) (scope : Scope)
    (bounded : count ≤ horizon) (positive : 0 < threshold)
    (budget : source.code.sites + DeviationBudget.budget source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary horizon < threshold + threshold)
    (enough : threshold ≤ (QuorumProgress.readySupport source input cut protocol vocabulary encoding law receiver scope true sends count).card)
    (send : Nat) (wire : AttestationTransport.Wire source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (ready : applicationAt source input cut protocol vocabulary encoding law scope send = some (wire, payment))
    (recipient : wire.recipient = receiver) (deadline : ReceiptProgress.deadline source send ≤ count) :
    ∃ actualReceipt actualPayment, produce source input cut protocol (QueueScheduler.environment source input cut)
      vocabulary encoding law receiver count horizon scope threshold = .paid actualReceipt actualPayment := by
  unfold applicationAt at ready
  split at ready <;> try contradiction
  rename_i candidate window
  split at ready <;> try contradiction
  rename_i ballot statement origin
  split at ready <;> try contradiction
  rename_i aligned
  have pair := Option.some.inj ready
  cases pair
  obtain ⟨_, receipt, inside, same⟩ := ReceiptProgress.ready_plan_generates_a_valid_receipt
    source input cut protocol vocabulary encoding law send wire window
  have received := (ReceiptProgress.receipts_are_preserved source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding law wire.recipient (ReceiptProgress.deadline source send) count deadline).subset inside
  rw [recipient] at received
  have support := le_trans enough (Finset.card_le_card (QuorumProgress.generated_support_is_in_the_actual_receiver
    source input cut protocol vocabulary encoding law receiver scope true sends count))
  have confirmation := receipt_and_source_payment_generate_confirmation source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding law receiver count scope threshold positive support receipt payment received
    (by rw [same]; exact aligned.1 ▸ origin) (same ▸ aligned.1 ▸ aligned.2.1) aligned.2.2
  obtain ⟨actualReceipt, actualPayment, confirmed⟩ := confirmation
  have decided := QuorumProgress.generated_windows_and_source_budget_decide_the_supported_value
    source input cut protocol vocabulary encoding law receiver scope true sends count threshold positive enough
    (by
      have card := source_budget_is_monotone source input cut protocol
        (QueueScheduler.environment source input cut) vocabulary count horizon bounded
      omega)
  refine ⟨actualReceipt, actualPayment, ?_⟩
  unfold produce
  rw [if_neg (by omega), if_neg (by omega), decided, confirmed]

section NativeConsumer

variable (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (actualInput : Input bound.source.code) (actualCut : Nat)
  (actualProtocol : Distributed.Recall.Information.Agency.Protocol.Rule bound.source.code)
  (actualRival : Opponent bound.source.code)
  (actualEncoding : AttestationTransport.Encoding bound.source)
  (actualLaw : AttestationReception.ReceptionLaw bound.source)
  (empty : bound.source.continuation = [])

/-- A successful application decision is consumed at its original payment cut,
using the unchanged facade's native responsibility, whole ledger and next. -/
theorem paid_original_root_consumer
    (receiver : Fin bound.source.code.sites) (count horizon : Nat) (scope : Scope) (threshold : Nat)
    (receipt : AttestationReception.Receipt bound.source)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (paid : produce bound.source actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw
      receiver count horizon scope threshold = .paid receipt payment) :
    let n := receipt.wire.ballot.cut
    let consumed := ControlResponsibility.produce bound actualInput actualCut actualProtocol actualRival
      vocabulary actualEncoding actualLaw empty n
    let runtime := ControlResponsibility.runtime bound actualInput actualCut actualProtocol actualRival
      vocabulary actualEncoding actualLaw empty n
    n < count ∧
      (∃ item, (item, true) ∈ consumed.requests ∧
        flowAt (bound.source.code.law.actualDebit item.before item.request) payment.debtor payment.unit = payment.amount ∧
        flowAt (bound.source.code.law.actualCredit item.before item.request) payment.creditor payment.unit = payment.amount ∧
        (bound.source.code.law.step item.before item.request).claims payment.instrument payment.debtor payment.creditor =
          payment.priorClaim - payment.quantity) ∧
      consumed.responsibility.current = Native.Authority.fullGenerate
        (ControlResponsibility.actualBound bound actualInput actualCut actualProtocol actualRival)
        (ControlResponsibility.depth bound actualCut n) ∧
      consumed.responsibility.feedback.native = Native.generate
        (ControlResponsibility.actualBound bound actualInput actualCut actualProtocol actualRival).source
        (ControlResponsibility.depth bound actualCut n) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (CommunicationRuntime.facade bound actualInput actualCut actualProtocol actualRival
        vocabulary actualEncoding actualLaw empty).process.stateAt
          ((CommunicationRuntime.facade bound actualInput actualCut actualProtocol actualRival
            vocabulary actualEncoding actualLaw empty).process.successor runtime.state) := by
  have confirmed := paid_retains_the_original_application_confirmation bound.source actualInput actualCut actualProtocol actualRival
    vocabulary actualEncoding actualLaw receiver count horizon scope threshold receipt payment paid
  have inside := (ReceivedPayment.confirmation_requires_actual_receipt_quorum_and_the_same_payment
    bound.source actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw
    receiver count scope threshold receipt payment confirmed).1
  have earlier := (BallotQuorum.receipt_ballot_has_actual_origin bound.source actualInput actualCut actualProtocol actualRival
    vocabulary actualEncoding actualLaw receiver count receipt inside).2
  obtain ⟨item, inventory, valid, _, _, _, debit, credit, claims, _⟩ :=
    paid_has_actual_financial_effects_and_literal_next bound.source actualInput actualCut actualProtocol actualRival
      vocabulary actualEncoding actualLaw receiver count horizon scope threshold receipt payment paid
  have rooted := ControlResponsibility.original_native_histories_and_root_next_are_consumed_together
    bound actualInput actualCut actualProtocol actualRival vocabulary actualEncoding actualLaw empty receipt.wire.ballot.cut
  refine ⟨earlier, ⟨item, ?_, debit, credit, claims⟩, rooted.1, rooted.2.1, rooted.2.2.2.1, rooted.2.2.2.2⟩
  change (item, true) ∈ (ControlResponsibility.items bound actualInput actualCut actualProtocol actualRival receipt.wire.ballot.cut).map _
  exact List.mem_map.mpr ⟨item, inventory, by simp [valid]⟩

end NativeConsumer

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AccountableDecision

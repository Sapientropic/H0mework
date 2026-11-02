import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptOrigin
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedPayment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptProgress

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open AttestationTransport

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : Encoding source) (law : AttestationReception.ReceptionLaw source)

abbrev observed (receiver : Fin source.code.sites) (count : Nat) :=
  AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count

theorem receipts_are_preserved (receiver : Fin source.code.sites) (n m : Nat) (later : n ≤ m) :
    (observed source input cut protocol rival vocabulary encoding law receiver n).receipts <+:
      (observed source input cut protocol rival vocabulary encoding law receiver m).receipts := by
  induction m, later using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
    apply ih.trans
    change _ <+: (AttestationReception.receive source input cut protocol rival vocabulary encoding law receiver m
      (observed source input cut protocol rival vocabulary encoding law receiver m)).receipts
    unfold AttestationReception.receive
    dsimp only
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem one_authenticated_origin_has_one_ballot (one two : OwnedAttestation.Ballot source)
    (first : OwnedAttestation.verify source input cut protocol rival vocabulary one = true)
    (second : OwnedAttestation.verify source input cut protocol rival vocabulary two = true)
    (same : (one.cut, one.position) = (two.cut, two.position)) : one = two := by
  have generated := of_decide_eq_true first
  have other := of_decide_eq_true second
  obtain ⟨cuts, positions⟩ := Prod.mk.inj same
  rw [cuts, positions, other] at generated
  exact (Option.some.inj generated).symm

/-- A valid repeated wire preserves the existing content receipt. Otherwise
the original receiver appends the receipt at this actual delivery cut. -/
theorem actual_valid_delivery_generates_a_content_receipt
    (send delivered : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding send = some wire)
    (earlier : send < delivered)
    (attempt : AttestationReception.deliveredAt source input cut protocol rival delivered wire.serial = true)
    (scope : wire.ballot.scope = law.scope wire.recipient (execution source input cut protocol rival delivered).before)
    (timely : delivered ≤ wire.sendCut + law.maxDelay)
    (paid : ∀ item ∈ source.code.law.rawItems (execution source input cut protocol rival delivered).before
      (source.code.deliveryCost wire.recipient), source.code.law.Valid item.before item.request) :
    ∃ receipt ∈ (observed source input cut protocol rival vocabulary encoding law wire.recipient (delivered + 1)).receipts,
      receipt.wire.ballot = wire.ballot := by
  have identity := ReceiptOrigin.issued_identity source input cut protocol rival vocabulary encoding send wire generated
  have authenticated : AttestationTransport.verify source input cut protocol rival vocabulary encoding wire = true := by
    unfold AttestationTransport.verify
    apply decide_eq_true
    rw [identity.1]
    exact generated
  have owned := (authenticated_wire_has_an_earlier_owned_paid_statement source input cut protocol rival vocabulary encoding wire authenticated).2.2.1
  have incoming := ReceiptOrigin.actual_delivery_reconstructs_the_original_wire source input cut protocol rival
    vocabulary encoding send delivered wire generated earlier attempt
  have matching := ReceiptOrigin.issued_packet_matches_at_every_later_cut source input cut protocol rival
    vocabulary encoding send delivered wire generated earlier
  by_cases duplicate : (wire.ballot.cut, wire.ballot.position) ∈
      (observed source input cut protocol rival vocabulary encoding law wire.recipient delivered).receipts.map
        (fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position))
  · obtain ⟨old, inside, same⟩ := List.mem_map.mp duplicate
    have oldAuth := (AttestationReception.receipts_have_actual_communication source input cut protocol rival
      vocabulary encoding law wire.recipient delivered old inside).1
    have oldOwned := (authenticated_wire_has_an_earlier_owned_paid_statement source input cut protocol rival
      vocabulary encoding old.wire oldAuth).2.2.1
    exact ⟨old, (receipts_are_preserved source input cut protocol rival vocabulary encoding law wire.recipient
      delivered (delivered + 1) (by omega)).subset inside,
      one_authenticated_origin_has_one_ballot source input cut protocol rival vocabulary old.wire.ballot wire.ballot oldOwned owned same⟩
  · have accepts : AttestationReception.check source input cut protocol rival vocabulary encoding law wire.recipient delivered
        ((observed source input cut protocol rival vocabulary encoding law wire.recipient delivered).receipts.map
          fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) wire = .accepted wire := by
      unfold AttestationReception.check
      split_ifs <;> first | rfl | contradiction | omega
    refine ⟨⟨wire, delivered⟩, ?_, rfl⟩
    simp only [observed, AttestationReception.run, AttestationReception.receive, incoming, accepts]
    exact List.mem_append_right _ (List.mem_singleton_self _)

def deadline (send : Nat) : Nat :=
  2 * ((send + 2) / 2 + (QueueScheduler.admitted source.code).card)

theorem a_source_window_generates_a_valid_content_receipt
    (send : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary encoding send = some wire)
    (supported : wire.serial ∈ QueueScheduler.admitted source.code)
    (enough : deadline source send ≤ (source.feedbackState input cut).remaining)
    (timing : deadline source send ≤ send + law.maxDelay + 1)
    (scope : ∀ n ∈ Finset.range (deadline source send), send < n →
      wire.ballot.scope = law.scope wire.recipient
        (execution source input cut protocol (QueueScheduler.environment source input cut) n).before)
    (paid : ∀ n ∈ Finset.range (deadline source send), send < n →
      ∀ item ∈ source.code.law.rawItems
        (execution source input cut protocol (QueueScheduler.environment source input cut) n).before
        (source.code.deliveryCost wire.recipient), source.code.law.Valid item.before item.request) :
    ∃ receipt ∈ (observed source input cut protocol (QueueScheduler.environment source input cut)
      vocabulary encoding law wire.recipient (deadline source send)).receipts,
      receipt.wire.ballot = wire.ballot := by
  have starts : send + 1 ≤ deadline source send := by unfold deadline; omega
  have born := ReceiptOrigin.issued_address_is_new_and_present source input cut protocol
    (QueueScheduler.environment source input cut) vocabulary encoding send wire generated
  have fresh := ReceiptOrigin.a_new_wire_has_no_old_scheduled_attempt source input cut protocol
    vocabulary encoding send wire generated (by omega)
  obtain ⟨n, afterSend, beforeEnd, delivered⟩ := QueueScheduler.a_pending_packet_is_attempted_during_its_source_window
    source input cut protocol (send + 1) wire.serial enough born.2 supported fresh
  change n < deadline source send at beforeEnd
  have identity := ReceiptOrigin.issued_identity source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding send wire generated
  obtain ⟨receipt, actual, same⟩ := actual_valid_delivery_generates_a_content_receipt source input cut protocol
    (QueueScheduler.environment source input cut) vocabulary encoding law send n wire generated (by omega) delivered
    (scope n (Finset.mem_range.mpr beforeEnd) (by omega))
    (by rw [identity.1]; omega)
    (paid n (Finset.mem_range.mpr beforeEnd) (by omega))
  exact ⟨receipt, (receipts_are_preserved source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding law wire.recipient (n + 1) (deadline source send) (by omega)).subset actual, same⟩

inductive Obstruction where
  | missingSend | unadmittedAddress | insufficientCuts | missingTiming | scopeWindow | paymentWindow | missingReceipt
  deriving DecidableEq

inductive PlanData (Body : Type) where
  | blocked (reason : Obstruction)
  | ready (wire : Body)
  deriving DecidableEq

abbrev Plan := PlanData (Wire source)

/-- All adequacy conditions are computed from this run's actual send, future
source states, delivery interface and original request validity. -/
def plan (send : Nat) : Plan source :=
  match AttestationTransport.issuedAt source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding send with
  | none => .blocked .missingSend
  | some wire =>
    if wire.serial ∉ QueueScheduler.admitted source.code then .blocked .unadmittedAddress
    else if ¬ deadline source send ≤ (source.feedbackState input cut).remaining then .blocked .insufficientCuts
    else if ¬ deadline source send ≤ send + law.maxDelay + 1 then .blocked .missingTiming
    else if ¬ ∀ n ∈ Finset.range (deadline source send), send < n →
        wire.ballot.scope = law.scope wire.recipient
          (execution source input cut protocol (QueueScheduler.environment source input cut) n).before then .blocked .scopeWindow
    else if ¬ ∀ n ∈ Finset.range (deadline source send), send < n →
        ∀ item ∈ source.code.law.rawItems
          (execution source input cut protocol (QueueScheduler.environment source input cut) n).before
          (source.code.deliveryCost wire.recipient), source.code.law.Valid item.before item.request then .blocked .paymentWindow
    else .ready wire

theorem ready_plan_generates_a_valid_receipt (send : Nat) (wire : Wire source)
    (ready : plan source input cut protocol vocabulary encoding law send = .ready wire) :
    AttestationTransport.issuedAt source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding send = some wire ∧
      ∃ receipt ∈ (observed source input cut protocol (QueueScheduler.environment source input cut)
        vocabulary encoding law wire.recipient (deadline source send)).receipts,
        receipt.wire.ballot = wire.ballot := by
  unfold plan at ready
  split at ready <;> try contradiction
  rename_i candidate issued
  split_ifs at ready
  rename_i admitted enough timing scope paid
  cases ready
  refine ⟨issued, a_source_window_generates_a_valid_content_receipt source input cut protocol vocabulary encoding law send wire issued
    (by simpa only [not_not] using admitted) (by simpa only [not_not] using enough)
    (by simpa only [not_not] using timing) (by simpa only [not_not] using scope) (by simpa only [not_not] using paid)⟩

inductive CompletionData (Body : Type) where
  | blocked (reason : Obstruction)
  | received (receipt : Body)
  deriving DecidableEq

abbrev Completion := CompletionData (AttestationReception.Receipt source)

/-- Actual receipts take priority over a sufficient worst-case window test.
A short timing contract may already have succeeded at its real delivery cut. -/
def produce (send : Nat) : Completion source :=
  match AttestationTransport.issuedAt source input cut protocol (QueueScheduler.environment source input cut) vocabulary encoding send with
  | none => .blocked .missingSend
  | some wire =>
    match (observed source input cut protocol (QueueScheduler.environment source input cut)
        vocabulary encoding law wire.recipient (deadline source send)).receipts.find?
        (fun receipt => decide (receipt.wire.ballot = wire.ballot)) with
    | some receipt => .received receipt
    | none => match plan source input cut protocol vocabulary encoding law send with
      | .blocked reason => .blocked reason
      | .ready _ => .blocked .missingReceipt

theorem ready_plan_completes (send : Nat) (wire : Wire source)
    (ready : plan source input cut protocol vocabulary encoding law send = .ready wire) :
    ∃ receipt, produce source input cut protocol vocabulary encoding law send = .received receipt := by
  obtain ⟨issued, receipt, inside, same⟩ := ready_plan_generates_a_valid_receipt source input cut protocol vocabulary encoding law send wire ready
  unfold produce
  rw [issued]
  dsimp only
  cases found : (observed source input cut protocol (QueueScheduler.environment source input cut)
      vocabulary encoding law wire.recipient (deadline source send)).receipts.find?
      (fun receipt => decide (receipt.wire.ballot = wire.ballot)) with
  | some actual => exact ⟨actual, rfl⟩
  | none => exact False.elim ((List.find?_eq_none.mp found receipt inside) (decide_eq_true same))

theorem produced_receipt_has_the_actual_send_and_history (send : Nat) (receipt : AttestationReception.Receipt source)
    (done : produce source input cut protocol vocabulary encoding law send = .received receipt) :
    ∃ wire, AttestationTransport.issuedAt source input cut protocol (QueueScheduler.environment source input cut)
      vocabulary encoding send = some wire ∧
      receipt ∈ (observed source input cut protocol (QueueScheduler.environment source input cut)
        vocabulary encoding law wire.recipient (deadline source send)).receipts ∧ receipt.wire.ballot = wire.ballot := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i wire issued
  split at done
  · rename_i actual found
    cases done
    exact ⟨wire, issued, List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun (receipt : AttestationReception.Receipt source) =>
        decide (receipt.wire.ballot = wire.ballot)) found)⟩
  · split at done <;> contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptProgress

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationTransport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception

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
  (encoding : Encoding source)

structure ReceptionLaw where
  scope : Fin source.code.sites → RawCurrent Party Good (Mandate.State Party Technology) Instrument → Scope
  maxDelay : Nat

inductive Rejection where
  | missingWire | missingDelivery | unauthenticated | missingPacket | wrongRecipient
  | staleScope | late | unpaidDelivery | duplicate
  deriving DecidableEq

inductive VerdictData (Body : Type) where
  | rejected (reason : Rejection)
  | accepted (wire : Body)
  deriving DecidableEq

abbrev Verdict := VerdictData (Wire source)
abbrev Receipt := ReceiptData (Wire source)

structure ReceiverData (Body : Type) where
  receipts : List (ReceiptData Body)
  audit : List (Nat × Option Body × VerdictData Body)
  deriving DecidableEq

abbrev Receiver := ReceiverData (Wire source)

def deliveredAt (n serial : Nat) : Bool :=
  if n < (source.feedbackState input cut).remaining then
    match move source input cut protocol rival n with
    | some event => match event.val with
      | .deliver address => address == serial
      | _ => false
    | none => false
  else false

def matchingPacket (n : Nat) (wire : Wire source) : Bool :=
  match (state source input cut protocol rival n).frame.sent[wire.serial]? with
  | none => false
  | some packet => decide (packet.sender = wire.ballot.key ∧ packet.recipient = wire.recipient ∧
      packet.signal = wire.signal ∧ packet.sentAfter = wire.sentAfter)

theorem matched_packet_is_actual (n : Nat) (wire : Wire source)
    (matched : matchingPacket source input cut protocol rival n wire = true) :
    ∃ packet, (state source input cut protocol rival n).frame.sent[wire.serial]? = some packet ∧
      packet.sender = wire.ballot.key ∧ packet.recipient = wire.recipient ∧
      packet.signal = wire.signal ∧ packet.sentAfter = wire.sentAfter := by
  unfold matchingPacket at matched
  split at matched <;> try contradiction
  rename_i packet actual
  exact ⟨packet, actual, of_decide_eq_true matched⟩

theorem actual_delivery_submits_the_original_cost (empty : source.continuation = [])
    (n serial : Nat) (packet : source.code.Packet)
    (delivered : deliveredAt source input cut protocol rival n serial = true)
    (present : (state source input cut protocol rival n).frame.sent[serial]? = some packet) :
    (execution source input cut protocol rival n).submitted = source.code.deliveryCost packet.recipient := by
  unfold deliveredAt at delivered
  split at delivered <;> try contradiction
  rename_i bounded
  unfold move at delivered
  split at delivered <;> try contradiction
  rename_i event chosen
  split at delivered <;> try contradiction
  rename_i address kind
  have same : address = serial := of_decide_eq_true delivered
  subst address
  rw [(OwnedAttestation.actual source input cut protocol rival).feedback_word_is_actual
    (actualInput source input cut protocol rival) rfl empty, Execution.policy_at]
  change word source.code (Residual.scheduleAt source cut
    (Distributed.Recall.Information.Agency.Protocol.term source input cut protocol).val n) _ _ = _
  rw [Distributed.Recall.Information.Agency.Protocol.active_control_is_the_selected_work_policy
    source input cut protocol n bounded]
  change word source.code (some protocol.work.val) (actualInput source input cut protocol rival)
    (state source input cut protocol rival n) = _
  simp only [word, chosen, stepLocal, kind, Code.step, present, List.nil_append]

variable (law : ReceptionLaw source)

def check (receiver : Fin source.code.sites) (n : Nat) (seen : List (Nat × Nat)) (wire : Wire source) : Verdict source :=
  if deliveredAt source input cut protocol rival n wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.sendCut < n then .rejected .unauthenticated
  else if AttestationTransport.verify source input cut protocol rival vocabulary encoding wire ≠ true then .rejected .unauthenticated
  else if matchingPacket source input cut protocol rival n wire ≠ true then .rejected .missingPacket
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.ballot.scope ≠ law.scope receiver (execution source input cut protocol rival n).before then .rejected .staleScope
  else if ¬ n ≤ wire.sendCut + law.maxDelay then .rejected .late
  else if ¬ ∀ item ∈ source.code.law.rawItems (execution source input cut protocol rival n).before
      (source.code.deliveryCost receiver), source.code.law.Valid item.before item.request then .rejected .unpaidDelivery
  else if (wire.ballot.cut, wire.ballot.position) ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_sound (receiver : Fin source.code.sites) (n : Nat) (seen : List (Nat × Nat))
    (wire result : Wire source)
    (accepted : check source input cut protocol rival vocabulary encoding law receiver n seen wire = .accepted result) :
    result = wire ∧ deliveredAt source input cut protocol rival n wire.serial = true ∧ wire.sendCut < n ∧
      AttestationTransport.verify source input cut protocol rival vocabulary encoding wire = true ∧
      matchingPacket source input cut protocol rival n wire = true ∧ wire.recipient = receiver ∧
      wire.ballot.scope = law.scope receiver (execution source input cut protocol rival n).before ∧
      n ≤ wire.sendCut + law.maxDelay ∧
      (∀ item ∈ source.code.law.rawItems (execution source input cut protocol rival n).before
        (source.code.deliveryCost receiver), source.code.law.Valid item.before item.request) ∧
      (wire.ballot.cut, wire.ballot.position) ∉ seen := by
  unfold check at accepted
  split_ifs at accepted; simp_all

/-- Incoming data are reconstructed from the actual delivery address and the
earlier owned sends of this very feedback run. -/
def incoming (n : Nat) : Option (Wire source) :=
  match move source input cut protocol rival n with
  | none => none
  | some event => match event.val with
    | .deliver serial =>
        ((List.range n).filterMap (AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding)).find?
          (fun wire => wire.serial == serial)
    | _ => none

def receive (receiver : Fin source.code.sites) (n : Nat) (previous : Receiver source) : Receiver source :=
  let wire := incoming source input cut protocol rival vocabulary encoding n
  let verdict := match wire with
    | none => VerdictData.rejected .missingWire
    | some wire => check source input cut protocol rival vocabulary encoding law receiver n
        (previous.receipts.map fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) wire
  ⟨match verdict with
    | .accepted wire => previous.receipts ++ [⟨wire, n⟩]
    | .rejected _ => previous.receipts,
    previous.audit ++ [(n, wire, verdict)]⟩

def run (receiver : Fin source.code.sites) : Nat → Receiver source
  | 0 => ⟨[], []⟩
  | n + 1 => receive source input cut protocol rival vocabulary encoding law receiver n (run receiver n)

theorem receipts_have_actual_communication (receiver : Fin source.code.sites) (count : Nat)
    (receipt : Receipt source)
    (inside : receipt ∈ (run source input cut protocol rival vocabulary encoding law receiver count).receipts) :
    AttestationTransport.verify source input cut protocol rival vocabulary encoding receipt.wire = true ∧
      deliveredAt source input cut protocol rival receipt.delivery receipt.wire.serial = true ∧
      matchingPacket source input cut protocol rival receipt.delivery receipt.wire = true ∧
      receipt.wire.recipient = receiver ∧ receipt.wire.sendCut < receipt.delivery ∧
      receipt.delivery < count ∧
      receipt.wire.ballot.scope = law.scope receiver (execution source input cut protocol rival receipt.delivery).before ∧
      receipt.delivery ≤ receipt.wire.sendCut + law.maxDelay ∧
      (∀ item ∈ source.code.law.rawItems (execution source input cut protocol rival receipt.delivery).before
        (source.code.deliveryCost receiver), source.code.law.Valid item.before item.request) := by
  induction count with
  | zero => simp [run] at inside
  | succ n ih =>
    simp only [run, receive] at inside
    split at inside
    · rename_i wire outcome
      rcases List.mem_append.mp inside with old | fresh
      · obtain ⟨auth, delivered, packet, who, earlier, bounded, scope, time, paid⟩ := ih old
        exact ⟨auth, delivered, packet, who, earlier, by omega, scope, time, paid⟩
      · have same := List.mem_singleton.mp fresh
        subst receipt
        cases candidate : incoming source input cut protocol rival vocabulary encoding n with
        | none => simp [candidate] at outcome
        | some body =>
          simp only [candidate] at outcome
          obtain ⟨rfl, delivered, earlier, auth, packet, who, scope, time, paid, _⟩ :=
            check_sound source input cut protocol rival vocabulary encoding law receiver n _ body wire outcome
          exact ⟨auth, delivered, packet, who, earlier, Nat.lt_succ_self _, scope, time, paid⟩
    · obtain ⟨auth, delivered, packet, who, earlier, bounded, scope, time, paid⟩ := ih inside
      exact ⟨auth, delivered, packet, who, earlier, by omega, scope, time, paid⟩

theorem receipt_has_actual_packet_content_and_paid_delivery
    (receiver : Fin source.code.sites) (count : Nat) (receipt : Receipt source)
    (inside : receipt ∈ (run source input cut protocol rival vocabulary encoding law receiver count).receipts) :
    ∃ packet, (state source input cut protocol rival receipt.delivery).frame.sent[receipt.wire.serial]? = some packet ∧
      encoding packet.signal = some receipt.wire.ballot ∧
      (execution source input cut protocol rival receipt.delivery).submitted = source.code.deliveryCost receiver ∧
      (∀ item ∈ source.code.law.rawItems (execution source input cut protocol rival receipt.delivery).before
        (execution source input cut protocol rival receipt.delivery).submitted, source.code.law.Valid item.before item.request) := by
  obtain ⟨authenticated, delivered, matching, who, _, _, _, _, paid⟩ :=
    receipts_have_actual_communication source input cut protocol rival vocabulary encoding law receiver count receipt inside
  obtain ⟨empty, _, _, _, encoded, _⟩ := authenticated_wire_has_an_earlier_owned_paid_statement
    source input cut protocol rival vocabulary encoding receipt.wire authenticated
  obtain ⟨packet, present, _, recipient, signal, _⟩ :=
    matched_packet_is_actual source input cut protocol rival receipt.delivery receipt.wire matching
  have submitted := actual_delivery_submits_the_original_cost source input cut protocol rival empty
    receipt.delivery receipt.wire.serial packet delivered present
  rw [recipient, who] at submitted
  refine ⟨packet, present, ?_, submitted, ?_⟩
  · simpa only [signal] using encoded
  · simpa only [submitted] using paid

theorem repeated_sends_cannot_duplicate_a_ballot_receipt (receiver : Fin source.code.sites) (count : Nat) :
    ((run source input cut protocol rival vocabulary encoding law receiver count).receipts.map
      fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)).Nodup := by
  induction count with
  | zero => simp [run]
  | succ n ih =>
    simp only [run, receive]
    split
    · rename_i wire outcome
      have fresh : (wire.ballot.cut, wire.ballot.position) ∉
          ((run source input cut protocol rival vocabulary encoding law receiver n).receipts.map
            fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) := by
        cases candidate : incoming source input cut protocol rival vocabulary encoding n with
        | none => simp [candidate] at outcome
        | some body =>
          simp only [candidate] at outcome
          obtain ⟨rfl, _, _, _, _, _, _, _, _, unused⟩ :=
            check_sound source input cut protocol rival vocabulary encoding law receiver n _ body wire outcome
          exact unused
      simpa using List.nodup_append.mpr ⟨ih, by simp, by simpa using fresh⟩
    · exact ih

def evidence (observed : Receiver source) : List (Receipt source × Receipt source) :=
  (observed.receipts.product observed.receipts).filter fun pair =>
    OwnedAttestation.conflicts source pair.1.wire.ballot pair.2.wire.ballot

theorem generated_conflict_evidence_has_two_actual_owned_origins
    (receiver : Fin source.code.sites) (count : Nat) (first second : Receipt source)
    (inside : (first, second) ∈ evidence source
      (run source input cut protocol rival vocabulary encoding law receiver count)) :
    OwnedAttestation.verify source input cut protocol rival vocabulary first.wire.ballot = true ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary second.wire.ballot = true ∧
      first.wire.ballot.key = second.wire.ballot.key ∧
      first.wire.ballot.scope = second.wire.ballot.scope ∧
      first.wire.ballot.choice ≠ second.wire.ballot.choice ∧
      (first.wire.ballot.cut, first.wire.ballot.position) ≠ (second.wire.ballot.cut, second.wire.ballot.position) := by
  obtain ⟨members, conflict⟩ := List.mem_filter.mp inside
  obtain ⟨one, two⟩ := List.mem_product.mp members
  have auth₁ := (receipts_have_actual_communication source input cut protocol rival vocabulary encoding law receiver count first one).1
  have auth₂ := (receipts_have_actual_communication source input cut protocol rival vocabulary encoding law receiver count second two).1
  have owned₁ := (authenticated_wire_has_an_earlier_owned_paid_statement source input cut protocol rival vocabulary encoding first.wire auth₁).2.2.1
  have owned₂ := (authenticated_wire_has_an_earlier_owned_paid_statement source input cut protocol rival vocabulary encoding second.wire auth₂).2.2.1
  obtain ⟨key, scope, different⟩ := of_decide_eq_true conflict
  refine ⟨owned₁, owned₂, key, scope, different, ?_⟩
  intro same
  have origin₁ := of_decide_eq_true owned₁
  have origin₂ := of_decide_eq_true owned₂
  have cuts := congrArg Prod.fst same
  have positions := congrArg Prod.snd same
  dsimp only at cuts positions
  rw [cuts, positions, origin₂] at origin₁
  exact different (congrArg OwnedAttestation.BallotData.choice (Option.some.inj origin₁).symm)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception

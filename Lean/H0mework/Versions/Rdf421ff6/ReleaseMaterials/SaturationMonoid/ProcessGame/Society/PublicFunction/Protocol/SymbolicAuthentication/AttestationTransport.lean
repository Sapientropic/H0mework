import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedAttestation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationTransport

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Fixed finite serialization of the complete ballot body. The decoded body
is only a candidate: the owned source execution must independently generate it. -/
abbrev Encoding := Fin source.code.signals → Option (OwnedAttestation.Ballot source)

structure WireData (Body : Type) (sites signals : Nat) where
  sendCut : Nat
  serial : Nat
  recipient : Fin sites
  signal : Fin signals
  sentAfter : Nat
  ballot : Body
  deriving DecidableEq

abbrev Wire := WireData (OwnedAttestation.Ballot source) source.code.sites source.code.signals
abbrev state (n : Nat) := OwnedAttestation.localState source input cut protocol rival n
abbrev execution (n : Nat) := OwnedAttestation.execution source input cut protocol rival n
abbrev actualInput := Distributed.Recall.Information.Agency.Protocol.targetInput source input cut protocol rival
def move (n : Nat) := decision source.code (actualInput source input cut protocol rival)
  (state source input cut protocol rival n)

def outgoing (n : Nat) : Option (Fin source.code.sites × Fin source.code.sites) :=
  if source.continuation.isEmpty then
    if n < (source.feedbackState input cut).remaining then
      match Distributed.Recall.Information.Agency.ownerAt source.code
          (Distributed.Recall.Information.Agency.start source cut)
          (state source input cut protocol rival n).history.length with
      | none => none
      | some site =>
        match Distributed.Recall.Information.Agency.Protocol.localEvent source.code protocol site
            ((state source input cut protocol rival n).frame.inbox site) with
        | none => none
        | some event => match event.val with
          | .send sender recipient => if sender = site then some (sender, recipient) else none
          | _ => none
    else none
  else none

theorem outgoing_submits_the_original_send_cost (n : Nat)
    (sender recipient : Fin source.code.sites)
    (generated : outgoing source input cut protocol rival n = some (sender, recipient)) :
    source.continuation = [] ∧
      (execution source input cut protocol rival n).submitted = source.code.sendCost sender recipient := by
  have empty : source.continuation = [] := by
    cases present : source.continuation with
    | nil => rfl
    | cons head tail => simp [outgoing, present] at generated
  simp only [outgoing, empty, List.isEmpty_nil, if_true] at generated
  split at generated <;> try contradiction
  rename_i bounded
  split at generated <;> try contradiction
  rename_i site owned
  split at generated <;> try contradiction
  rename_i event chosen
  split at generated <;> try contradiction
  rename_i sending receiving kind
  split at generated <;> try contradiction
  rename_i own
  have same := Option.some.inj generated
  cases same
  subst site
  exact ⟨empty, Distributed.Recall.Information.Agency.Protocol.actual_own_read_submits_the_original_fee
    source input cut protocol rival empty n bounded sender recipient owned event chosen kind⟩

variable (encoding : Encoding source)

/-- Read the new packet at the old queue length from the actual next feedback
state. No flattened replay, caller packet, or caller ballot enters this producer. -/
def issuedAt (n : Nat) : Option (Wire source) :=
  match outgoing source input cut protocol rival n with
  | none => none
  | some (sender, recipient) =>
    let serial := (state source input cut protocol rival n).frame.sent.length
    match (state source input cut protocol rival (n + 1)).frame.sent[serial]? with
    | none => none
    | some packet =>
      if packet.sender ≠ sender ∨ packet.recipient ≠ recipient then none
      else if ¬ ∀ item ∈ source.code.law.rawItems
          (execution source input cut protocol rival n).before (source.code.sendCost sender recipient),
          source.code.law.Valid item.before item.request then none
      else match encoding packet.signal with
      | none => none
      | some ballot =>
        if ¬ ballot.cut < n then none
        else if OwnedAttestation.verify source input cut protocol rival vocabulary ballot ≠ true then none
        else if ballot.key ≠ sender then none
        else if ¬ (state source input cut protocol rival ballot.cut).frame.word.length + ballot.position < packet.sentAfter then none
        else some ⟨n, serial, recipient, packet.signal, packet.sentAfter, ballot⟩

def verify (wire : Wire source) : Bool :=
  decide (issuedAt source input cut protocol rival vocabulary encoding wire.sendCut = some wire)

theorem issued_has_actual_packet_and_owned_ballot (n : Nat) (wire : Wire source)
    (generated : issuedAt source input cut protocol rival vocabulary encoding n = some wire) :
    ∃ sender recipient packet ballot,
      outgoing source input cut protocol rival n = some (sender, recipient) ∧
      (state source input cut protocol rival (n + 1)).frame.sent[
        (state source input cut protocol rival n).frame.sent.length]? = some packet ∧
      packet.sender = sender ∧ packet.recipient = recipient ∧
      (∀ item ∈ source.code.law.rawItems
        (execution source input cut protocol rival n).before (source.code.sendCost sender recipient),
        source.code.law.Valid item.before item.request) ∧
      encoding packet.signal = some ballot ∧ ballot.cut < n ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary ballot = true ∧
      ballot.key = sender ∧
      (state source input cut protocol rival ballot.cut).frame.word.length + ballot.position < packet.sentAfter ∧
      wire = ⟨n, (state source input cut protocol rival n).frame.sent.length,
        recipient, packet.signal, packet.sentAfter, ballot⟩ := by
  unfold issuedAt at generated
  split at generated <;> try contradiction
  rename_i sender recipient sent
  dsimp only at generated
  split at generated <;> try contradiction
  rename_i packet actualPacket
  split at generated <;> try contradiction
  rename_i addresses
  split at generated <;> try contradiction
  rename_i paid
  split at generated <;> try contradiction
  rename_i ballot encoded
  split at generated <;> try contradiction
  rename_i earlier
  split at generated <;> try contradiction
  rename_i attested
  split at generated <;> try contradiction
  rename_i key
  split at generated <;> try contradiction
  rename_i timestamp
  have same := (Option.some.inj generated).symm
  have matching : packet.sender = sender ∧ packet.recipient = recipient := by
    simpa only [not_or, not_not] using addresses
  exact ⟨sender, recipient, packet, ballot, sent, actualPacket, matching.1, matching.2,
    by simpa only [not_not] using paid, encoded,
    by simpa only [not_not] using earlier,
    by simpa only [not_not] using attested,
    by simpa only [not_not] using key,
    by simpa only [not_not] using timestamp, same⟩

theorem authenticated_wire_has_an_earlier_owned_paid_statement (wire : Wire source)
    (authenticated : verify source input cut protocol rival vocabulary encoding wire = true) :
    source.continuation = [] ∧
      (execution source input cut protocol rival wire.sendCut).submitted =
        source.code.sendCost wire.ballot.key wire.recipient ∧
      OwnedAttestation.verify source input cut protocol rival vocabulary wire.ballot = true ∧
      wire.ballot.cut < wire.sendCut ∧
      encoding wire.signal = some wire.ballot ∧
      (state source input cut protocol rival wire.ballot.cut).frame.word.length + wire.ballot.position < wire.sentAfter := by
  have generated := of_decide_eq_true authenticated
  obtain ⟨sender, recipient, packet, ballot, sent, _, _, _, _, encoded, earlier, attested, key, timestamp, same⟩ :=
    issued_has_actual_packet_and_owned_ballot source input cut protocol rival vocabulary encoding wire.sendCut wire generated
  have submitted := outgoing_submits_the_original_send_cost source input cut protocol rival wire.sendCut sender recipient sent
  rw [same]
  dsimp only
  rw [key]
  exact ⟨submitted.1, submitted.2, attested, earlier, encoded, timestamp⟩

theorem same_send_has_one_wire (left right : Wire source)
    (one : verify source input cut protocol rival vocabulary encoding left = true)
    (two : verify source input cut protocol rival vocabulary encoding right = true)
    (same : left.sendCut = right.sendCut) : left = right := by
  have first := of_decide_eq_true one
  have second := of_decide_eq_true two
  rw [same, second] at first
  exact (Option.some.inj first).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationTransport

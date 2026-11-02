import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueScheduler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptOrigin

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

theorem actual_queue_prefix (n m : Nat) (later : n ≤ m) :
    (state source input cut protocol rival n).frame.sent <+:
      (state source input cut protocol rival m).frame.sent := by
  induction m, later using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
    apply ih.trans
    change _ <+: (advance source.code _ _ _).frame.sent
    exact (QueueScheduler.advance_preserves_memory_and_queue source.code _ _ _).2

theorem packet_at_a_stable_address (n m serial : Nat) (later : n ≤ m)
    (packet : source.code.Packet)
    (actual : (state source input cut protocol rival n).frame.sent[serial]? = some packet) :
    (state source input cut protocol rival m).frame.sent[serial]? = some packet := by
  obtain ⟨more, same⟩ := actual_queue_prefix source input cut protocol rival n m later
  rw [← same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp actual).1]
  exact actual

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : Encoding source)

theorem issued_identity (n : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some wire) :
    wire.sendCut = n ∧ wire.serial = (state source input cut protocol rival n).frame.sent.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ :=
    issued_has_actual_packet_and_owned_ballot source input cut protocol rival vocabulary encoding n wire generated
  rw [same]
  exact ⟨rfl, rfl⟩

theorem issued_address_is_new_and_present (n : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some wire) :
    (state source input cut protocol rival n).frame.sent.length = wire.serial ∧
      wire.serial < (state source input cut protocol rival (n + 1)).frame.sent.length := by
  obtain ⟨_, _, _, _, _, packet, _, _, _, _, _, _, _, _, _⟩ :=
    issued_has_actual_packet_and_owned_ballot source input cut protocol rival vocabulary encoding n wire generated
  have serial := (issued_identity source input cut protocol rival vocabulary encoding n wire generated).2
  exact ⟨serial.symm, by simpa only [serial] using (List.getElem?_eq_some_iff.mp packet).1⟩

theorem same_serial_has_one_actual_wire (n m : Nat) (one two : Wire source)
    (first : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some one)
    (second : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding m = some two)
    (same : one.serial = two.serial) : one = two := by
  have a := issued_address_is_new_and_present source input cut protocol rival vocabulary encoding n one first
  have b := issued_address_is_new_and_present source input cut protocol rival vocabulary encoding m two second
  have cuts : n = m := by
    by_contra different
    rcases lt_or_gt_of_ne different with before | before
    · have grows := (actual_queue_prefix source input cut protocol rival (n + 1) m (by omega)).length_le
      omega
    · have grows := (actual_queue_prefix source input cut protocol rival (m + 1) n (by omega)).length_le
      omega
  subst m
  exact Option.some.inj (first.symm.trans second)

theorem issued_packet_matches_at_every_later_cut (n m : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some wire)
    (later : n < m) : AttestationReception.matchingPacket source input cut protocol rival m wire = true := by
  obtain ⟨sender, recipient, packet, ballot, _, actual, senderEq, recipientEq, _, _, _, _, key, _, same⟩ :=
    issued_has_actual_packet_and_owned_ballot source input cut protocol rival vocabulary encoding n wire generated
  have kept := packet_at_a_stable_address source input cut protocol rival (n + 1) m _ (by omega) packet actual
  simp only [same, AttestationReception.matchingPacket, kept]
  simp only [senderEq, recipientEq, key, and_self, decide_true]

/-- Incoming is reconstructed from the original delivery address and the
unique actual send that generated that address. -/
theorem actual_delivery_reconstructs_the_original_wire (n delivered : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding n = some wire)
    (earlier : n < delivered)
    (attempt : AttestationReception.deliveredAt source input cut protocol rival delivered wire.serial = true) :
    AttestationReception.incoming source input cut protocol rival vocabulary encoding delivered = some wire := by
  have actual := attempt
  unfold AttestationReception.deliveredAt at actual
  split at actual <;> try contradiction
  split at actual <;> try contradiction
  rename_i event chosen
  split at actual <;> try contradiction
  rename_i serial kind
  have address : serial = wire.serial := of_decide_eq_true actual
  unfold AttestationReception.incoming
  rw [chosen]
  dsimp only
  rw [kind]
  dsimp only
  have member : wire ∈ (List.range delivered).filterMap (AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding) :=
    List.mem_filterMap.mpr ⟨n, List.mem_range.mpr earlier, generated⟩
  cases found : ((List.range delivered).filterMap (AttestationTransport.issuedAt source input cut protocol rival vocabulary encoding)).find?
      (fun candidate => candidate.serial == serial) with
  | none =>
    have missing := List.find?_eq_none.mp found wire member
    exact False.elim (missing (by simpa only [address] using (beq_self_eq_true wire.serial)))
  | some body =>
    obtain ⟨origin, _, issued⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some found)
    have serialEq : body.serial = wire.serial := (of_decide_eq_true
      (List.find?_some (p := fun (candidate : Wire source) => candidate.serial == serial) found)).trans address
    have same := same_serial_has_one_actual_wire source input cut protocol rival vocabulary encoding origin n body wire issued generated serialEq
    simpa only [found] using congrArg some same

theorem scheduled_delivery_was_queued (n serial : Nat)
    (attempt : AttestationReception.deliveredAt source input cut protocol
      (QueueScheduler.environment source input cut) n serial = true) :
    serial < (QueueScheduler.state source input cut protocol n).frame.sent.length := by
  have actual := attempt
  unfold AttestationReception.deliveredAt at actual
  split at actual <;> try contradiction
  rename_i bounded
  split at actual <;> try contradiction
  rename_i event chosen
  split at actual <;> try contradiction
  rename_i address kind
  have serialEq : address = serial := of_decide_eq_true actual
  have external : Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut)
      (QueueScheduler.state source input cut protocol n).history.length = none := by
    cases turn : Distributed.Recall.Information.Agency.ownerAt source.code
        (Distributed.Recall.Information.Agency.start source cut)
        (QueueScheduler.state source input cut protocol n).history.length with
    | none => rfl
    | some site =>
      have ownMove := Distributed.Recall.Information.Agency.Protocol.own_decision_is_generated_from_the_actual_local_record
        source input cut protocol (QueueScheduler.environment source input cut) n bounded site turn
      have selected := ownMove.symm.trans chosen
      have own := Distributed.Recall.Information.Agency.Protocol.every_local_event_has_its_own_worker
        source.code protocol site _ event selected
      simp only [kind] at own
  have selected := (QueueScheduler.actual_external_turn_uses_the_queue source input cut protocol n bounded external).symm.trans chosen
  obtain ⟨picked, pickedKind, present, _⟩ := QueueScheduler.generated_move_has_actual_queue_and_fresh_address
    source.code _ _ _ _ event selected
  have same : picked = serial := (Event.deliver.inj (pickedKind.symm.trans kind)).trans serialEq
  simpa only [same] using present

theorem a_new_wire_has_no_old_scheduled_attempt (send : Nat) (wire : Wire source)
    (generated : AttestationTransport.issuedAt source input cut protocol
      (QueueScheduler.environment source input cut) vocabulary encoding send = some wire)
    (bounded : send + 1 ≤ (source.feedbackState input cut).remaining) :
    wire.serial ∉ QueueScheduler.attempted source.code (QueueScheduler.baseline source input cut)
      (QueueScheduler.state source input cut protocol (send + 1)).past := by
  intro old
  obtain ⟨n, earlier, delivered⟩ := (QueueScheduler.attempted_memory_is_the_actual_delivery_history
    source input cut protocol (send + 1) wire.serial bounded).mp old
  have present := scheduled_delivery_was_queued source input cut protocol n wire.serial delivered
  have grows := (actual_queue_prefix source input cut protocol (QueueScheduler.environment source input cut)
    n send (by omega)).length_le
  have newAddress := (issued_identity source input cut protocol (QueueScheduler.environment source input cut)
    vocabulary encoding send wire generated).2
  change wire.serial < (state source input cut protocol (QueueScheduler.environment source input cut) n).frame.sent.length at present
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptOrigin

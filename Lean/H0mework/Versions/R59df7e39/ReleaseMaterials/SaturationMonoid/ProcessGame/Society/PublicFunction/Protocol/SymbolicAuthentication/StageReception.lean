import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTransport

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageReception

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open StageTransport

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

structure Law (code : Code Party Good Port (Mandate.State Party Technology) Instrument) where
  scope : Fin code.sites → RawCurrent Party Good (Mandate.State Party Technology) Instrument → Scope
  maxDelay : Nat

structure ReceiptData (Body : Type) where
  wire : Body
  index : Nat
  delivery : Nat
  deriving DecidableEq

abbrev Receipt := ReceiptData (Wire (code := code))
abbrev Verdict := AttestationReception.VerdictData (Wire (code := code))

structure ReceiverData (Body : Type) where
  receipts : List (ReceiptData Body)
  audit : List (Nat × Option Body × AttestationReception.VerdictData Body)
  deriving DecidableEq

abbrev Receiver := ReceiverData (Wire (code := code))

def delivered (row : StageTrace.Record (code := code)) (serial : Nat) : Bool :=
  match admission row with
  | some event => match event.val with
    | .deliver address => address == serial
    | _ => false
  | none => false

def matchingPacket (row : StageTrace.Record (code := code)) (wire : Wire (code := code)) : Bool :=
  match row.before.frame.sent[wire.serial]? with
  | none => false
  | some packet => decide (packet.sender = wire.ballot.key ∧ packet.recipient = wire.recipient ∧
      packet.signal = wire.signal ∧ packet.sentAfter = wire.sentAfter)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem matched_packet_is_actual (row : StageTrace.Record (code := code)) (wire : Wire (code := code))
    (matched : matchingPacket row wire = true) :
    ∃ packet, row.before.frame.sent[wire.serial]? = some packet ∧
      packet.sender = wire.ballot.key ∧ packet.recipient = wire.recipient ∧
      packet.signal = wire.signal ∧ packet.sentAfter = wire.sentAfter := by
  unfold matchingPacket at matched
  split at matched <;> try contradiction
  rename_i packet present
  exact ⟨packet, present, of_decide_eq_true matched⟩

theorem actual_delivery_submits_the_original_cost
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : StageTrace.Record (code := code)) (inside : row ∈ StageTrace.records cursor stages)
    (serial : Nat) (packet : code.Packet) (sent : row.before.frame.sent[serial]? = some packet)
    (delivery : delivered row serial = true) : row.submitted = code.deliveryCost packet.recipient := by
  unfold delivered at delivery
  split at delivery <;> try contradiction
  rename_i event chosen
  split at delivery <;> try contradiction
  rename_i address kind
  have same : address = serial := of_decide_eq_true delivery
  subst address
  obtain ⟨pastStages, protocol, rival, suffix, _, actual⟩ :=
    StageTrace.every_record_retains_its_actual_stage cursor stages row inside
  subst row
  change (EventStep.seed (EventHistory.execute cursor pastStages)).frame.sent[serial]? = some packet at sent
  rw [a_material_admission_uses_the_actual_selected_event _ protocol rival event chosen]
  simp only [stepLocal, kind, Code.step, sent, List.nil_append]

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : Encoding (code := code)) (law : Law code)
  (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))

def check (receiver : Fin code.sites) (row : StageTrace.Record (code := code))
    (seen : List (Nat × Nat)) (wire : Wire (code := code)) : Verdict (code := code) :=
  if delivered row wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.sendCut < row.cursor.cut then .rejected .unauthenticated
  else if StageTransport.verify vocabulary encoding cursor stages wire ≠ true then .rejected .unauthenticated
  else if matchingPacket row wire ≠ true then .rejected .missingPacket
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.ballot.scope ≠ law.scope receiver row.before.current then .rejected .staleScope
  else if ¬ row.cursor.cut ≤ wire.sendCut + law.maxDelay then .rejected .late
  else if ¬ ∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request then .rejected .unpaidDelivery
  else if (wire.ballot.cut, wire.ballot.position) ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_sound (receiver : Fin code.sites) (row : StageTrace.Record (code := code))
    (seen : List (Nat × Nat)) (wire result : Wire (code := code))
    (accepted : check vocabulary encoding law cursor stages receiver row seen wire = .accepted result) :
    result = wire ∧ delivered row wire.serial = true ∧ wire.sendCut < row.cursor.cut ∧
      StageTransport.verify vocabulary encoding cursor stages wire = true ∧
      matchingPacket row wire = true ∧ wire.recipient = receiver ∧
      wire.ballot.scope = law.scope receiver row.before.current ∧
      row.cursor.cut ≤ wire.sendCut + law.maxDelay ∧
      (∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request) ∧
      (wire.ballot.cut, wire.ballot.position) ∉ seen := by
  unfold check at accepted
  split_ifs at accepted; simp_all

def incoming (index : Nat) : Option (Wire (code := code)) :=
  match (StageTrace.records cursor stages)[index]? with
  | none => none
  | some row => match admission row with
    | none => none
    | some event => match event.val with
      | .deliver serial => ((List.range index).filterMap (StageTransport.issuedAt vocabulary encoding cursor stages)).find?
          (fun wire => wire.serial == serial)
      | _ => none

def receive (receiver : Fin code.sites) (index : Nat) (previous : Receiver (code := code)) : Receiver (code := code) :=
  match (StageTrace.records cursor stages)[index]? with
  | none => previous
  | some row =>
    let candidate := incoming vocabulary encoding cursor stages index
    let verdict := match candidate with
      | none => AttestationReception.VerdictData.rejected .missingWire
      | some wire => check vocabulary encoding law cursor stages receiver row
          (previous.receipts.map fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) wire
    ⟨match verdict with
      | .accepted wire => previous.receipts ++ [⟨wire, index, row.cursor.cut⟩]
      | .rejected _ => previous.receipts,
      previous.audit ++ [(row.cursor.cut, candidate, verdict)]⟩

def run (receiver : Fin code.sites) : Nat → Receiver (code := code)
  | 0 => ⟨[], []⟩
  | index + 1 => receive vocabulary encoding law cursor stages receiver index (run receiver index)

theorem observation_past_the_actual_history_creates_no_extra_audit
    (receiver : Fin code.sites) (extra : Nat) :
    run vocabulary encoding law cursor stages receiver (stages.length + extra) =
      run vocabulary encoding law cursor stages receiver stages.length := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have absent : (StageTrace.records cursor stages)[stages.length + extra]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      rw [StageTrace.record_count]
      omega
    change receive vocabulary encoding law cursor stages receiver (stages.length + extra)
      (run vocabulary encoding law cursor stages receiver (stages.length + extra)) = _
    unfold receive
    rw [absent]
    exact ih

theorem every_receipt_retains_its_actual_delivery
    (receiver : Fin code.sites) (count : Nat) (receipt : Receipt (code := code))
    (inside : receipt ∈ (run vocabulary encoding law cursor stages receiver count).receipts) :
    ∃ row seen, (StageTrace.records cursor stages)[receipt.index]? = some row ∧
      receipt.delivery = row.cursor.cut ∧ receipt.index < count ∧
      check vocabulary encoding law cursor stages receiver row seen receipt.wire = .accepted receipt.wire := by
  induction count with
  | zero => simp [run] at inside
  | succ index ih =>
    simp only [run, receive] at inside
    split at inside
    · exact (ih inside).imp fun row ⟨seen, actual, cut, bounded, accepted⟩ =>
        ⟨seen, actual, cut, by omega, accepted⟩
    · rename_i row actual
      split at inside
      · rename_i wire outcome
        rcases List.mem_append.mp inside with old | fresh
        · obtain ⟨row, seen, original, cut, bounded, accepted⟩ := ih old
          exact ⟨row, seen, original, cut, by omega, accepted⟩
        · cases List.mem_singleton.mp fresh
          cases candidate : incoming vocabulary encoding cursor stages index with
          | none => simp [candidate] at outcome
          | some body =>
            simp only [candidate] at outcome
            obtain ⟨rfl, _⟩ := check_sound vocabulary encoding law cursor stages receiver row _ body wire outcome
            exact ⟨row, _, actual, rfl, Nat.lt_succ_self _, outcome⟩
      · obtain ⟨row, seen, original, cut, bounded, accepted⟩ := ih inside
        exact ⟨row, seen, original, cut, by omega, accepted⟩

theorem receipt_has_actual_send_delivery_and_owned_ballot_origin
    (receiver : Fin code.sites) (count : Nat) (receipt : Receipt (code := code))
    (inside : receipt ∈ (run vocabulary encoding law cursor stages receiver count).receipts) :
    ∃ sendIndex sendRow origin deliveryRow packet,
      (StageTrace.records cursor stages)[sendIndex]? = some sendRow ∧
      origin ∈ (StageTrace.records cursor stages).take sendIndex ∧
      receipt.wire.ballot ∈ StageBudget.ledger vocabulary cursor stages ∧
      sendRow.submitted = code.sendCost receipt.wire.ballot.key receiver ∧
      (StageTrace.records cursor stages)[receipt.index]? = some deliveryRow ∧
      receipt.delivery = deliveryRow.cursor.cut ∧ receipt.wire.sendCut < receipt.delivery ∧
      deliveryRow.before.frame.sent[receipt.wire.serial]? = some packet ∧
      encoding packet.signal = some receipt.wire.ballot ∧
      deliveryRow.submitted = code.deliveryCost receiver ∧
      (∀ item ∈ StageTrace.items sendRow, code.law.Valid item.before item.request) ∧
      (∀ item ∈ StageTrace.items deliveryRow, code.law.Valid item.before item.request) ∧
      receipt.wire.ballot.scope = law.scope receiver deliveryRow.before.current ∧
      receipt.delivery ≤ receipt.wire.sendCut + law.maxDelay := by
  obtain ⟨row, seen, actual, cut, _, accepted⟩ := every_receipt_retains_its_actual_delivery vocabulary encoding law cursor stages receiver count receipt inside
  obtain ⟨_, delivered, earlier, auth, matched, who, scope, time, valid, _⟩ :=
    check_sound vocabulary encoding law cursor stages receiver row seen receipt.wire receipt.wire accepted
  obtain ⟨sendIndex, sendRow, origin, sentPacket, sent, prior, _, owned, _, sentWord,
    _, _, _, _, _, decoded, _, sentValid, _⟩ :=
    authenticated_wire_has_actual_send_and_paid_ballot vocabulary encoding cursor stages receipt.wire auth
  obtain ⟨packet, present, _, recipient, signal, _⟩ := matched_packet_is_actual row receipt.wire matched
  have word := actual_delivery_submits_the_original_cost cursor stages row
    (List.mem_of_getElem? actual) receipt.wire.serial packet present delivered
  rw [recipient, who] at word
  exact ⟨sendIndex, sendRow, origin, row, packet, sent, prior, owned,
    by simpa only [who] using sentWord, actual, cut, by simpa only [cut] using earlier,
    present, by simpa only [signal] using decoded, word, sentValid, valid, scope,
    by simpa only [cut] using time⟩

theorem duplicate_delivery_cannot_duplicate_an_origin
    (receiver : Fin code.sites) (count : Nat) :
    ((run vocabulary encoding law cursor stages receiver count).receipts.map
      fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)).Nodup := by
  induction count with
  | zero => simp [run]
  | succ index ih =>
    simp only [run, receive]
    split
    · exact ih
    · rename_i row _
      split
      · rename_i wire outcome
        have fresh : (wire.ballot.cut, wire.ballot.position) ∉
            ((run vocabulary encoding law cursor stages receiver index).receipts.map
              fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position)) := by
          cases candidate : incoming vocabulary encoding cursor stages index with
          | none => simp [candidate] at outcome
          | some body =>
            simp only [candidate] at outcome
            obtain ⟨rfl, _, _, _, _, _, _, _, _, unused⟩ :=
              check_sound vocabulary encoding law cursor stages receiver row _ body wire outcome
            exact unused
        simpa using List.nodup_append.mpr ⟨ih, by simp, by simpa using fresh⟩
      · exact ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageReception

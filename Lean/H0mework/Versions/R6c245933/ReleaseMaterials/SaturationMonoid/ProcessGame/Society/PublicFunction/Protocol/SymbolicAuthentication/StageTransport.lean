import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTransport

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Wire := AttestationTransport.WireData (StageBudget.Ballot (code := code)) code.sites code.signals
abbrev Encoding := Fin code.signals → Option (StageBudget.Ballot (code := code))
abbrev admission (row : StageTrace.Record (code := code)) := ControlExecution.admitted code row.call

theorem a_material_admission_uses_the_actual_selected_event
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (event : Choice code)
    (chosen : admission (StageTrace.material cursor protocol rival) = some event) :
    (StageTrace.material cursor protocol rival).submitted =
      (stepLocal code protocol.work.val (EventStep.seed cursor) event.val).word := by
  have live : (EventStep.seed cursor).remaining ≠ 0 := by
    intro stopped
    simp only [admission, StageTrace.material, StageTrace.capture, if_pos stopped,
      ControlExecution.admitted] at chosen
    contradiction
  change ControlExecution.admitted code (StageTrace.capture cursor protocol rival (EventStep.seed cursor)) = some event at chosen
  change word code (some protocol.work.val) _ (EventStep.seed cursor) = _
  simp only [word, decision, if_neg live, chosen]

def outgoing (row : StageTrace.Record (code := code)) : Option (Fin code.sites × Fin code.sites) :=
  match row.call with
  | .own site (some event) => match event.val with
    | .send sender recipient => if sender = site then some (sender, recipient) else none
    | _ => none
  | _ => none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem outgoing_has_an_owned_call (row : StageTrace.Record (code := code))
    (sender recipient : Fin code.sites) (sent : outgoing row = some (sender, recipient)) :
    ∃ event, row.call = .own sender (some event) ∧ event.val = .send sender recipient := by
  unfold outgoing at sent
  split at sent <;> try contradiction
  rename_i site event call
  split at sent <;> try contradiction
  rename_i sending receiving kind
  split at sent <;> try contradiction
  rename_i own
  cases Option.some.inj sent
  subst site
  exact ⟨event, call, kind⟩

theorem outgoing_submits_the_original_send_cost
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (row : StageTrace.Record (code := code)) (inside : row ∈ StageTrace.records cursor stages)
    (sender recipient : Fin code.sites) (sent : outgoing row = some (sender, recipient)) :
    row.submitted = code.sendCost sender recipient := by
  obtain ⟨event, call, kind⟩ := outgoing_has_an_owned_call row sender recipient sent
  obtain ⟨pastStages, protocol, rival, suffix, _, same⟩ :=
    StageTrace.every_record_retains_its_actual_stage cursor stages row inside
  subst row
  have chosen : admission (StageTrace.material (EventHistory.execute cursor pastStages) protocol rival) = some event := by
    simp only [admission, call, ControlExecution.admitted]
  rw [a_material_admission_uses_the_actual_selected_event _ protocol rival event chosen]
  simp only [stepLocal, kind, Code.step, List.nil_append]

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def ballots (row : StageTrace.Record (code := code)) :=
  (List.range row.submitted.length).filterMap (StageBudget.issued vocabulary row)

variable (encoding : Encoding (code := code))

/-- Serialization supplies a candidate. An earlier actual owned item must independently generate it. -/
def issue (earlier : List (StageTrace.Record (code := code))) (row : StageTrace.Record (code := code)) : Option (Wire (code := code)) :=
  match outgoing row with
  | none => none
  | some (sender, recipient) =>
    let serial := row.before.frame.sent.length
    match row.after.frame.sent[serial]? with
    | none => none
    | some packet =>
      if packet.sender ≠ sender ∨ packet.recipient ≠ recipient then none
      else if ¬ ∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request then none
      else match encoding packet.signal with
      | none => none
      | some body =>
        match earlier.find? (fun origin => decide (body ∈ ballots vocabulary origin)) with
        | none => none
        | some origin =>
          if ¬ body.cut < row.cursor.cut then none
          else if body.key ≠ sender then none
          else if ¬ origin.before.frame.word.length + body.position < packet.sentAfter then none
          else some ⟨row.cursor.cut, serial, recipient, packet.signal, packet.sentAfter, body⟩

def issuedAt (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (index : Nat) : Option (Wire (code := code)) :=
  let rows := StageTrace.records cursor stages
  match rows[index]? with
  | none => none
  | some row => issue vocabulary encoding (rows.take index) row

def wires (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :=
  (List.range stages.length).filterMap (issuedAt vocabulary encoding cursor stages)

def verify (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (wire : Wire (code := code)) : Bool :=
  decide (wire ∈ wires vocabulary encoding cursor stages)

theorem issue_has_actual_packet_and_prior_owned_item
    (earlier : List (StageTrace.Record (code := code))) (row : StageTrace.Record (code := code))
    (wire : Wire (code := code)) (made : issue vocabulary encoding earlier row = some wire) :
    ∃ sender recipient packet body origin,
      outgoing row = some (sender, recipient) ∧
      row.after.frame.sent[row.before.frame.sent.length]? = some packet ∧
      packet.sender = sender ∧ packet.recipient = recipient ∧
      (∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request) ∧
      encoding packet.signal = some body ∧ origin ∈ earlier ∧ body ∈ ballots vocabulary origin ∧
      body.cut < row.cursor.cut ∧ body.key = sender ∧
      origin.before.frame.word.length + body.position < packet.sentAfter ∧
      wire = ⟨row.cursor.cut, row.before.frame.sent.length, recipient, packet.signal, packet.sentAfter, body⟩ := by
  unfold issue at made
  split at made <;> try contradiction
  rename_i sender recipient sent
  dsimp only at made
  split at made <;> try contradiction
  rename_i packet present
  split at made <;> try contradiction
  rename_i address
  split at made <;> try contradiction
  rename_i valid
  split at made <;> try contradiction
  rename_i body decoded
  split at made <;> try contradiction
  rename_i origin found
  split at made <;> try contradiction
  rename_i earlierCut
  split at made <;> try contradiction
  rename_i key
  split at made <;> try contradiction
  rename_i timestamp
  have members := List.mem_of_find?_eq_some found
  have authenticated := of_decide_eq_true (List.find?_some (p := fun origin => decide (body ∈ ballots vocabulary origin)) found)
  have addresses : packet.sender = sender ∧ packet.recipient = recipient := by
    simpa only [not_or, not_not] using address
  exact ⟨sender, recipient, packet, body, origin, sent, present, addresses.1, addresses.2,
    by simpa only [not_not] using valid, decoded, members, authenticated,
    by simpa only [not_not] using earlierCut, by simpa only [not_not] using key,
    by simpa only [not_not] using timestamp, (Option.some.inj made).symm⟩

theorem authenticated_wire_has_actual_send_and_paid_ballot
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (wire : Wire (code := code)) (authenticated : verify vocabulary encoding cursor stages wire = true) :
    ∃ index row origin packet,
      (StageTrace.records cursor stages)[index]? = some row ∧
      origin ∈ (StageTrace.records cursor stages).take index ∧
      wire.ballot ∈ ballots vocabulary origin ∧
      wire.ballot ∈ StageBudget.ledger vocabulary cursor stages ∧
      row.cursor.cut = wire.sendCut ∧ row.submitted = code.sendCost wire.ballot.key wire.recipient ∧
      row.after.frame.sent[wire.serial]? = some packet ∧
      packet.sender = wire.ballot.key ∧ packet.recipient = wire.recipient ∧
      packet.signal = wire.signal ∧ packet.sentAfter = wire.sentAfter ∧
      encoding wire.signal = some wire.ballot ∧ wire.ballot.cut < wire.sendCut ∧
      (∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request) ∧
      origin.before.frame.word.length + wire.ballot.position < wire.sentAfter := by
  obtain ⟨index, _, made⟩ := List.mem_filterMap.mp (of_decide_eq_true authenticated)
  unfold issuedAt at made
  dsimp only at made
  split at made <;> try contradiction
  rename_i row actual
  obtain ⟨sender, recipient, packet, body, origin, sent, present, senderMatch, recipientMatch, valid, decoded,
    prior, owned, earlierCut, key, timestamp, same⟩ := issue_has_actual_packet_and_prior_owned_item vocabulary encoding _ row wire made
  have word := outgoing_submits_the_original_send_cost cursor stages row (List.mem_of_getElem? actual) sender recipient sent
  have ledger : body ∈ StageBudget.ledger vocabulary cursor stages :=
    List.mem_flatMap.mpr ⟨origin, List.mem_of_mem_take prior, owned⟩
  rw [same]
  exact ⟨index, row, origin, packet, actual, prior, owned, ledger, rfl, by simpa only [key] using word,
    present, senderMatch.trans key.symm, recipientMatch, rfl, rfl, decoded, earlierCut, valid, timestamp⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageTransport

import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestAttestationRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadback

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Zero is the empty code. Positive codes address the source's registered action
-- alphabet, independently of the actual history, wire or candidate statement.
def decode (reading : Fin code.signals) : Option (RequestAttestation.Request (Party := Party)
    (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :=
  match reading.val with
  | 0 => none
  | n + 1 => code.actions[n]?

def localRead (reading : Fin code.signals) := if code.memoryReady reading then decode (code := code) reading else none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem equal_local_records_generate_equal_request_readings (left right : Fin code.signals) (same : left = right) :
    localRead (code := code) left = localRead (code := code) right := congrArg localRead same

structure ReceiptData (Confirmation Statement Reading : Type) where
  confirmation : Confirmation
  statement : Statement
  reading : Reading
  deriving DecidableEq

abbrev Receipt := ReceiptData (StageReception.Receipt (code := code)) (RequestAttestation.Statement (code := code)) (Fin code.signals)

inductive Rejection where
  | missingStatement | sourceCodeMismatch | missingDeliveryRow | localNotReady | localMismatch
  deriving DecidableEq

inductive OutcomeData (Body : Type) where
  | rejected (reason : Rejection)
  | recovered (body : Body)
  deriving DecidableEq

abbrev Outcome := OutcomeData (Receipt (code := code))

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))

def priorStatements (wire : StageTransport.Wire (code := code)) :=
  RequestAttestation.ledger vocabulary start (stages.take (wire.sendCut - start.cut))

def sourceBody (wire : StageTransport.Wire (code := code)) :=
  (priorStatements vocabulary start stages wire).find? (fun body => decide (body.ballot = wire.ballot))

def inspect (receiver : Fin code.sites) (confirmation : StageReception.Receipt (code := code)) : Outcome (code := code) :=
  match sourceBody vocabulary start stages confirmation.wire with
  | none => .rejected .missingStatement
  | some body =>
    if decode (code := code) confirmation.wire.signal ≠ some body.request then .rejected .sourceCodeMismatch
    else match (StageTrace.records start stages)[confirmation.index]? with
    | none => .rejected .missingDeliveryRow
    | some row =>
      let reading := row.after.frame.inbox receiver
      if code.memoryReady reading ≠ true then .rejected .localNotReady
      else if localRead (code := code) reading ≠ some body.request then .rejected .localMismatch
      else .recovered ⟨confirmation, body, reading⟩

structure ResultData (Reception Outcome Receipt : Type) where
  reception : Reception
  outcomes : List Outcome
  receipts : List Receipt

abbrev Result := ResultData (StageReception.Receiver (code := code)) (Outcome (code := code)) (Receipt (code := code))

def produce (receiver : Fin code.sites) (count : Nat) : Result (code := code) :=
  let reception := StageReception.run vocabulary encoding law start stages receiver count
  let outcomes := reception.receipts.map (inspect vocabulary start stages receiver)
  ⟨reception, outcomes, outcomes.filterMap fun outcome => match outcome with
    | .rejected _ => none
    | .recovered receipt => some receipt⟩

theorem inspect_binds_source_content_and_the_actual_local_record
    (receiver : Fin code.sites) (confirmation : StageReception.Receipt (code := code))
    (receipt : Receipt (code := code)) (made : inspect vocabulary start stages receiver confirmation = .recovered receipt) :
    receipt.confirmation = confirmation ∧
      receipt.statement ∈ priorStatements vocabulary start stages confirmation.wire ∧
      receipt.statement.ballot = confirmation.wire.ballot ∧
      decode (code := code) confirmation.wire.signal = some receipt.statement.request ∧
      ∃ row, (StageTrace.records start stages)[confirmation.index]? = some row ∧
        receipt.reading = row.after.frame.inbox receiver ∧ code.memoryReady receipt.reading = true ∧
        localRead (code := code) receipt.reading = some receipt.statement.request := by
  unfold inspect at made
  split at made <;> try contradiction
  rename_i body found
  split at made <;> try contradiction
  rename_i encoded
  split at made <;> try contradiction
  rename_i row actual
  dsimp only at made
  split at made <;> try contradiction
  rename_i ready
  split at made <;> try contradiction
  rename_i recovered
  cases OutcomeData.recovered.inj made
  unfold sourceBody at found
  exact ⟨rfl, List.mem_of_find?_eq_some found, of_decide_eq_true (List.find?_some
    (p := fun candidate : RequestAttestation.Statement (code := code) => decide (candidate.ballot = confirmation.wire.ballot)) found),
    by simpa only [not_not] using encoded, row, actual, rfl,
    by simpa only [not_not] using ready, by simpa only [not_not] using recovered⟩

theorem a_recovered_request_has_a_real_confirmation
    (receiver : Fin code.sites) (count : Nat) (receipt : Receipt (code := code))
    (inside : receipt ∈ (produce vocabulary encoding law start stages receiver count).receipts) :
    receipt.confirmation ∈ (StageReception.run vocabulary encoding law start stages receiver count).receipts ∧
      inspect vocabulary start stages receiver receipt.confirmation = .recovered receipt := by
  obtain ⟨outcome, included, made⟩ := List.mem_filterMap.mp inside
  cases outcome with
  | rejected reason => contradiction
  | recovered produced =>
    cases Option.some.inj made
    obtain ⟨confirmation, actual, inspected⟩ := List.mem_map.mp included
    have same := (inspect_binds_source_content_and_the_actual_local_record vocabulary start stages receiver confirmation receipt inspected).1
    exact ⟨same ▸ actual, same ▸ inspected⟩

theorem prior_statements_are_in_the_same_complete_source
    (wire : StageTransport.Wire (code := code)) (body : RequestAttestation.Statement (code := code))
    (inside : body ∈ priorStatements vocabulary start stages wire) :
    body ∈ RequestAttestation.ledger vocabulary start stages := by
  have records := StageQueue.records_append start (stages.take (wire.sendCut - start.cut))
    (stages.drop (wire.sendCut - start.cut))
  rw [List.take_append_drop] at records
  unfold RequestAttestation.ledger
  rw [records, List.flatMap_append]
  exact List.mem_append_left _ inside

theorem recovered_requests_have_paid_communication_complete_source_and_local_readback
    (receiver : Fin code.sites) (count : Nat) (receipt : Receipt (code := code))
    (inside : receipt ∈ (produce vocabulary encoding law start stages receiver count).receipts) :
    receipt.confirmation ∈ (StageReception.run vocabulary encoding law start stages receiver count).receipts ∧
      receipt.statement ∈ RequestAttestation.ledger vocabulary start stages ∧
      receipt.statement.ballot = receipt.confirmation.wire.ballot ∧
      decode (code := code) receipt.confirmation.wire.signal = some receipt.statement.request ∧
      ∃ row, (StageTrace.records start stages)[receipt.confirmation.index]? = some row ∧
        receipt.reading = row.after.frame.inbox receiver ∧ code.memoryReady receipt.reading = true ∧
        localRead (code := code) receipt.reading = some receipt.statement.request := by
  obtain ⟨confirmed, made⟩ := a_recovered_request_has_a_real_confirmation vocabulary encoding law start stages receiver count receipt inside
  obtain ⟨_, prior, ballot, encoded, localRecord⟩ :=
    inspect_binds_source_content_and_the_actual_local_record vocabulary start stages receiver receipt.confirmation receipt made
  exact ⟨confirmed, prior_statements_are_in_the_same_complete_source vocabulary start stages _ receipt.statement prior,
    ballot, encoded, localRecord⟩

theorem removing_all_actual_confirmations_removes_all_recoveries
    (receiver : Fin code.sites) (count : Nat)
    (absent : (StageReception.run vocabulary encoding law start stages receiver count).receipts = []) :
    (produce vocabulary encoding law start stages receiver count).receipts = [] := by
  simp only [produce, absent, List.map_nil, List.filterMap_nil]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadback

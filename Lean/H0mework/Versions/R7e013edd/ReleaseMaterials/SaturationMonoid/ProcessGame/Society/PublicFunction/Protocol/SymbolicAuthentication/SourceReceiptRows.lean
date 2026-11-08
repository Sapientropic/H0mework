import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageReception

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReceiptRows
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code))

def wireAt (rows : List (StageTrace.Record (code := code))) (index : Nat) : Option (StageTransport.Wire (code := code)) :=
  match rows[index]? with
  | none => none
  | some row => StageTransport.issue vocabulary encoding (rows.take index) row

def wires (rows : List (StageTrace.Record (code := code))) : List (StageTransport.Wire (code := code)) := (List.range rows.length).filterMap (wireAt vocabulary encoding rows)

theorem wireAt_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (index : Nat) :
    wireAt vocabulary encoding (StageTrace.records cursor stages) index = StageTransport.issuedAt vocabulary encoding cursor stages index := by
  unfold wireAt StageTransport.issuedAt
  dsimp only
  cases present : (StageTrace.records cursor stages)[index]? <;> rfl

theorem wires_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) :
    wires vocabulary encoding (StageTrace.records cursor stages) = StageTransport.wires vocabulary encoding cursor stages := by
  unfold wires StageTransport.wires
  rw [StageTrace.record_count]
  congr 1

def check (table : List (StageTransport.Wire (code := code))) (law : StageReception.Law code) (receiver : Fin code.sites)
    (row : StageTrace.Record (code := code)) (seen : List (Nat × Nat)) (wire : StageTransport.Wire (code := code)) : StageReception.Verdict (code := code) :=
  if StageReception.delivered row wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.sendCut < row.cursor.cut then .rejected .unauthenticated
  else if decide (wire ∈ table) ≠ true then .rejected .unauthenticated
  else if StageReception.matchingPacket row wire ≠ true then .rejected .missingPacket
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.ballot.scope ≠ law.scope receiver row.before.current then .rejected .staleScope
  else if ¬ row.cursor.cut ≤ wire.sendCut + law.maxDelay then .rejected .late
  else if ¬ ∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request then .rejected .unpaidDelivery
  else if (wire.ballot.cut,wire.ballot.position) ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (law : StageReception.Law code) (receiver : Fin code.sites)
    (row : StageTrace.Record (code := code)) (seen : List (Nat × Nat)) (wire : StageTransport.Wire (code := code)) :
    check (wires vocabulary encoding (StageTrace.records cursor stages)) law receiver row seen wire =
      StageReception.check vocabulary encoding law cursor stages receiver row seen wire := by
  simp only [check,StageReception.check,StageTransport.verify,wires_actual vocabulary encoding]
  rfl

def incoming (rows : List (StageTrace.Record (code := code))) (index : Nat) : Option (StageTransport.Wire (code := code)) :=
  match rows[index]? with
  | none => none
  | some row => match StageTransport.admission row with
    | none => none
    | some event => match event.val with
      | .deliver serial => ((List.range index).filterMap (wireAt vocabulary encoding rows)).find? (fun wire => wire.serial == serial)
      | _ => none

theorem incoming_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (index : Nat) :
    incoming vocabulary encoding (StageTrace.records cursor stages) index = StageReception.incoming vocabulary encoding cursor stages index := by
  unfold incoming StageReception.incoming
  have same : wireAt vocabulary encoding (StageTrace.records cursor stages) = StageTransport.issuedAt vocabulary encoding cursor stages :=
    funext (wireAt_actual vocabulary encoding cursor stages)
  rw [same]
  cases present : (StageTrace.records cursor stages)[index]? with
  | none => rfl
  | some row =>
    dsimp only
    cases admitted : StageTransport.admission row with
    | none => simp only
    | some event =>
      simp only
      cases kind : event.val <;> simp only

def receive (rows : List (StageTrace.Record (code := code))) (table : List (StageTransport.Wire (code := code))) (law : StageReception.Law code) (receiver : Fin code.sites)
    (index : Nat) (previous : StageReception.Receiver (code := code)) : StageReception.Receiver (code := code) :=
  match rows[index]? with
  | none => previous
  | some row =>
    let candidate := incoming vocabulary encoding rows index
    let verdict := match candidate with
      | none => AttestationReception.VerdictData.rejected .missingWire
      | some wire => check table law receiver row
          (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire
    ⟨match verdict with
      | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
      | .rejected _ => previous.receipts,
      previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩

theorem receive_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (law : StageReception.Law code) (receiver : Fin code.sites) (index : Nat) (previous : StageReception.Receiver (code := code)) :
    receive vocabulary encoding (StageTrace.records cursor stages) (wires vocabulary encoding (StageTrace.records cursor stages)) law receiver index previous =
      StageReception.receive vocabulary encoding law cursor stages receiver index previous := by
  simp only [receive,StageReception.receive,incoming_actual,check_actual]
  cases present : (StageTrace.records cursor stages)[index]? with
  | none => rfl
  | some row =>
    dsimp only
    cases candidate : StageReception.incoming vocabulary encoding cursor stages index with
    | none => simp only
    | some wire =>
      simp only
      cases verdict : StageReception.check vocabulary encoding law cursor stages receiver row
        (previous.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire <;> simp only

def run (rows : List (StageTrace.Record (code := code))) (law : StageReception.Law code) (receiver : Fin code.sites) : Nat → StageReception.Receiver (code := code) :=
  let table := wires vocabulary encoding rows
  Nat.rec ⟨[],[]⟩ fun index previous => receive vocabulary encoding rows table law receiver index previous

theorem run_actual (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (law : StageReception.Law code) (receiver : Fin code.sites) (count : Nat) :
    run vocabulary encoding (StageTrace.records cursor stages) law receiver count =
      StageReception.run vocabulary encoding law cursor stages receiver count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change receive vocabulary encoding _ _ _ _ count (run vocabulary encoding _ _ _ count) = StageReception.receive _ _ _ _ _ _ count _
    rw [ih,receive_actual vocabulary encoding]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReceiptRows

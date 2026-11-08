import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffSource
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageReception

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor old) (past : List (EventHistory.Stage (code := old))) (extra : CatalogueHandoffSource.Catalogue old)
abbrev saved := EventHistory.execute start past
abbrev code := CatalogueHandoffSource.code old extra
def resumed (_original : (saved start past).side = .original) := CatalogueHandoffSource.cursor old extra (saved start past)
variable (original : (saved start past).side = .original)

theorem the_resumed_seed_is_the_actual_saved_source :
    EventStep.seed (resumed start past extra original) =
      Extension.state old (CatalogueHandoffSource.supply old extra) (EventStep.seed (saved start past)) :=
  CatalogueHandoffSource.seed old extra _ original
variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := old))
  (law : StageReception.Law (code extra))
  (future : List (EventHistory.Stage (code := code extra))) (receiver : Fin old.sites)

-- The old send producer remains the authentication source. A new interpreter
-- may receive that message; its own stage must independently pay delivery.
abbrev candidates := StageTransport.wires vocabulary encoding start past
structure ReceptionSource where
  private mk ::
  law : StageReception.Law old
  receipts : StageReception.Receiver (code := old)
  actual : receipts = StageReception.run vocabulary encoding law start past receiver past.length

def remember (priorLaw : StageReception.Law old) : ReceptionSource start past vocabulary encoding receiver :=
  ⟨priorLaw,StageReception.run vocabulary encoding priorLaw start past receiver past.length,rfl⟩

variable (origin : ReceptionSource start past vocabulary encoding receiver)
abbrev rows := StageTrace.records (resumed start past extra original) future

def incoming (index : Nat) : Option (StageTransport.Wire (code := old)) :=
  match (rows start past extra original future)[index]? with
  | none => none
  | some row => match StageTransport.admission row with
    | none => none
    | some event => match event.val with
      | .deliver serial => (candidates start past vocabulary encoding).find? (fun wire => wire.serial == serial)
      | _ => none

def check (row : StageTrace.Record (code := code extra)) (seen : List (Nat × Nat))
    (wire : StageTransport.Wire (code := old)) : StageReception.Verdict (code := old) :=
  if StageReception.delivered row wire.serial ≠ true then .rejected .missingDelivery
  else if ¬ wire.sendCut < row.cursor.cut then .rejected .unauthenticated
  else if StageTransport.verify vocabulary encoding start past wire ≠ true then .rejected .unauthenticated
  else if StageReception.matchingPacket row wire ≠ true then .rejected .missingPacket
  else if wire.recipient ≠ receiver then .rejected .wrongRecipient
  else if wire.ballot.scope ≠ law.scope receiver row.before.current then .rejected .staleScope
  else if ¬ row.cursor.cut ≤ wire.sendCut + law.maxDelay then .rejected .late
  else if ¬ ∀ item ∈ StageTrace.items row, (code extra).law.Valid item.before item.request then .rejected .unpaidDelivery
  else if (wire.ballot.cut,wire.ballot.position) ∈ seen then .rejected .duplicate
  else .accepted wire

theorem check_sound (row : StageTrace.Record (code := code extra)) (seen : List (Nat × Nat))
    (wire result : StageTransport.Wire (code := old))
    (accepted : check start past extra vocabulary encoding law receiver row seen wire = .accepted result) :
    result = wire ∧ StageReception.delivered row wire.serial = true ∧ wire.sendCut < row.cursor.cut ∧
      StageTransport.verify vocabulary encoding start past wire = true ∧
      StageReception.matchingPacket row wire = true ∧ wire.recipient = receiver ∧
      wire.ballot.scope = law.scope receiver row.before.current ∧
      row.cursor.cut ≤ wire.sendCut + law.maxDelay ∧
      (∀ item ∈ StageTrace.items row, (code extra).law.Valid item.before item.request) ∧
      (wire.ballot.cut,wire.ballot.position) ∉ seen := by
  unfold check at accepted
  split_ifs at accepted; simp_all

def receive (index : Nat) (previous : StageReception.Receiver (code := old)) : StageReception.Receiver (code := old) :=
  match (rows start past extra original future)[index]? with
  | none => previous
  | some row =>
    let candidate := incoming start past extra original vocabulary encoding future index
    let seen := (origin.receipts.receipts ++ previous.receipts).map
      (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))
    let verdict := match candidate with
      | none => AttestationReception.VerdictData.rejected .missingWire
      | some wire => check start past extra vocabulary encoding law receiver row seen wire
    ⟨match verdict with
      | .accepted wire => previous.receipts ++ [⟨wire,index,row.cursor.cut⟩]
      | .rejected _ => previous.receipts,
      previous.audit ++ [(row.cursor.cut,candidate,verdict)]⟩

def run : Nat → StageReception.Receiver (code := old) :=
  Nat.rec ⟨[],[]⟩ fun n previous =>
    receive start past extra original vocabulary encoding law future receiver origin n previous

theorem receipt_has_two_actual_source_origins (count : Nat) (receipt : StageReception.Receipt (code := old))
    (inside : receipt ∈ (run start past extra original vocabulary encoding law future receiver origin count).receipts) :
    StageTransport.verify vocabulary encoding start past receipt.wire = true ∧
      ∃ row ∈ rows start past extra original future,
        StageReception.delivered row receipt.wire.serial = true ∧
        StageReception.matchingPacket row receipt.wire = true ∧
        row.cursor.cut = receipt.delivery ∧
        row.cursor.cut ≤ receipt.wire.sendCut + law.maxDelay ∧
        (∀ item ∈ StageTrace.items row, (code extra).law.Valid item.before item.request) ∧
        (receipt.wire.ballot.cut,receipt.wire.ballot.position) ∉
          origin.receipts.receipts.map
            (fun prior => (prior.wire.ballot.cut,prior.wire.ballot.position)) := by
  induction count with
  | zero => simp [run] at inside
  | succ n ih =>
    change receipt ∈ (receive start past extra original vocabulary encoding law future receiver origin n
      (run start past extra original vocabulary encoding law future receiver origin n)).receipts at inside
    let before := run start past extra original vocabulary encoding law future receiver origin n
    let seen := (origin.receipts.receipts ++ before.receipts).map
      (fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position))
    cases actual : (rows start past extra original future)[n]? with
    | none => exact ih (by simpa only [receive,actual] using inside)
    | some row =>
      cases incoming : CatalogueHandoffConsumer.incoming start past extra original vocabulary encoding future n with
      | none => exact ih (by simpa only [receive,actual,incoming] using inside)
      | some wire =>
        cases accepted : check start past extra vocabulary encoding law receiver row seen wire with
        | rejected reason =>
          dsimp only [seen,before] at accepted
          exact ih (by simpa only [receive,actual,incoming,accepted,before] using inside)
        | accepted body =>
          dsimp only [seen,before] at accepted
          have present : receipt ∈ before.receipts ++ [⟨body,n,row.cursor.cut⟩] := by
            simpa only [receive,actual,incoming,accepted,before] using inside
          rcases List.mem_append.mp present with previous | freshReceipt
          · exact ih previous
          · have eq := List.mem_singleton.mp freshReceipt
            subst receipt
            have sound := check_sound start past extra vocabulary encoding law receiver row seen wire body accepted
            rcases sound with ⟨rfl,delivered,_,auth,matched,_,_,delay,paid,fresh⟩
            refine ⟨auth,row,List.mem_of_getElem? actual,delivered,matched,rfl,delay,paid,?_⟩
            intro oldReceipt
            exact fresh (by simp only [seen,List.map_append,List.mem_append];exact Or.inl oldReceipt)

theorem receipt_consumes_the_new_native_delivery (count : Nat) (receipt : StageReception.Receipt (code := old))
    (inside : receipt ∈ (run start past extra original vocabulary encoding law future receiver origin count).receipts) :
    StageTransport.verify vocabulary encoding start past receipt.wire = true ∧
      ∃ row ∈ StageTrace.records (resumed start past extra original) future,
        row.submitted = (code extra).deliveryCost receipt.wire.recipient ∧
        (∀ item ∈ StageTrace.items row, (code extra).law.Valid item.before item.request) ∧
        (Financial.inventoryAt (EventHistory.execute (resumed start past extra original) future).source.input
          (ProgrammeHistory.visitAt (EventHistory.execute (resumed start past extra original) future).source.input
            (EventStep.boundary row.cursor))).filterMap
          (Financial.InstructionOrigin.instruction? (EventHistory.execute (resumed start past extra original) future).source.input) =
            StageTrace.items row := by
  obtain ⟨auth,row,member,delivered,matched,_,_,paid,_⟩ :=
    receipt_has_two_actual_source_origins start past extra original vocabulary encoding law future receiver origin count receipt inside
  obtain ⟨packet,present,_,recipient,_,_⟩ := StageReception.matched_packet_is_actual row receipt.wire matched
  refine ⟨auth,row,member,?_,paid,StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ member⟩
  rw [StageReception.actual_delivery_submits_the_original_cost _ _ row member _ packet present delivered,recipient]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffConsumer

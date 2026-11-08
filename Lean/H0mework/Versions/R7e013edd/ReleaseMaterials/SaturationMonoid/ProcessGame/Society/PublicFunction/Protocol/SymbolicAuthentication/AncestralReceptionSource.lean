import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRetryProgress
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CatalogueHandoffConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AncestralReceptionSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
abbrev Emitter := Code Party Good Port (Mandate.State Party Technology) Instrument
variable (root : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

abbrev code := CatalogueHandoffSource.code root

def join (earlier : CatalogueHandoffSource.Catalogue root)
    (later : CatalogueHandoffSource.Catalogue (code root earlier)) : CatalogueHandoffSource.Catalogue root :=
  ⟨earlier.actions ++ later.actions,max earlier.actionLimit later.actionLimit,
    earlier.histories ++ later.histories,max earlier.historyLimit later.historyLimit,earlier.events ++ later.events⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem joined_code_is_the_same_actual_extension (earlier : CatalogueHandoffSource.Catalogue root)
    (later : CatalogueHandoffSource.Catalogue (code root earlier)) :
    CatalogueHandoffSource.code (code root earlier) later = code root (join root earlier later) := by
  simp only [code,CatalogueHandoffSource.code,CatalogueHandoffSource.supply,Extension.code,join,
    Nat.max_zero,List.append_assoc,Nat.max_assoc]

def recode {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : Cursor right := same ▸ cursor

theorem recode_input {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (recode same cursor).source.input = cursor.source.input := by
  cases same
  rfl

theorem recode_current {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (EventStep.seed (recode same cursor)).current = (EventStep.seed cursor).current := by
  cases same
  rfl

theorem recode_remaining {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (EventStep.seed (recode same cursor)).remaining = (EventStep.seed cursor).remaining := by
  cases same
  rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem recode_side {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (recode same cursor).side = cursor.side := by cases same;rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem recode_cut {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (recode same cursor).cut = cursor.cut := by cases same;rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem recode_owner {left right : Emitter (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (same : left = right) (cursor : Cursor left) : (recode same cursor).ownerStart = cursor.ownerStart := by cases same;rfl

inductive Position where
  | original (index : Nat)
  | successor (step : Nat)
  deriving DecidableEq

structure ReceiptData (Body : Type) where
  wire : Body
  position : Position
  delivery : Nat
  deriving DecidableEq

structure ReceiverData (Body : Type) where
  receipts : List (ReceiptData Body)
  audit : List (Nat × Option Body × AttestationReception.VerdictData Body)
  deriving DecidableEq

abbrev Receipt := ReceiptData (StageTransport.Wire (code := root))
abbrev Receiver := ReceiverData (StageTransport.Wire (code := root))

def remember (prior : StageReception.Receipt (code := root)) : Receipt root :=
  ⟨prior.wire,.original prior.index,prior.delivery⟩

structure State where
  private mk ::
  catalogue : CatalogueHandoffSource.Catalogue root
  cursor : Cursor (code root catalogue)
  original : cursor.side = .original
  receiver : Receiver root
  reception : StageReception.Law root
  steps : Nat

variable (start : Cursor root) (past : List (EventHistory.Stage (code := root)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := root))
  (priorLaw : StageReception.Law root) (recipient : Fin root.sites)

abbrev saved := EventHistory.execute start past

def initial (catalogue : CatalogueHandoffSource.Catalogue root)
    (original : (saved root start past).side = .original) : State root :=
  ⟨catalogue,CatalogueHandoffSource.cursor root catalogue (saved root start past),original,
    let prior := StageReception.run vocabulary encoding priorLaw start past recipient past.length
    ⟨prior.receipts.map (remember root),prior.audit⟩,priorLaw,0⟩

structure Command (state : State root) where
  addition : CatalogueHandoffSource.Catalogue (code root state.catalogue)
  protocol : Rule (code root (join root state.catalogue addition))
  rival : Opponent (code root (join root state.catalogue addition))

def migrated (state : State root) (command : Command root state) :=
  recode (joined_code_is_the_same_actual_extension root state.catalogue command.addition)
    (CatalogueHandoffSource.cursor (code root state.catalogue) command.addition state.cursor)

abbrev row (state : State root) (command : Command root state) :=
  StageTrace.material (migrated root state command) command.protocol command.rival

def incoming (state : State root) (command : Command root state) : Option (StageTransport.Wire (code := root)) :=
  match StageTransport.admission (row root state command) with
  | none => none
  | some event => match event.val with
    | .deliver serial => (StageTransport.wires vocabulary encoding start past).find? (fun wire => wire.serial == serial)
    | _ => none

def verdict (state : State root) (command : Command root state) : StageReception.Verdict (code := root) :=
  match incoming root start past vocabulary encoding state command with
  | none => .rejected .missingWire
  | some wire => CatalogueHandoffConsumer.check start past (join root state.catalogue command.addition)
      vocabulary encoding ⟨state.reception.scope,state.reception.maxDelay⟩ recipient (row root state command)
      (state.receiver.receipts.map fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)) wire

def next (state : State root) (command : Command root state) : State root :=
  let actual := row root state command
  let outcome := verdict root start past vocabulary encoding recipient state command
  let cursor := (migrated root state command).after command.protocol command.rival
  let original : cursor.side = .original :=
    (recode_side _ _).trans state.original
  ⟨join root state.catalogue command.addition,cursor,original,
    ⟨match outcome with
      | .accepted wire => state.receiver.receipts ++ [⟨wire,.successor state.steps,actual.cursor.cut⟩]
      | .rejected _ => state.receiver.receipts,
      state.receiver.audit ++ [(actual.cursor.cut,incoming root start past vocabulary encoding state command,outcome)]⟩,
    state.reception,state.steps + 1⟩

abbrev Controller := (state : State root) → Command root state

def run (begin : State root) (control : Controller root) : Nat → State root :=
  Nat.rec begin fun _ state => next root start past vocabulary encoding recipient state (control state)

theorem run_zero (begin : State root) (control : Controller root) :
    run root start past vocabulary encoding recipient begin control 0 = begin := rfl

theorem run_succ (begin : State root) (control : Controller root) (count : Nat) :
    run root start past vocabulary encoding recipient begin control (count+1) =
      next root start past vocabulary encoding recipient
        (run root start past vocabulary encoding recipient begin control count)
        (control (run root start past vocabulary encoding recipient begin control count)) := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AncestralReceptionSource

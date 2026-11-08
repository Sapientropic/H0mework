import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.History
set_option autoImplicit false
set_option maxRecDepth 100000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Wire
open Lean Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def origin : String := "provider-material-3/native-export-6/v1"
-- Public receipt exposes the delivered good and source clock, not unrelated inventories or claims.
def sourceJson (current : ProviderCurrent) : Json := Json.mkObj [
  ("available",toJson (toString (current.stock 1 .feedstock))),
  ("clock",toJson (toString current.clock)),("round",toJson current.round)]

def sourceFlow (entries : Flow ProviderParty ProviderGood) : Json := toJson (entries.map fun ((actor,good),amount) =>
  Json.arr #[toJson ("source:"++toString actor.val),toJson (Supply.Privacy.Wire.goodName (material good)),toJson (toString amount)])

def viewJson (view : Packet.View) : Json := Json.mkObj [
  ("available",toJson (toString view.available)),("clock",toJson (toString view.clock)),("round",toJson view.round)]
def sourceActor (actor : ProviderParty) : Json := toJson ("source:"++toString actor.val)
def sourcePort : ProviderPort → Json
  | .reserve owner => Json.mkObj [("kind",toJson "source"),("base",toJson "reserve"),("owner",toJson owner.val)]
  | .service => Json.mkObj [("kind",toJson "source"),("base",toJson "service")]
  | .challenge => Json.mkObj [("kind",toJson "source"),("base",toJson "challenge")]
def sourceAction (action : ProviderAction) : Json :=
  let operation:=match action.operation with
    | .use actor bundle purpose => Json.mkObj [("kind",toJson "use"),("actor",sourceActor actor),
        ("bundle",toJson (bundle.map fun (good,quantity) => Json.arr #[toJson (Supply.Privacy.Wire.goodName (material good)),toJson (toString quantity)])),
        ("purpose",toJson (Supply.Privacy.Wire.useName purpose))]
    | _ => Json.mkObj [("kind",toJson "unexpected-source-operation")]
  Json.mkObj [("signer",sourceActor action.signer),("consents",toJson (action.consents.map sourceActor)),
    ("purpose",sourcePort action.purpose),("gates",toJson (action.gates.map sourcePort)),("operation",operation)]
def sourceRows : Json := toJson (Packet.rows.map fun row => Json.mkObj [
  ("cut",toJson row.cut),("before",viewJson row.before),("next",viewJson row.after),
  ("remainingBefore",toJson row.remainingBefore),("remainingAfter",toJson row.remainingAfter),
  ("submitted",toJson (row.submitted.map sourceAction)),
  ("items",toJson (row.items.map fun item => Json.mkObj [
    ("index",toJson item.index),("request",sourceAction item.request),
    ("accepted",toJson item.accepted),("debit",sourceFlow item.debit),("credit",sourceFlow item.credit)]))])


def account {plan : Plan} (state : Consume.State plan) : Json := Json.mkObj [
  ("slots",toJson state.service.account.current.slots.length),
  ("outstanding",toJson (toString (Financial.Family.ledgerClaims Finance.sources state.service.account.current .delivery supplier receiver)))]

def eventOfJson (command : Json) : Except String Consume.Event := do
  match (command.getObjValAs? String "kind").toOption with
  | some "arrival" => return .arrival (←command.getObjValAs? Nat "quantity")
  | _ => return .service (Productive.Wire.commandOfJson command)

def advance {plan : Plan} (state : Consume.State plan) (command : Json) : Consume.State plan :=
  match eventOfJson command with | .error _ => state | .ok event => Consume.step state event

def render {plan : Plan} (state : Consume.State plan) (command : Json) : Json := Id.run do
  let next:=advance state command
  let mut status:="ERROR"
  let mut service:=Json.null
  let mut consumed:=false
  match eventOfJson command with
  | .error message => service:=Json.mkObj [("status",toJson "ERROR"),("message",toJson message),("metadata",command)]
  | .ok (.arrival quantity) =>
    consumed:=!state.spent && decide ((quantity:ℚ)=Effect.quantity)
    status:=if consumed then "ARRIVED" else "BLOCKED"
  | .ok (.service parsed) =>
    service:=Productive.Wire.render parsed (Productive.answer state.service parsed)
    status:=(service.getObjValAs? String "status").toOption.getD "ERROR"
  let opening:=(service.getObjValAs? Bool "opening").toOption.getD false
  return Json.mkObj [("source_root",toJson origin),("metadata",command),("status",toJson status),
    ("before",Supply.Privacy.Wire.stateJson state.service.session.current),
    ("next",Supply.Privacy.Wire.stateJson next.service.session.current),
    ("scope",Supply.Privacy.Wire.scopeJson state.service.session.window.scope),
    ("nextScope",Supply.Privacy.Wire.scopeJson next.service.session.window.scope),
    ("opening",toJson opening),("source",sourceJson (Consume.sourceCurrent state)),
    ("sourceNext",sourceJson (Consume.sourceCurrent next)),("sourceRows",if consumed then sourceRows else Json.arr #[]),
    ("debit",if consumed then Json.arr #[Json.arr #[toJson "source:1",toJson "feed",toJson "3"]] else Json.arr #[]),
    ("credit",if consumed then Json.arr #[Json.arr #[toJson "audit:0",toJson "feed",toJson "3"]] else Json.arr #[]),
    ("spent",toJson next.spent),("account",account next),("service",service)]

structure Execution (larger : Bool) where
  input : EnergyRenewal.Privacy.SourceInput
  state : Consume.State (input.plan larger)
  output : List Json

def execute (larger : Bool) (request : Json) : Except String (Execution larger) := do
  let source ←request.getObjVal? "source"
  let commands ←request.getObjValAs? (Array Json) "events"
  let first ←History.restore larger source []
  let mut state:=first.state
  let mut output:=[]
  for command in commands do
    output:=output++[render state command]
    state:=advance state command
  return ⟨first.input,state,output⟩

def actual (larger : Bool) (request : Json) : Except String Json := do
  let execution ←execute larger request
  match execution.output.getLast? with
  | none => throw "ARRIVAL_EVENT_REQUIRED"
  | some reply => return reply

def publicReadout (request : Json) : Except String Json := actual false request

theorem actual_output_is_from_the_complete_word (larger : Bool) (request : Json) :
    actual larger request=(execute larger request).bind (fun execution =>
      match execution.output.getLast? with | none => .error "ARRIVAL_EVENT_REQUIRED" | some reply => .ok reply) := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Wire

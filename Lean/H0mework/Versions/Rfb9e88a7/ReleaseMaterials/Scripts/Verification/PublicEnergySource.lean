import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Runtime
import Lean.Data.Json

set_option autoImplicit false
set_option maxRecDepth 65536

open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
open SaturationMonoid.ProcessGame.Society.PublicFunction
open Audit.Scoped
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
namespace EnergyExport
def queryJson (query : Query) : Json := Json.mkObj [("slots",toJson query.slots.val),("fields",toJson query.fields.val)]
def evidenceJson (slot : Slot) (evidence : Evidence) : Json :=
  Json.mkObj [("slot",toJson slot.val),
    ("admission",match evidence.admission with
      | none => .null
      | some event => Json.mkObj [("slot",toJson event.slot),("ordinal",toJson event.ordinal)]),
    ("payment",match evidence.payment with
      | none => .null
      | some event => Json.mkObj [("slot",toJson event.slot),("visit",toJson event.visit),("row",toJson event.row),
        ("available",toJson (toString event.available)),("start",toJson (toString event.start)),("finish",toJson (toString event.finish))])]

def accessName : Access → String
  | .admitted => "admitted" | .unauthorized => "unauthorized" | .expired => "expired" | .unfunded => "unfunded"

def recordJson (record : Record) : Json :=
  Json.mkObj [("cut",toJson record.cut),("actor",toJson record.actor),("query",queryJson record.query),
    ("access",toJson (accessName record.access)),("version",toJson record.version),
    ("clock",toJson (toString record.clock)),("labor",toJson (toString record.laborCost)),
    ("evidence",toJson (record.evidence.map (fun (slot,evidence) => evidenceJson slot evidence)))]


def ratOfJson (value : Json) : Except String ℚ := do
  let value ← value.getStr?
  match value.splitOn "/" with
  | [n] =>
    let some n := n.trimAscii.toString.toInt? | throw "RATIONAL"
    return n
  | [n,d] =>
    let some n := n.trimAscii.toString.toInt? | throw "RATIONAL"
    let some d := d.trimAscii.toString.toNat? | throw "RATIONAL"
    if d = 0 then throw "RATIONAL_ZERO_DENOMINATOR"
    return (n : ℚ) / d
  | _ => throw "RATIONAL"

def queryOfJson (value : Json) : Except String Query := do
  let mask ← value.getObjValAs? Nat "slots"
  let fields ← value.getObjValAs? Nat "fields"
  if hm : mask < 64 then
    if hf : fields < 4 then return ⟨⟨mask,hm⟩,⟨fields,hf⟩⟩
    else throw "FIELD_MASK"
  else throw "SLOT_MASK"

def optional {α : Type} (value : Json) (parse : Json → Except String α) : Except String (Option α) :=
  match value with
  | .null => .ok none
  | _ => some <$> parse value

def recordOfJson (value : Json) : Except String Record := do
  let access : Access ← match ← value.getObjValAs? String "access" with
    | "admitted" => pure .admitted | "unauthorized" => pure .unauthorized
    | "expired" => pure .expired | "unfunded" => pure .unfunded | _ => throw "ACCESS"
  let evidence ← (← value.getObjValAs? (Array Json) "evidence").toList.mapM fun entry => do
    let index ← entry.getObjValAs? Nat "slot"
    if h : index < 6 then
      let admission ← optional (← entry.getObjVal? "admission") fun item => do
        return (⟨← item.getObjValAs? Nat "slot",← item.getObjValAs? Nat "ordinal"⟩ : Admission)
      let payment ← optional (← entry.getObjVal? "payment") fun item => do
        return (⟨← item.getObjValAs? Nat "slot",← item.getObjValAs? Nat "visit",← item.getObjValAs? Nat "row",
          ← ratOfJson (← item.getObjVal? "available"),← ratOfJson (← item.getObjVal? "start"),
          ← ratOfJson (← item.getObjVal? "finish")⟩ : Payment)
      return ((⟨index,h⟩ : Slot),(⟨admission,payment⟩ : Evidence))
    else throw "SLOT"
  return ⟨← value.getObjValAs? Nat "cut",← value.getObjValAs? Nat "actor",← queryOfJson (← value.getObjVal? "query"),
    access,← value.getObjValAs? Nat "version",← ratOfJson (← value.getObjVal? "clock"),
    ← ratOfJson (← value.getObjVal? "labor"),evidence⟩

def kind : Operation Party Good (Mandate.State Party Technology) Unit → String
  | .present => "submission" | .transfer .. => "transfer" | .use .. => "use"
  | .revise _ target => match target.last with
    | some .revoke => "revoke" | some (.propose _) => "propose" | some .accept => "accept" | _ => "revision"
  | _ => "other"

def snapshot (current : AuditCurrent) : Json := Json.mkObj
  [("clock",toJson (toString current.clock)),("round",toJson current.round),
   ("holder",toJson current.technology.holder),("offered",toJson current.technology.offered),
   ("version",toJson current.technology.version),
   ("energy",toJson ((List.range 4).map fun actor => toString (current.stock actor .energy))),
   ("labor",toJson ((List.range 4).map fun actor => toString (current.stock actor .labor)))]

def rowJson (law : RawLaw Party Good AuditPort (Mandate.State Party Technology) Unit)
    (item : ExecutionItem Party Good AuditPort (Mandate.State Party Technology) Unit) : Json :=
  Json.mkObj [("index",toJson item.index),("signer",toJson item.request.signer),
    ("kind",toJson (kind item.request.operation)),("accepted",toJson (decide (law.Valid item.before item.request))),
    ("energyDebit",toJson ((List.range 4).map fun actor => toString (flowAt (law.actualDebit item.before item.request) actor .energy))),
    ("energyCredit",toJson ((List.range 4).map fun actor => toString (flowAt (law.actualCredit item.before item.request) actor .energy)))]

def execute (request : Json) : Except String Json := do
  let cut ← request.getObjValAs? Nat "cut"
  if cut = 0 then throw "SOURCE_ORDER"
  let history ← (← request.getObjValAs? (Array Json) "history").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← queryOfJson (← item.getObjVal? "query"))
  let queries := fun ordinal => ((history.find? fun item => item.1 = ordinal).map Prod.snd).getD (defaultQuery ordinal)
  let births ← (← request.getObjValAs? (Array Json) "births").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← item.getObjValAs? String "key")
  let replyInputs ← (← request.getObjValAs? (Array Json) "replies").toList.mapM fun item => do
    let observed ← item.getObjValAs? Nat "observedCut"
    let atCut ← item.getObjValAs? Nat "cut"
    if observed ≥ atCut ∨ atCut ≥ cut then throw "REPLY_ORDER"
    return (atCut,observed,← item.getObjValAs? Nat "challenger",← optional (← item.getObjVal? "alleged") recordOfJson)
  let replies : Governance.Replies := replyInputs.foldl (fun past (atCut,observed,challenger,alleged) =>
    past ++ [(atCut,⟨challenger,observed,(Governance.current queries false births past atCut).technology,alleged⟩)]) []
  let candidate ← request.getObjValAs? Nat "candidate"
  let plan : EnergyRenewal.Plan := ⟨queries,false,births,replies,cut,candidate⟩
  let before := EnergyRenewal.before plan
  let actions := EnergyRenewal.actions plan
  let supplyAfter := EnergyRenewal.after plan
  let supply := Json.mkObj [("before",snapshot before),("next",snapshot supplyAfter),
    ("rows",toJson ((auditLaw.rawItems before actions).map (rowJson auditLaw)))]
  let supplied := EnergyRenewal.Runtime.nextEpoch plan
  match supplied with
  | none =>
    let code := if ¬ EnergyRenewal.Eligible plan then "INELIGIBLE" else
      if ¬ EnergyRenewal.Quiet before then "ACTIVE_MANDATE" else "UNPAID_SUPPLY"
    return Json.mkObj [("ready",toJson false),("reason",toJson code),("supply",supply)]
  | some seed =>
    let ready := seed.ready
    let requests ← (← request.getObjValAs? (Array Json) "queries").toList.mapM fun item => do
      return (← item.getObjValAs? Nat "ordinal",← queryOfJson (← item.getObjVal? "query"))
    let requestsAt := fun ordinal => ((requests.find? fun item => item.1 = ordinal).map Prod.snd).getD (defaultQuery ordinal)
    let ordinal ← request.getObjValAs? Nat "ordinal"
    if ordinal = 0 then throw "EPOCH_ORDER"
    let result := seed.consume requestsAt ordinal
    let before := ready.epochCurrent requestsAt ordinal
    let word := ready.epochWord requestsAt before
    let after := ready.epochCurrent requestsAt (ordinal+1)
    let packets := result.packets.map fun delivery => Json.mkObj
      [("index",toJson delivery.access.val.index),("actor",toJson candidate),
       ("query",queryJson (requestsAt ordinal)),("unit",toJson ("energy" : String)),
       ("accessEnergy",toJson ("1" : String)),("deliveryEnergy",toJson ("1" : String)),
       ("clock",toJson (toString delivery.access.val.before.clock)),
       ("version",toJson delivery.access.val.before.technology.version),
       ("evidence",toJson (delivery.evidence.map fun (slot,evidence) => evidenceJson slot evidence))]
    let stages := (List.range (ordinal+1)).map fun visit =>
      let before := ready.epochCurrent requestsAt visit
      let actions := if visit = 0 then [] else ready.epochWord requestsAt before
      Json.mkObj [("ordinal",toJson visit),("before",snapshot before),
        ("rows",toJson ((ready.law.rawItems before actions).map (rowJson ready.law))),
        ("next",snapshot (ready.epochCurrent requestsAt (visit+1)))]
    return Json.mkObj [("ready",toJson true),("supply",supply),
      ("scope",Json.mkObj [("unit",toJson ("energy" : String)),("earliest",toJson (toString ready.task.earliest)),
        ("deadline",toJson (toString ready.task.deadline)),("slots",toJson ready.task.slots.length),
        ("revisionEnergy",toJson ("1" : String)),("oldDeadline",toJson (toString auditTask.deadline))]),
      ("epoch",Json.mkObj [("ordinal",toJson ordinal),("before",snapshot before),
        ("rows",toJson ((ready.law.rawItems before word).map (rowJson ready.law))),
        ("packets",toJson packets),("next",snapshot after)]),
      ("stages",toJson stages),("nextCut",toJson (cut+ordinal+2))]

end EnergyExport

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= EnergyExport.execute
    stdout.putStrLn ((match result with | .ok value => value | .error message => Json.mkObj [("error",toJson message)]).compress)
    stdout.flush

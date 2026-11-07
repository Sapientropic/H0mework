import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Governance.Runtime
import Lean.Data.Json

set_option autoImplicit false
set_option maxRecDepth 65536

open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
open SaturationMonoid.ProcessGame.Society.PublicFunction
open Audit.Scoped
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
namespace GovernanceExport
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

def execute (request : Json) : Except String Json := do
  let cut ← request.getObjValAs? Nat "cut"
  if cut = 0 then throw "SOURCE_ORDER"
  let history ← (← request.getObjValAs? (Array Json) "history").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← queryOfJson (← item.getObjVal? "query"))
  let queries := fun ordinal => ((history.find? fun item => item.1 = ordinal).map Prod.snd).getD (defaultQuery ordinal)
  let oldBirths ← (← request.getObjValAs? (Array Json) "births").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← item.getObjValAs? String "key")
  let operation ← request.getObjValAs? String "op"
  let key ← request.getObjValAs? String "key"
  let births := oldBirths ++ [(cut,key)]
  let replies ← if operation = "response" then do
      let observed ← request.getObjValAs? Nat "observedCut"
      if observed ≥ cut then throw "SOURCE_ORDER"
      let alleged ← optional (← request.getObjVal? "alleged") recordOfJson
      let challenger ← request.getObjValAs? Nat "challenger"
      let before := Governance.current queries false births [] cut
      pure [(cut,(⟨challenger,observed,before.technology,alleged⟩ : Response.Objection))]
    else if operation = "registration" then pure [] else throw "OPERATION"
  let facade := Governance.Runtime.facade queries false births replies
  let state := Governance.Runtime.activated queries false births replies cut
  let payload : Governance.Runtime.Result queries false births replies cut := match facade.readoutAt state .governance with
    | .inl ⟨_,payload⟩ => payload cut (by
      change (SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt
        (Governance.input queries false births replies) state.state).current = _
      rw [Governance.Runtime.activated_state])
    | .inr impossible => nomatch impossible
  let before := Governance.Runtime.beforeAt queries false births replies cut
  let actions := Governance.Runtime.wordAt queries false births replies cut
  let after := Governance.Runtime.beforeAt queries false births replies (cut+1)
  let roles := (payload.roles key).map fun role => Json.mkObj
    [("index",toJson role.item.val.index),("principal",toJson (toString (Governance.principal key))),
     ("role",toJson ("executor" : String)),("holder",toJson role.item.val.before.technology.holder)]
  let rows := (auditLaw.rawItems before actions).map fun item => Json.mkObj
    [("index",toJson item.index),("signer",toJson (toString item.request.signer)),
     ("kind",toJson (kind item.request.operation)),("accepted",toJson (decide (auditLaw.Valid item.before item.request)))]
  return Json.mkObj [("cut",toJson cut),("key",toJson key),("roles",toJson roles),("rows",toJson rows),
    ("labor",toJson (toString (actualNetLabor before actions))),
    ("failures",toJson (payload.rejected.map fun failure => Json.mkObj
      [("index",toJson failure.item.val.index),("kind",toJson (kind failure.item.val.request.operation)),
       ("gap",toJson (toString (Response.laborGap failure failure.item.val.request.signer))),
       ("expired",toJson (decide (auditTask.deadline < failure.item.val.before.clock)))])),
    ("before",Json.mkObj [("holder",toJson before.technology.holder),("version",toJson before.technology.version),("clock",toJson (toString before.clock))]),
    ("next",Json.mkObj [("cut",toJson (cut+1)),("holder",toJson after.technology.holder),("version",toJson after.technology.version),("clock",toJson (toString after.clock))])]

end GovernanceExport

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= GovernanceExport.execute
    stdout.putStrLn ((match result with | .ok value => value | .error message => Json.mkObj [("error",toJson message)]).compress)
    stdout.flush

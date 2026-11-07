import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime
import Lean.Data.Json

set_option autoImplicit false
set_option maxRecDepth 65536

open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
open Audit.Scoped

private instance : Inhabited Query := ⟨⟨0,0⟩⟩

def liveResult (queries : Nat → Query) (larger : Bool) (cut : Nat) : Runtime.Result queries larger cut :=
  match (Runtime.facade queries larger).readoutAt (Runtime.activated queries larger cut) .audit with
  | .inl ⟨_,payload⟩ => payload cut (by
      change (SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt (input queries larger)
        (Runtime.activated queries larger cut).state).current = _
      rw [Runtime.activated_state])
  | .inr impossible => nomatch impossible

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

def queriesFrom (inputs : List (Nat × Query)) (cut : Nat) : Query :=
  ((inputs.find? (fun item => item.1 = cut)).map Prod.snd).getD (defaultQuery cut)

def inspect (larger : Bool) (inputs : List (Nat × Query)) (start : Nat) : Nat := Id.run do
  let mut cut := start
  for _ in List.range 10 do
    if !(recordsAt (queriesFrom inputs) larger cut).isEmpty then return cut
    cut := cut + 1
  return cut

def queryOfJson (value : Json) : Except String Query := do
  let mask ← value.getObjValAs? Nat "slots"
  let fields ← value.getObjValAs? Nat "fields"
  if hm : mask < 64 then
    if hf : fields < 4 then return ⟨⟨mask,hm⟩,⟨fields,hf⟩⟩
    else throw "FIELD_MASK"
  else throw "SLOT_MASK"

def backend (larger : Bool) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut cut := 0
  let mut inputs : List (Nat × Query) := []
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result : Except String Json := do
      let request ← Json.parse line
      let operation ← request.getObjValAs? String "op"
      if operation = "inspect" then
        let chosen := inspect larger inputs cut
        let state := fastCurrent (queriesFrom inputs) larger chosen
        let some read := (liveResult (queriesFrom inputs) larger chosen).records.head? | throw "NO_SOURCE_REQUEST"
        return Json.mkObj [("cut",toJson chosen),("actor",toJson read.actor),("version",toJson state.technology.version),
          ("clock",toJson (toString state.clock))]
      else
        if operation ≠ "advance" ∧ operation ≠ "preview" then throw "OPERATION"
        let chosen ← request.getObjValAs? Nat "cut"
        if chosen ≠ inspect larger inputs cut then throw "SOURCE_CUT"
        let query ← queryOfJson (← request.getObjVal? "query")
        let nextInputs := inputs ++ [(chosen,query)]
        let some record := (liveResult (queriesFrom nextInputs) larger chosen).records.head? | throw "NO_SOURCE_REQUEST"
        return recordJson record
    match result with
    | .error error => stdout.putStrLn ((Json.mkObj [("error",toJson error)]).compress)
    | .ok response =>
      let request := (Json.parse line).toOption.get!
      if (request.getObjValAs? String "op").toOption = some "advance" then
        let chosen := (request.getObjValAs? Nat "cut").toOption.get!
        let query := (queryOfJson ((request.getObjVal? "query").toOption.get!)).toOption.get!
        inputs := inputs ++ [(chosen,query)]
        cut := chosen + 1
      stdout.putStrLn response.compress
    stdout.flush

def main (arguments : List String) : IO Unit := do
  backend (arguments.head? = some "private-two")

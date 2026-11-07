import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire
open Lean
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Continuation

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

def requestOfJson (value : Json) : Except String EnergyRenewal.Continuation.Request := do
  let command ← match ← value.getObjValAs? String "op" with
    | "read" => pure Command.read | "repair" => pure Command.repair
    | "revoke" => pure Command.revoke | "open" => pure Command.openWindow
    | "grant" => pure Command.grant | _ => throw "CONTINUATION_OPERATION"
  return ⟨command,← queryOfJson (← value.getObjVal? "query")⟩

/-- Only public decoder inputs cross this boundary. Private worlds remain in their source histories. -/
def decode (request : Json) : Except String SourceInput := do
  let mode ← request.getObjValAs? String "mode"
  if mode ≠ "continuation" ∧ mode ≠ "handoff" then throw "WIRE_MODE"
  let cut ← request.getObjValAs? Nat "cut"
  if cut = 0 then throw "SOURCE_ORDER"
  let history ← (← request.getObjValAs? (Array Json) "history").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← queryOfJson (← item.getObjVal? "query"))
  let queries := fun ordinal => ((history.find? fun item => item.1 = ordinal).map Prod.snd).getD (defaultQuery ordinal)
  let births ← (← request.getObjValAs? (Array Json) "births").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "cut",← item.getObjValAs? String "key")
  let replies ← (← request.getObjValAs? (Array Json) "replies").toList.mapM fun item => do
    let observed ← item.getObjValAs? Nat "observedCut"
    let atCut ← item.getObjValAs? Nat "cut"
    if observed ≥ atCut ∨ atCut ≥ cut then throw "REPLY_ORDER"
    return (atCut,observed,← item.getObjValAs? Nat "challenger",← optional (← item.getObjVal? "alleged") recordOfJson)
  let candidate ← request.getObjValAs? Nat "candidate"
  let originals ← (← request.getObjValAs? (Array Json) "queries").toList.mapM fun item => do
    return (← item.getObjValAs? Nat "ordinal",← queryOfJson (← item.getObjVal? "query"))
  let epochQueries := fun ordinal => ((originals.find? fun item => item.1 = ordinal).map Prod.snd).getD (defaultQuery ordinal)
  let ordinal ← request.getObjValAs? Nat "ordinal"
  let phases ← (← request.getObjValAs? (Array Json) "phases").toList.mapM fun phase => do
    (← phase.getArr?).toList.mapM requestOfJson
  let handoffs ← if mode = "continuation" then pure none else do
    let received ← (← request.getObjValAs? (Array Json) "handoffs").toList.mapM fun item => do
      return (⟨← item.getObjValAs? Bool "replace",← item.getObjValAs? Nat "actor",← queryOfJson (← item.getObjVal? "query")⟩ : Handoff.Request)
    pure (some received)
  return ⟨queries,births,replies,cut,candidate,epochQueries,ordinal,⟨phases,handoffs⟩⟩

/-- The actual source semantics; retained for independent replay, never an argument of the public worker. -/
def actual (larger : Bool) (request : Json) : Except String Json :=
  (decode request).bind (sourceResponse larger)

/-- A proof-supported readout, with no private input or private source evaluation on its execution path. -/
def publicReadout (request : Json) : Except String Json := actual false request

theorem public_readout_is_actual (larger : Bool) (request : Json) : publicReadout request = actual larger request := by
  cases larger with
  | false => rfl
  | true =>
    unfold publicReadout actual
    cases decode request with
    | error _ => rfl
    | ok input => exact source_response_equal input

theorem actual_branches_equal (request : Json) : actual false request = actual true request :=
  public_readout_is_actual true request

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire

import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Packets
import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Wire
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root Lean

def actorJson (actor : Actor) : Json := match actor with
  | .inl p => toJson ("audit:"++toString p) | .inr p => toJson ("provider:"++toString p.val)
def goodName : Good → String
  | .seed => "seed" | .feed => "feed" | .life => "life" | .spare => "spare"
  | .waste => "waste" | .energy => "energy" | .labor => "labor"
def instrumentName : Instrument → String | .audit => "audit" | .provider => "provider" | .delivery => "delivery"
def useName : Use → String
  | .investment => "investment" | .necessity => "necessity" | .maintenance => "maintenance" | .contribution => "contribution" | .external => "external"
def basePort : Cell.Port → String | .common => "common" | .machine => "machine" | .revision => "revision"
def queryJson (query : Query) := Json.mkObj [("slots",toJson query.slots.val),("fields",toJson query.fields.val)]
def portJson : Port → Json
  | .audit port => Json.mkObj [("kind",toJson "audit"),("base",toJson (basePort port.base)),("query",port.query.elim Json.null queryJson)]
  | .provider port => match port with
    | .service => Json.mkObj [("kind",toJson "provider"),("base",toJson "service")]
    | .challenge => Json.mkObj [("kind",toJson "provider"),("base",toJson "challenge")]
    | .reserve owner => Json.mkObj [("kind",toJson "provider"),("base",toJson "reserve"),("owner",toJson owner.val)]
  | .exchange => Json.mkObj [("kind",toJson "exchange")]
def bundleJson (bundle : Bundle Good) : Json := Json.arr ((bundle.map fun (good,quantity) =>
  Json.arr #[toJson (goodName good),toJson (toString quantity)]).toArray)
def technologyJson (technology : Technology) : Json := Json.mkObj [
  ("audit",Json.mkObj [("technology",toJson technology.audit.technology),("holder",toJson technology.audit.holder),
    ("offered",toJson technology.audit.offered),("version",toJson technology.audit.version)]),
  ("provider",Json.mkObj [("technology",toJson technology.provider.technology),("holder",toJson (technology.provider.holder.map Fin.val)),
    ("offered",toJson (technology.provider.offered.map Fin.val)),("version",toJson technology.provider.version)]),
  ("clockLag",toJson (toString technology.clockLag)),("roundLag",toJson (toString technology.roundLag))]

def actionJson (action : JointAction) : Json :=
  let op := match action.operation with
    | .produce p => Json.mkObj [("kind",toJson "produce"),("actor",actorJson p)]
    | .transfer p q goods => Json.mkObj [("kind",toJson "transfer"),("from",actorJson p),("to",actorJson q),("bundle",bundleJson goods)]
    | .use p goods purpose => Json.mkObj [("kind",toJson "use"),("actor",actorJson p),("bundle",bundleJson goods),("purpose",toJson (useName purpose))]
    | .issue i p q n => Json.mkObj [("kind",toJson "issue"),("instrument",toJson (instrumentName i)),("debtor",actorJson p),("creditor",actorJson q),("quantity",toJson (toString n))]
    | .assign i p q r n => Json.mkObj [("kind",toJson "assign"),("instrument",toJson (instrumentName i)),("debtor",actorJson p),("creditor",actorJson q),("newCreditor",actorJson r),("quantity",toJson (toString n))]
    | .settle i p q n => Json.mkObj [("kind",toJson "settle"),("instrument",toJson (instrumentName i)),("debtor",actorJson p),("creditor",actorJson q),("quantity",toJson (toString n))]
    | .revise p next => Json.mkObj [("kind",toJson "revise"),("actor",actorJson p),("technology",technologyJson next)]
    | .present => Json.mkObj [("kind",toJson "present")]
  Json.mkObj [("signer",actorJson action.signer),("consents",toJson (action.consents.map actorJson)),
    ("purpose",portJson action.purpose),("gates",toJson (action.gates.map portJson)),("operation",op)]

def stateJson (current : Current) : Json := Json.mkObj [
  ("clock",toJson (toString current.clock)),("round",toJson current.round),("technology",technologyJson current.technology),
  ("stock",Json.arr ((actors.flatMap fun actor => (goods.filter fun good => (actor,good)!=(receiver,Good.feed)).map fun good =>
    Json.arr #[actorJson actor,toJson (goodName good),toJson (toString (current.stock actor good))]).toArray)),
  ("claims",Json.arr (([Instrument.audit,.provider,.delivery].flatMap fun i => actors.flatMap fun debtor => actors.map fun creditor =>
    Json.arr #[toJson (instrumentName i),actorJson debtor,actorJson creditor,toJson (toString (current.claims i debtor creditor))]).toArray))]

def scopeJson (scope : Scope) : Json := Json.mkObj [("unit",toJson "energy"),
  ("earliest",toJson (toString scope.task.earliest)),("deadline",toJson (toString scope.task.deadline)),
  ("slots",toJson (scope.task.slots.map fun slot => Json.mkObj [("actor",toJson slot.bearer),
    ("goods",bundleJson slot.goods),("purpose",toJson (useName slot.purpose))])),
  ("revisionCost",bundleJson scope.revisionCost)]
def flowJson (flow : Flow Actor Good) : Json := Json.arr ((flow.map fun ((actor,good),q) =>
  Json.arr #[actorJson actor,toJson (goodName good),toJson (toString q)]).toArray)
def itemJson (item : PublicItem) : Json := Json.mkObj [("index",toJson item.index),("request",actionJson item.request),
  ("accepted",toJson item.accepted),("debit",flowJson item.debit),("credit",flowJson item.credit)]

def refusalName : RefusalKind → String | .fuelAbsent => "fuel-absent" | .laborAbsent => "labor-absent" | .sourceRejected => "source-rejected"
def render (command : Command) (result : Except String Reply) : Json :=
  match result with
  | .error message => Json.mkObj [("metadata",command.metadata),("status",toJson "ERROR"),("message",toJson message)]
  | .ok reply =>
    let query := match command.request with | .ok (query,_) => query | .error _ => defaultQuery 0
    let packets := publicPackets reply.observation.actions reply.actor query
    let refusals := reply.observation.actions.filterMap fun item => if item.accepted then none else
      some (Json.mkObj [("index",toJson item.index),("kind",toJson (refusalName (refusalKind item.before item.request)))])
    Json.mkObj [("metadata",command.metadata),("status",toJson (if reply.opening then "OPENED" else
        if !packets.isEmpty then "DELIVERED" else if !refusals.isEmpty then "BLOCKED" else "CONTINUED")),
      ("actor",toJson reply.actor),("target",toJson reply.target),("history",toJson reply.historyLength),
      ("scope",scopeJson reply.scope),("nextScope",scopeJson reply.nextScope),("opening",toJson reply.opening),
      ("rows",toJson (reply.observation.actions.map itemJson)),("refusals",toJson refusals),
      ("packets",toJson (packets.map fun evidence => evidence.map fun (slot,value) => EnergyRenewal.Privacy.evidenceJson slot value)),
      ("next",stateJson reply.observation.next)]

def modeOfJson (value : Json) : Except String Mode := do
  match ← value.getStr? with
  | "normal" => pure .normal | "withhold-fuel" => pure .withholdFuel
  | "deny-production" => pure .denyProduction | "wrong-supplier" => pure .wrongSupplier
  | "refeed" => pure .refeed | "deny-recycling" => pure .denyRecycling
  | _ => throw "SUPPLY_MODE"

def commandOfJson (value : Json) : Command :=
  ⟨(do
    let query ← EnergyRenewal.Privacy.Wire.queryOfJson (←value.getObjVal? "query")
    let mode ← match value.getObjVal? "mode" with
      | .error _ => pure Mode.normal | .ok mode => modeOfJson mode
    return (query,mode)),value⟩

structure Execution (larger : Bool) where
  private mk ::
  input : EnergyRenewal.Privacy.SourceInput
  state : Finance.State (input.plan larger)
  output : List Json

/-- Public output and the closed-audit successor are readouts of the same source execution. -/
def execute (larger : Bool) (request : Json) : Except String (Execution larger) := do
  let base ← request.getObjVal? "base"
  let commands ← request.getObjValAs? (Array Json) "requests"
  let input ← EnergyRenewal.Privacy.Wire.decode base
  let initial ← Source.initial larger input
  let generated := play initial render (fun _ n => commandOfJson (commands[n]?.getD Json.null)) commands.size
  return ⟨input,generated.1,generated.2⟩

/-- This is the exact decoder and renderer used by the online source, including unsuccessful commands. -/
def actualTranscript (larger : Bool) (request : Json) : Except String (List Json) := do
  let base ← request.getObjVal? "base"
  let commands ← request.getObjValAs? (Array Json) "requests"
  let input ← EnergyRenewal.Privacy.Wire.decode base
  sourceOutput larger input render (fun _ n => commandOfJson (commands[n]?.getD Json.null)) commands.size

theorem complete_default_transcripts_are_equal (request : Json) :
    actualTranscript false request=actualTranscript true request := by
  unfold actualTranscript
  cases request.getObjVal? "base" with
  | error _ => rfl
  | ok base =>
    cases request.getObjValAs? (Array Json) "requests" with
    | error _ => rfl
    | ok commands =>
      simp only [bind,Except.bind]
      cases decoded : EnergyRenewal.Privacy.Wire.decode base with
      | error _ => rfl
      | ok input => exact every_source_strategy_keeps_complete_cumulative_supply_privacy input render _ _

def actual (larger : Bool) (request : Json) : Except String Json := do
  let output ← actualTranscript larger request
  match output.getLast? with
  | some value => pure value
  | none => throw "SUPPLY_REQUEST_REQUIRED"

def publicReadout (request : Json) : Except String Json := actual false request

theorem public_readout_is_its_actual_branch (larger : Bool) (request : Json) : publicReadout request=actual larger request := by
  cases larger with
  | false => rfl
  | true => unfold publicReadout actual;rw [complete_default_transcripts_are_equal]

theorem default_render_keeps_the_original_packets {plan : Plan} (state : Finance.State plan) (query : Query) (mode : Mode) :
    publicPackets (reply state query mode).observation.actions (reply state query mode).actor query=
      (state.session.packets query mode).map Packet.evidence :=
  (actual_packets_are_read_from_the_complete_public_trace state.session.window.scope state.session.prepared
    (state.session.actions query mode) state.session.actor query).symm

def adaptive (larger : Bool) (base : Json) (strategy : List Json → Nat → Json) (count : Nat) : Except String (List Json) :=
  (EnergyRenewal.Privacy.Wire.decode base).bind fun input =>
    sourceOutput larger input render (fun past n => commandOfJson (strategy past n)) count

theorem every_decoded_strategy_keeps_all_default_output (base : Json) (strategy : List Json → Nat → Json) (count : Nat) :
    adaptive false base strategy count=adaptive true base strategy count := by
  unfold adaptive
  cases EnergyRenewal.Privacy.Wire.decode base with
  | error _ => rfl
  | ok input => exact every_source_strategy_keeps_complete_cumulative_supply_privacy input render _ _

theorem execution_output_is_the_exact_default_transcript (larger : Bool) (request : Json) :
    (execute larger request).map Execution.output=actualTranscript larger request := by
  unfold execute actualTranscript sourceOutput
  cases base : request.getObjVal? "base" with
  | error _ => rfl
  | ok value =>
    cases commands : request.getObjValAs? (Array Json) "requests" with
    | error _ => rfl
    | ok items =>
      simp only [bind,Except.bind]
      cases input : EnergyRenewal.Privacy.Wire.decode value with
      | error _ => rfl
      | ok source =>
        simp only [Except.bind]
        cases original : Source.initial larger source with
        | error _ => rfl
        | ok state => rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Wire

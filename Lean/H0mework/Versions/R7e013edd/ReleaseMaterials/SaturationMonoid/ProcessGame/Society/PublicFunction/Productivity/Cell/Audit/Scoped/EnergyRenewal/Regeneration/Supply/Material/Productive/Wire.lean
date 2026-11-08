import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Privacy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Wire
open Lean

def modeOf (value : String) : Except String Mode := match value with
  | "normal" => .ok .normal | "deny-transport" => .ok .denyTransport
  | "deny-factory" => .ok .denyFactory | _ => .error "PRODUCTIVE_MODE"

def commandOfJson (value : Json) : Command := ⟨(do
  match ←value.getObjValAs? String "kind" with
  | "cycle" => return .inl (←modeOf (←value.getObjValAs? String "mode"))
  | "service" =>
    let query ←EnergyRenewal.Privacy.Wire.queryOfJson (←value.getObjVal? "query")
    let mode ←match value.getObjVal? "mode" with
      | .error _ => pure Supply.Mode.normal
      | .ok mode => Supply.Privacy.Wire.modeOfJson mode
    return .inr (query,mode)
  | _ => throw "PRODUCTIVE_KIND"),value⟩

def itemJson (item : Supply.Privacy.PublicItem) : Json := Json.mkObj [
  ("index",toJson item.index),
  ("request",Supply.Privacy.Wire.actionJson item.request),("accepted",toJson item.accepted),
  ("debit",Supply.Privacy.Wire.flowJson item.debit),("credit",Supply.Privacy.Wire.flowJson item.credit)]

def render (command : Command) (result : Except String Reply) : Json := match result with
  | .error message => Json.mkObj [("metadata",command.metadata),("status",toJson "ERROR"),("message",toJson message)]
  | .ok (.inl (history,observation)) => Json.mkObj [
    ("metadata",command.metadata),("status",toJson (if observation.actions.all (·.accepted) then "PRODUCED" else "BLOCKED")),
    ("history",toJson history),("before",Supply.Privacy.Wire.stateJson observation.before),
    ("rows",toJson (observation.actions.map itemJson)),("next",Supply.Privacy.Wire.stateJson observation.next)]
  | .ok (.inr reply) =>
    let request := match command.request with
      | .ok (.inr request) => .ok request | _ => .error "PRODUCTIVE_SERVICE"
    Supply.Privacy.Wire.render ⟨request,command.metadata⟩ (.ok reply)

theorem complete_adaptive_default_output_and_own_next {lp rp : Plan}
    (left : Finance.State lp) (right : Finance.State rp)
    (same : Supply.Privacy.Source.SessionTwin left.session right.session) (strategy : Strategy) (count : Nat) :
    Supply.Privacy.Source.SessionTwin (play left render strategy count).1.session (play right render strategy count).1.session ∧
      (play left render strategy count).2=(play right render strategy count).2 :=
  cumulative_related_own_states_and_complete_output left right same render strategy count

def sourceOutput (larger : Bool) (input : EnergyRenewal.Privacy.SourceInput)
    (prior : Supply.Privacy.Strategy) (priorCount : Nat) (strategy : Strategy) (count : Nat) : Except String (List Json) :=
  (Supply.Privacy.Source.initial larger input).map fun state =>
    (play (Supply.Privacy.play state Supply.Privacy.Wire.render prior priorCount).1 render strategy count).2

theorem every_original_source_history_generates_cumulative_privacy (input : EnergyRenewal.Privacy.SourceInput)
    (prior : Supply.Privacy.Strategy) (priorCount : Nat) (strategy : Strategy) (count : Nat) :
    sourceOutput false input prior priorCount strategy count=sourceOutput true input prior priorCount strategy count := by
  have consume : ∀ {lp rp : Plan} {left : Except String (Finance.State lp)} {right : Except String (Finance.State rp)},
      EnergyRenewal.Privacy.ResultRel
        (fun l r => Supply.Privacy.Source.SessionTwin l.session r.session ∧ l.account=r.account) left right →
      left.map (fun state => (play (Supply.Privacy.play state Supply.Privacy.Wire.render prior priorCount).1 render strategy count).2)=
        right.map (fun state => (play (Supply.Privacy.play state Supply.Privacy.Wire.render prior priorCount).1 render strategy count).2) := by
    intro lp rp left right related
    cases related with
    | error _ => rfl
    | ok matched =>
      have old := Supply.Privacy.cumulative_related_own_states_and_complete_output _ _ matched.1
        Supply.Privacy.Wire.render prior priorCount
      exact congrArg Except.ok (complete_adaptive_default_output_and_own_next _ _ old.1 strategy count).2
  exact consume (Supply.Privacy.Source.original_source_generates_new_supply_initial_relation input)

structure Execution (larger : Bool) where
  input : EnergyRenewal.Privacy.SourceInput
  initial : Finance.State (input.plan larger)
  state : Finance.State (input.plan larger)
  prior : List Json
  output : List Json

structure Decoded where
  input : EnergyRenewal.Privacy.SourceInput
  prior : Array Json
  commands : Array Json

def decode (request : Json) : Except String Decoded := do
  let parent ←request.getObjVal? "parent"
  let base ←parent.getObjVal? "base"
  let prior ←parent.getObjValAs? (Array Json) "requests"
  let input ←EnergyRenewal.Privacy.Wire.decode base
  let commands ←request.getObjValAs? (Array Json) "commands"
  return ⟨input,prior,commands⟩

def Decoded.priorStrategy (decoded : Decoded) : Supply.Privacy.Strategy :=
  fun _ n => Supply.Privacy.Wire.commandOfJson (decoded.prior[n]?.getD Json.null)
def Decoded.strategy (decoded : Decoded) : Strategy :=
  fun _ n => commandOfJson (decoded.commands[n]?.getD Json.null)

def execute (larger : Bool) (request : Json) : Except String (Execution larger) := do
  let decoded ←decode request
  let state ←Supply.Privacy.Source.initial larger decoded.input
  let old := Supply.Privacy.play state Supply.Privacy.Wire.render decoded.priorStrategy decoded.prior.size
  let generated := play old.1 render decoded.strategy decoded.commands.size
  return ⟨decoded.input,old.1,generated.1,old.2,generated.2⟩

def actualTranscript (larger : Bool) (request : Json) : Except String (List Json) := do
  let decoded ←decode request
  sourceOutput larger decoded.input decoded.priorStrategy decoded.prior.size decoded.strategy decoded.commands.size

theorem execution_output_is_the_exact_default_transcript (larger : Bool) (request : Json) :
    (execute larger request).map Execution.output=actualTranscript larger request := by
  unfold execute actualTranscript
  cases parsed : decode request with
  | error _ => rfl
  | ok decoded =>
    simp only [bind,Except.bind]
    unfold sourceOutput
    cases initial : Supply.Privacy.Source.initial larger decoded.input <;> rfl

theorem complete_default_transcripts_are_equal (request : Json) :
    actualTranscript false request=actualTranscript true request := by
  unfold actualTranscript
  cases parsed : decode request with
  | error _ => rfl
  | ok decoded =>
    exact every_original_source_history_generates_cumulative_privacy decoded.input
      decoded.priorStrategy decoded.prior.size decoded.strategy decoded.commands.size

def actual (larger : Bool) (request : Json) : Except String Json := do
  let output ←actualTranscript larger request
  match output.getLast? with
  | none => throw "PRODUCTIVE_REQUEST_REQUIRED"
  | some value => pure value

def publicReadout (request : Json) : Except String Json := actual false request

theorem public_readout_is_its_actual_branch (larger : Bool) (request : Json) :
    publicReadout request=actual larger request := by
  cases larger with
  | false => rfl
  | true => unfold publicReadout actual;rw [complete_default_transcripts_are_equal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Wire

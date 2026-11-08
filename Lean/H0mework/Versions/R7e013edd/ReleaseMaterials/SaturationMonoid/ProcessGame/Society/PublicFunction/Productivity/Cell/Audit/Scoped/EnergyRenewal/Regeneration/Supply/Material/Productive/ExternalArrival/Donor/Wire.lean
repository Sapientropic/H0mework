import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Wire
open Lean Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def sourceRoot : String := "original-target-donor/feed6/v1"
def statusName : Status → String
  | .supplied => "SUPPLIED"
  | .blocked reason => match reason with
    | .stale => "STALE"
    | .withheld => "WITHHELD"
    | .signer => "WRONG_SIGNER"
    | .material => "MATERIAL"
    | .sourceLaw => "SOURCE_LAW"

def decode (command : Json) : Except String (Nat × Actor × Bool) := do
  let quantity ← command.getObjValAs? Nat "quantity"
  if quantity ≠ 6 then throw "DONOR_QUANTITY"
  let round ← command.getObjValAs? Nat "round"
  let signer ← command.getObjValAs? Nat "signer"
  let enabled ← command.getObjValAs? Bool "enabled"
  if signer < 4 then return (round,.inl signer,enabled)
  else throw "DONOR_SIGNER_RANGE"

def isDonation (command : Json) : Bool :=
  (command.getObjValAs? String "kind").toOption == some "donate"

def advance {plan : Plan} (state : State plan) (command : Json) : State plan :=
  if isDonation command then
    match decode command with
    | .error _ => state
    | .ok (round,signer,enabled) => donate state round signer enabled
  else operate state command

def render {plan : Plan} (state : State plan) (command : Json) : Json :=
  if isDonation command then
    match decode command with
    | .error message => Json.mkObj [("source_root",toJson sourceRoot),("metadata",command),
        ("status",toJson "ERROR"),("message",toJson message)]
    | .ok (round,signer,enabled) =>
      let before := prepared state.legacy.service
      let word := Donor.word state.legacy.service round signer enabled before
      let after := donate state round signer enabled
      Json.mkObj [("source_root",toJson sourceRoot),("metadata",command),
        ("status",toJson (statusName (status state.legacy.service round signer enabled before))),
        ("source_id",toJson ("audit:3/round:"++toString (origin state.legacy.service))),
        ("origin",toJson (origin state.legacy.service)),("next_origin",toJson (origin after.legacy.service)),
        ("before",Supply.Privacy.Wire.stateJson (Supply.Privacy.publicize before)),
        ("rows",toJson ((Productive.publicItems state.legacy.service.session.window.scope before word 0).map Productive.Wire.itemJson)),
        ("next",Supply.Privacy.Wire.stateJson (Supply.Privacy.publicize after.legacy.service.session.current)),
        ("oldSource",ExternalArrival.Wire.sourceJson (Consume.sourceCurrent state.legacy)),
        ("oldSourceNext",ExternalArrival.Wire.sourceJson (Consume.sourceCurrent after.legacy)),
        ("oldSpent",toJson after.legacy.spent),("account",ExternalArrival.Wire.account after.legacy)]
  else ExternalArrival.Wire.render state.legacy command

structure Execution (larger : Bool) where
  input : EnergyRenewal.Privacy.SourceInput
  old : List Json
  state : State (input.plan larger)
  output : List Json

def execute (larger : Bool) (request : Json) : Except String (Execution larger) := do
  let original ← ExternalArrival.Wire.execute larger (←request.getObjVal? "base")
  let commands ← request.getObjValAs? (Array Json) "commands"
  let mut state := start original.state
  let mut output := []
  for command in commands do
    output := output++[render state command]
    state := advance state command
  return ⟨original.input,original.output,state,output⟩

def readout (larger : Bool) (request : Json) : Except String Json := do
  let execution ← execute larger request
  return Json.mkObj [("schema",toJson "actual77-donor-continuation/v1"),("old",toJson execution.old),
    ("output",toJson execution.output),("next",Supply.Privacy.Wire.stateJson execution.state.legacy.service.session.current),
    ("oldSource",ExternalArrival.Wire.sourceJson (Consume.sourceCurrent execution.state.legacy)),
    ("oldSpent",toJson execution.state.legacy.spent),("attempts",toJson execution.state.receipts.length),
    ("account",ExternalArrival.Wire.account execution.state.legacy)]

theorem decoded_donation_is_the_actual_source_update {plan : Plan} (state : State plan) (command : Json)
    (kind : isDonation command = true) (round : Nat) (signer : Actor) (enabled : Bool)
    (decoded : decode command = .ok (round,signer,enabled)) :
    advance state command = donate state round signer enabled := by simp only [advance,kind,if_true,decoded]

theorem every_old_command_uses_the_original_consumer {plan : Plan} (state : State plan) (command : Json)
    (old : isDonation command = false) :
    (advance state command).legacy = ExternalArrival.Wire.advance state.legacy command ∧
      render state command = ExternalArrival.Wire.render state.legacy command := by
  simp [advance,render,old,operate]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Wire

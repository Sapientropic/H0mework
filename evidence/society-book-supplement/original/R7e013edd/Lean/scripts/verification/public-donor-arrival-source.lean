import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Wire

open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal

def main (args : List String) : IO Unit := do
  let mode := args.headD "public"
  if mode != "public" && mode != "private-one" && mode != "private-two" then
    throw (IO.userError "WORKER_MODE")
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result : Except String Json := do
      let request ← Json.parse line
      match (request.getObjValAs? String "mode").toOption with
      | some "donor-probe" =>
        let left ← Regeneration.Supply.Productive.ExternalArrival.Donor.Wire.readout false request
        let right ← Regeneration.Supply.Productive.ExternalArrival.Donor.Wire.readout true request
        return Json.mkObj [("left",left),("right",right)]
      | some "donor" =>
        let execution ← Regeneration.Supply.Productive.ExternalArrival.Donor.Wire.execute (mode="private-two") request
        match execution.output.getLast? with
        | none => throw "DONOR_EMPTY_WORD"
        | some reply => return reply
      | some "source-extension" => request.getObjVal? "native"
      | some "arrival-replay" =>
        (Regeneration.Supply.Productive.ExternalArrival.Wire.execute (mode="private-two") request).map (fun e => toJson e.output)
      | some "arrival" =>
        if mode="public" then Regeneration.Supply.Productive.ExternalArrival.Wire.publicReadout request
        else Regeneration.Supply.Productive.ExternalArrival.Wire.actual (mode="private-two") request
      | some "productive" =>
        if mode="public" then Regeneration.Supply.Productive.Wire.publicReadout request
        else Regeneration.Supply.Productive.Wire.actual (mode="private-two") request
      | some "regeneration" =>
        if mode="public" then Regeneration.Supply.Privacy.Wire.publicReadout request
        else Regeneration.Supply.Privacy.Wire.actual (mode="private-two") request
      | _ => if mode="public" then Privacy.Wire.publicReadout request else Privacy.Wire.actual (mode="private-two") request
    stdout.putStrLn ((match result with | .ok value => value | .error message => Json.mkObj [("error",toJson message)]).compress)
    stdout.flush

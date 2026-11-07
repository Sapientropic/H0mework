import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire
open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy

def main (args : List String) : IO Unit := do
  let mode := args.headD "public"
  if mode != "public" && mode != "actual-one" && mode != "actual-two" then
    throw (IO.userError "WORKER_MODE")
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result : Except String Json := do
      let request ← Json.parse line
      if mode = "public" then Wire.publicReadout request else Wire.actual (mode = "actual-two") request
    stdout.putStrLn ((match result with | .ok value => value | .error message => Json.mkObj [("error",toJson message)]).compress)
    stdout.flush

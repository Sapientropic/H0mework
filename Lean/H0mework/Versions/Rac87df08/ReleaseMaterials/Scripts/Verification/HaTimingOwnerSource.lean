import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Timing.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
open Lean
open SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
open Audit.Scoped Audit.Scoped.EnergyRenewal Audit.Scoped.EnergyRenewal.Privacy

/-- Owner-only materialization of the source frame and actual root next, after the public epoch. -/
def inspectOwnedNext (larger : Bool) (raw : Json) : Except String Json := do
  let input ← Wire.decode raw
  let own ← Timing.sourceHandoffSeed larger input
  let visible ← Timing.sourceHandoffSeed false input
  let requests := input.commands.handoffs.getD []
  let actual := own.current requests (own.ordinal+requests.length+1)
  let restored := Timing.rebuild (visible.current requests (visible.ordinal+requests.length+1))
    (Timing.ownFrame own.window.initial)
  let native ← Wire.actual larger raw
  return Json.mkObj [("native",native),("actualPublic",snapshot actual),("rebuiltPublic",snapshot restored),
    ("frame",toJson ((List.range 4).map fun actor => Json.mkObj [("actor",toJson actor),
      ("sourceInitial",toJson (toString (own.window.initial.stock actor .feed))),
      ("actualNext",toJson (toString (actual.stock actor .feed))),
      ("rebuiltNext",toJson (toString (restored.stock actor .feed)))])),
    ("sourceOrdinal",toJson own.ordinal),("consumedRequests",toJson requests.length)]

def main (arguments : List String) : IO Unit := do
  let some variant := arguments.head? | throw (IO.userError "OWNER_VARIANT_REQUIRED")
  if variant ≠ "private-one" ∧ variant ≠ "private-two" then throw (IO.userError "OWNER_VARIANT_REQUIRED")
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= inspectOwnedNext (variant = "private-two")
    stdout.putStrLn ((match result with | .ok value => value | .error message => Json.mkObj [("error",toJson message)]).compress)
    stdout.flush

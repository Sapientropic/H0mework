import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundState
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BodyMaterial
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NeuralMaterial
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3MaterialFiles
set_option autoImplicit false
namespace FlyCNS.C3BoundKernel
open Lean
def directory : System.FilePath := "Lean/scratch/FlyCNS/.cache/C3"
structure Identity where
  instanceId : String
  occurrenceId : String
  installationId : String
structure Installation where
  private mk ::
  identity : Identity
  kernel : FlyCNS.C3Macro.Material
structure Environment where
  tick : Int
  odor_gain : Array Float
  sugar_stock : Array Float
  water_stock : Array Float
  deriving FromJson
structure Neural where
  start_tick : Int
  stop_tick : Int
  period_ticks : Int
  neurons : Array Nat
  pulse_uv : Int
  deriving FromJson
def checked {α : Type} (e : Except String α) : IO α :=
  match e with | .ok v => pure v | .error why => throw (IO.userError why)
def readJson (p : System.FilePath) : IO Json := do checked (Json.parse (← IO.FS.readFile p))

/-- The authoritative IO caller supplies only its existing identity. This
module has no Source dependency and accepts no primitive evaluator or after. -/
def install (identity : Identity) : IO Installation := do
  for (relative,digest) in FlyCNS.C3MaterialFiles.original do
    let command ← IO.Process.output {cmd:="shasum",args:=#["-a","256",(directory/relative).toString]}
    if command.exitCode != 0 || (command.stdout.splitOn " ").headD "" != digest then
      throw (IO.userError ("raw-derived C7 material changed: "++relative))
  let (neural,_) ← FlyCNS.C3Integer.readMaterial (directory/"integer-material-200")
  let body ← FlyCNS.C3Body.material (directory/"whole-body-source-tick-200/material")
  let writer : FlyCNS.C3Writer.Material ← checked (fromJson? (← readJson (directory/"common-pure-macros-200/writer/material.json")))
  if writer.instance_id != identity.instanceId || writer.occurrence_id != identity.occurrenceId ||
      writer.installation_sha256 != identity.installationId then
    throw (IO.userError "pure numerical material changes source identity")
  let catalogue ← checked (FlyCNS.C3Registered.admit writer)
  let frames ← readJson (directory/"raw-programme-whole-native-tick-200/schedule.json")
  let e : Array Environment ← checked (frames.getObjValAs? _ "environment")
  let n : Array Neural ← checked (frames.getObjValAs? _ "neural")
  let programme : FlyCNS.C3Programme.Material := ⟨e.map (fun f => ⟨Int64.ofInt f.tick,f.odor_gain,f.sugar_stock,f.water_stock⟩),
    n.map fun f => ⟨Int64.ofInt f.start_tick,Int64.ofInt f.stop_tick,Int64.ofInt f.period_ticks,f.neurons,Int64.ofInt f.pulse_uv⟩⟩
  return ⟨identity,⟨⟨neural,body⟩,programme,catalogue⟩⟩
def generate (installed : Installation) (before : FlyCNS.C3BoundState.RawCurrent) : Except String FlyCNS.C3Successful.Result := do
  let state ← FlyCNS.C3BoundState.decode before
  FlyCNS.C3Successful.successor installed.kernel state
end FlyCNS.C3BoundKernel

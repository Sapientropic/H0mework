import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.Source
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.currentAt_eq_frame
run_elab do
  let env ← getEnv
  let owners := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.CurrentFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.Source]
  let mut output := #[]
  for owner in owners do
    let some index := env.getModuleIdx? owner | throwError "missing original actual C caller {owner}"
    for entry in IR.declMapExt.getModuleEntries env index do
      output := output.push <| Json.mkObj [("owner",toJson owner.toString),("name",toJson entry.name.toString),("body",toJson (toString entry))]
  let some target ← IO.getEnv "HW_ROOT_FRAME_IR" | throwError "missing output path"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "CURRENT FRAME ACTUAL CALLER IR EMITTED"

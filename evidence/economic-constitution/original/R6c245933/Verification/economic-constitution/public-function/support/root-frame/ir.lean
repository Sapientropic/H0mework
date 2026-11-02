import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.foldedRootVisitAt_is_the_original_visit
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime.stateAt_eq_frame
run_elab do
  let env ← getEnv
  let owners := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime]
  let mut output := #[]
  for owner in owners do
    let some index := env.getModuleIdx? owner | throwError "missing original actual C caller {owner}"
    for entry in IR.declMapExt.getModuleEntries env index do
      output := output.push <| Json.mkObj [("owner",toJson owner.toString),("name",toJson entry.name.toString),("body",toJson (toString entry))]
  let some target ← IO.getEnv "HW_ROOT_FRAME_IR" | throwError "missing output path"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "ROOT FRAME ACTUAL CALLER IR EMITTED"

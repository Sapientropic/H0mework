import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Source
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime.currentAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime.wordAt_eq_frame
run_elab do
  let env ← getEnv
  let names := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime.frameCurrentAt, `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime.frameWordAt, `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.history]
  let mut output := #[]
  for name in names do
    let some declaration := IR.findEnvDecl env name | throwError "missing actual lifecycle readout {name}"
    output := output.push <| Json.mkObj [("name",toJson name.toString),("body",toJson (toString declaration))]
  let some moduleIndex := env.getModuleIdx? `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Source | throwError "missing original Financed source module"
  for declaration in IR.declMapExt.getModuleEntries env moduleIndex do
    output := output.push <| Json.mkObj [("name",toJson declaration.name.toString),("body",toJson (toString declaration))]
  let some target ← IO.getEnv "HW_LIFECYCLE_IR" | throwError "missing IR output"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "LIFECYCLE FRAME IR EMITTED"

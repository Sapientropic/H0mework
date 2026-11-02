import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.FutureRuntime.stateAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime.stateAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime.stateAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime.stateAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime.stateAt_eq_frame
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime.stateAt_eq_frame
run_elab do
  let env ← getEnv
  let owners := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime]
  let mut output := #[]
  for owner in owners do
    let some index := env.getModuleIdx? owner | throwError "missing original actual C caller {owner}"
    for entry in IR.declMapExt.getModuleEntries env index do
      output := output.push <| Json.mkObj [("owner",toJson owner.toString),("name",toJson entry.name.toString),("body",toJson (toString entry))]
  let some target ← IO.getEnv "HW_TEMPORAL_IR" | throwError "missing output path"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "TEMPORAL FRAME SIX ACTUAL CALLERS IR EMITTED"

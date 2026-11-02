import PublicDefaultActualNative
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
run_elab do
  let env ← getEnv
  let modules := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement]
  let mut entries := #[]
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName | throwError "module missing {moduleName}"
    for declaration in IR.declMapExt.getModuleEntries env index do
      entries := entries.push <| Json.mkObj [("name",toJson declaration.name.toString),
        ("module",toJson moduleName.toString),
        ("params",Json.arr <| declaration.params.map fun p => Json.mkObj [("borrow",toJson p.borrow),("type",toJson (reprStr p.ty))]),
        ("result",toJson (reprStr declaration.resultType))]
  let some target ← IO.getEnv "HW_IR_ABI" | throwError "missing IR ABI output"
  IO.FS.writeFile target ((Json.arr entries).pretty ++ "\n")
  logInfo m!"DIRECT FINANCE IMPURE ABI EMITTED: {entries.size}"

import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
set_option pp.maxSteps 100000
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.produce_eq_shared
run_elab do
  let env ← getEnv
  let sourceName := "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event."
  let mut output := #[]
  for suffix in ["produceShared", "Future.Native.produce"] do
    let name := (sourceName ++ suffix).toName
    let some decl := IR.findEnvDecl env name | throwError "missing compiled actual event producer {name}"
    let rendered := toString decl
    if suffix == "produceShared" then
      unless (rendered.splitOn (sourceName ++ "response")).length == 2 do
        throwError "shared actual event must construct exactly one original response"
      if (rendered.splitOn (sourceName ++ "evolution")).length != 1 ||
          (rendered.splitOn (sourceName ++ "financialRun")).length != 1 then
        throwError "shared event still calls a factory which independently reconstructs its response"
    else
      unless (rendered.splitOn (sourceName ++ "produceShared")).length == 2 do
        throwError "original Future consumer did not consume the shared actual event"
    output := output.push <| Json.mkObj [("name",toJson name.toString),("body",toJson rendered)]
  let some target ← IO.getEnv "HW_EVENT_ONCE_IR" | throwError "missing output"
  IO.FS.writeFile target ((Json.arr output).pretty ++ "\n")
  logInfo "SHARED EVENT IR PASS: one original response; actual evolution and finance consume it; original Future consumer calls shared producer"

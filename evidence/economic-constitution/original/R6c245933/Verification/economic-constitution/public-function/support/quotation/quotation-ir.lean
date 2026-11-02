import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Task
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
run_elab do
  let env ← getEnv
  let sourcePrefix := "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource."
  let mut outputs := #[]
  for suffix in ["quoteRateCached", "rateCached", "task", "quotedActions"] do
    let name := (sourcePrefix ++ suffix).toName
    let some decl := IR.findEnvDecl env name | throwError "missing original quotation worker {name}"
    let text := toString decl
    if suffix == "quoteRateCached" || suffix == "rateCached" then
      unless (text.splitOn (sourcePrefix ++ "quotedActions")).length == 2 do
        throwError "the quote search does not construct its shared original alphabet exactly once"
      if (text.splitOn (sourcePrefix ++ "code")).length != 1 ||
         (text.splitOn (sourcePrefix ++ "instDecidableOffered")).length != 1 then
        throwError "the quote search still calls the uncached code or offered predicate"
    if suffix == "task" then
      unless (text.splitOn (sourcePrefix ++ "rateCached")).length > 1 do
        throwError "the original Task producer does not consume the shared quote implementation"
    outputs := outputs.push <| Json.mkObj [("name",toJson name.toString),("body",toJson text)]
  let some target ← IO.getEnv "HW_QUOTE_IR" | throwError "missing IR target"
  IO.FS.writeFile target ((Json.arr outputs).pretty ++ "\n")
  logInfo "QUOTE CACHE IR PASS: one shared alphabet per search; no repeated original Code/Offered worker; original Task consumes cached rates"

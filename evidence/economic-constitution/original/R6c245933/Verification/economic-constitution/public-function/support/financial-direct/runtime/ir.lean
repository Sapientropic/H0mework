import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion
import Lean.Compiler.IR.CompilerM
import Lean.Elab.Command
open Lean Elab Command
set_option pp.maxSteps 100000
#print axioms SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion.Decision.financialRun_eq_direct
run_elab do
  let env ← getEnv
  let namespaceName := "SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion."
  let mut output := #[]
  for suffix in ["Decision.financialRun", "Decision.financialRunDirect", "Disposition.financialRun"] do
    let name := (namespaceName ++ suffix).toName
    let some decl := IR.findEnvDecl env name | throwError "missing compiled financial run {name}"
    let rendered := toString decl
    output := output.push <| Json.mkObj [("name",toJson name.toString),("body",toJson rendered)]
  IO.FS.writeFile ".agents/tmp/public-autonomous-origin-20261101/financial-direct/runtime/ir.json" ((Json.arr output).pretty ++ "\n")
  logInfo "DIRECT COMPLETION FINANCE IR EMITTED"

import PublicDefaultActualNative
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.ModPkgExt
import Lean.Compiler.NameMangling
import Lean.Elab.Command
open Lean Elab Command
run_elab do
  let env ← getEnv
  let modules := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Task,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Review,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Finance,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Plan,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.FinanceTransport,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Portfolio.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Repair.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Grant,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Costs,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback.Prefix,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Challenge,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.ChallengeRegression,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Future.Expiry.Progress.Responsibility.Transport]
  let mut entries := #[]
  let mut packages := #[]
  for moduleName in modules do
    let some index := env.getModuleIdx? moduleName | throwError "module missing {moduleName}"
    packages := packages.push <| Json.mkObj [("module", toJson moduleName.toString), ("package",toJson (env.getModulePackageByIdx? index))]
    for declaration in IR.declMapExt.getModuleEntries env index do
      let symbol ← match getExportNameFor? env declaration.name with
        | none => pure (getSymbolStem env declaration.name)
        | some (.str .anonymous s) => pure s
        | some n => throwError "unsupported export {n}"
      entries := entries.push <| Json.mkObj [("name",toJson declaration.name.toString),
        ("symbol",toJson symbol), ("module",toJson moduleName.toString),
        ("params",Json.arr <| declaration.params.map fun p => Json.mkObj [("borrow",toJson p.borrow),("type",toJson (reprStr p.ty))]),
        ("result",toJson (reprStr declaration.resultType))]
  let some target ← IO.getEnv "HW_IR_ABI" | throwError "missing IR ABI output"
  IO.FS.writeFile target ((Json.mkObj [("modules",Json.arr packages),("declarations",Json.arr entries)]).pretty ++ "\n")
  logInfo m!"LIFECYCLE IMPURE ABI EMITTED: modules={modules.size} declarations={entries.size}"

import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime
import Lean.Replay
import Lean.Elab.Command
import Lean.Util.FoldConsts

open Lean Elab Command
set_option maxRecDepth 100000

private partial def collect (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then collect env rest seen
    else match env.find? name with
      | none => collect env rest (seen.insert name)
      | some info => collect env (info.getUsedConstantsAsSet.toList ++ rest) (seen.insert name)

elab "#check_public_scoped_audit_kernel" : command => do
  let env ← getEnv
  let owned := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Continuation, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Evidence, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Origin, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Source, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Disclosure, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Actual, `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.Runtime]
  let explicit : Array Name := #[]
  let constants := env.constants.toList
  let roots := constants.filterMap fun (name,info) =>
    if (((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains || explicit.contains name) &&
        !info.isUnsafe && !info.isPartial then some name else none

  let closure := collect env roots
  let missing := closure.toList.filter fun name => (env.find? name).isNone
  unless missing.isEmpty do
    for (name,info) in constants do
      if closure.contains name && missing.any info.getUsedConstantsAsSet.contains then
        let owner := (env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!
        logInfo m!"REBUILD HELPER CONSUMER: {owner}"
    throwError "missing generated dependencies {missing}"
  let mut inventory : Std.HashMap Name ConstantInfo := {}
  let mut privateCount := 0
  let mut axioms : Array Name := #[]
  for name in closure do
    let some info := env.find? name | throwError "missing dependency {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe or partial logical dependency {name}"
    inventory := inventory.insert name info
    if (privateToUserName? name).isSome then privateCount := privateCount + 1
    if info matches .axiomInfo _ then axioms := axioms.push name
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do throwError "unauthorized axiom {axiomName}"
  let trace := collect env [`SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.traceCheck]
  let lifecycle := collect env [`SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.lifecycleCheck]
  if lifecycle.contains `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.traceCheck || trace.contains `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.lifecycleCheck then
    throwError "one scoped checker calls the other"
  for name in trace.toList ++ lifecycle.toList do
    if name == `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.source then
      throwError "public checker reaches the global source"
  logInfo "SCOPED CLIENT CLOSURES PASS: no global Cell.source; neither client calls the other"
  let fresh ← liftIO (mkEmptyEnvironment 0)
  let _ ← liftIO (Environment.replay inventory fresh)
  logInfo m!"PUBLIC SCOPED AUDIT KERNEL PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_public_scoped_audit_kernel

import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime
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

elab "#check_public_history_fold_runtime_kernel" : command => do
  let env ← getEnv
  let constants := env.constants.toList
  let roots : List Name := [`SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.FutureRuntime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.FutureRuntime.stateAt_eq_frame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime.stateAt_eq_frame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime.stateAt_eq_frame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime.stateAt_eq_frame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime.stateAt_eq_frame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime.stateAtFromFrame,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime.stateAt_eq_frame]

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
  let fresh ← liftIO (mkEmptyEnvironment 0)
  let _ ← liftIO (Environment.replay inventory fresh)
  logInfo m!"TEMPORAL FRAME KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_public_history_fold_runtime_kernel

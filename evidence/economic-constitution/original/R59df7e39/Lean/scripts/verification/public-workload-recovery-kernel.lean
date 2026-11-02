import SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Runtime
import SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
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
      | some info =>
        let peers := match info with
          | .inductInfo v => v.all ++ v.ctors
          | .ctorInfo v => [v.induct]
          | .recInfo v => v.all
          | .defnInfo v => v.all
          | .thmInfo v => v.all
          | _ => []
        collect env (info.getUsedConstantsAsSet.toList ++ peers ++ rest) (seen.insert name)

elab "#check_public_native_recovery_metering_kernel" : command => do
  let env ← getEnv
  let owned := #[`SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Cursor,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Walk,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Runtime,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Evaluation,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Runtime]
  for moduleName in owned do
    unless env.header.moduleNames.contains moduleName do throwError "missing owned module {moduleName}"
  let constants := env.constants.toList
  let roots := constants.filterMap fun (name,info) =>
    if ((env.getModuleIdxFor? name).map fun i => env.header.moduleNames[i.toNat]!).any owned.contains &&
        !info.isUnsafe && !info.isPartial then some name else none

  let closure := collect env roots
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
  logInfo m!"WORKLOAD RECOVERY EMPTY KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_public_native_recovery_metering_kernel

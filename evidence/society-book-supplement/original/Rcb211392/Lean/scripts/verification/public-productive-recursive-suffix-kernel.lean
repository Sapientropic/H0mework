import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Continuation
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

elab "#check_productive_recursive_suffix_kernel" : command => do
  let env ← getEnv
  let roots : List Name := [
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.every_intermediate_window_survives_its_remaining_future,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.every_actual_account_generates_the_remaining_account,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.every_intermediate_native_archive_is_preserved,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.full_carrier_continues_from_its_own_actual_after ]
  if roots.isEmpty then throwError "empty productive settlement audit"
  let closure := collect env roots
  let absent := closure.toList.filter fun name => (env.find? name).isNone
  unless absent.isEmpty do
    for name in absent do
      let parents := closure.toList.filter fun caller =>
        (env.find? caller).any fun info => info.getUsedConstantsAsSet.contains name
      logInfo m!"MISSING DEPENDENCY {name}; referenced by {parents}"
    throwError "incomplete logical dependency inventory ({absent.length} missing)"
  let mut inventory : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut privateCount := 0
  let mut usedModules : NameSet := {}
  for name in closure do
    let some info := env.find? name | do
      let parents := closure.toList.filter fun caller =>
        (env.find? caller).any fun info => info.getUsedConstantsAsSet.contains name
      throwError "missing dependency {name}; referenced by {parents}"
    if info.isUnsafe || info.isPartial then throwError "unsafe or partial logical dependency {name}"
    inventory := inventory.insert name info
    if let some moduleIndex := env.getModuleIdxFor? name then
      usedModules := usedModules.insert env.header.moduleNames[moduleIndex.toNat]!
    if (privateToUserName? name).isSome then privateCount := privateCount + 1
    if info matches .axiomInfo _ then axioms := axioms.push name
  for axiomName in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "unauthorized axiom {axiomName}"
  let fresh ← liftIO (mkEmptyEnvironment 0)
  let _ ← liftIO (Environment.replay inventory fresh)
  logInfo m!"KERNEL MODULES: {usedModules.toList.length}"
  logInfo m!"PRODUCTIVE RECURSIVE SUFFIX KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_productive_recursive_suffix_kernel

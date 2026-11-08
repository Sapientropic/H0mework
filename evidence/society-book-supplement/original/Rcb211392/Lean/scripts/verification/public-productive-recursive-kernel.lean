import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime
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

elab "#check_productive_recursive_kernel" : command => do
  let env ← getEnv
  let roots : List Name := [
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.capture,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.original_current_prefix,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.selected_word,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.own_current,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.every_actual_after_generates_the_remaining_future,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.every_finite_future_preserves_due_and_completed,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.every_finite_future_accounts_for_every_old_window,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.every_finite_future_preserves_old_claims,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.consume,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.actual_before_and_after,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.same_occurrence_whole_ledger_and_own_next,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.every_original_claim_keeps_its_native_position,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.every_original_archive_is_preserved,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime.original_native_history_is_preserved,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.completion_pays_its_own_window,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.completion_keeps_its_own_deadline,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.new_service_cannot_settle_the_inherited_task ]
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
  logInfo m!"PRODUCTIVE RECURSIVE KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_productive_recursive_kernel

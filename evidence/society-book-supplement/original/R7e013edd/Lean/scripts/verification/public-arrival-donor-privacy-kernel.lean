import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Donor.Privacy
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

elab "#check_arrival_donor_privacy_kernel" : command => do
  let env ← getEnv
  -- Logical mouths include the whole actual source, transport, financial inventory and consumer.
  -- Compile-time syntax extraction is not a logical premise; its emitted term is in this closure.
  let roots : List Name := [
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Runtime.same_occurrence_whole_ledger_and_own_next,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Consumer.the_same_actual_occurrence_pays_and_delivers,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Consumer.a_new_donor_never_reopens_the_old_complete_source,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Consumer.the_whole_old_responsibility_and_financial_prefix_survive,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Wire.every_old_command_uses_the_original_consumer,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.SourceFunding.original_governance_generates_its_private_feed_range,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.SourceFunding.actual_source_initial_is_backed,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.SourceFunding.original_arrival_execution_is_backed,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.donate_related,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.render_public,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.original_base_generates_the_donor_initial_relation,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.original_source_generates_the_complete_donor_execution_relation,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.complete_original_donor_readouts_are_equal,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.every_adaptive_prefix_keeps_related_actual_successors_and_complete_output,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.the_original_source_generates_every_adaptive_donor_relation,
    `SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor.Privacy.every_generated_policy_word_is_consumed_by_the_original_wire ]
  if roots.isEmpty then throwError "empty arrival donor privacy audit"
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
  logInfo m!"DONOR KERNEL REPLAY PASS: roots={roots.length}, closure={inventory.size}, private={privateCount}, axioms={axioms}"

#check_arrival_donor_privacy_kernel

from pathlib import Path
c=Path('.cache/fixed-mother-certification');p=c/'Consumers.lean';s=p.read_text();old=Path('docs/audits/physics/source-uniqueness/MotherCumulativeAdmittedWorld.lean').read_text();helper=old[old.index('private def completeRefs'):old.index('private partial def recoveryReach')]
if '\nopen Lean Elab Command\n' in s:s=s[:s.index('\nopen Lean Elab Command\n')]
s+='\nopen Lean Elab Command\nopen SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\n'+helper+'''run_cmd do
  let env ← getEnv
  let controls := [``FixedMotherConsumers.original_world, ``FixedMotherConsumers.original_inquiry,
    ``FixedMotherConsumers.original_process, ``FixedMotherConsumers.original_physical_seal_and_whole_law,
    ``FixedMotherConsumers.original_physical_tick_and_history]
  let mouth := ``FixedMotherRealization.root_admission_fixed_mother_complete_realization
  for name in controls do
    let some info := env.checked.get.find? name | throwError "MISSING_CONTROL {name}"
    let some value := info.value? true | throwError "MISSING_CONTROL_VALUE {name}"
    let refs := value.getUsedConstantsAsSet
    unless refs.contains mouth do throwError "DOES_NOT_DIRECTLY_CONSUME_SINGLE_MOUTH {name}"
    for forbidden in [``MotherAdmittedWorld.every_state, ``MotherCompleteInquiry.every_source,
        ``MotherMacroSource.every_source, ``MotherAdmittedWorld.Origin.consumers_recovers,
        ``MotherMacroSource.Origin.ask_recovers, ``MotherMacroSource.Origin.runtime_tick,
        ``MotherMacroSource.Origin.runtime_history] do
      if refs.contains forbidden then throwError "BYPASSED_SINGLE_MOUTH {name} {forbidden}"
  let closure := recoveryClosure env controls
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "CONTROL_UNCHECKED {name}"
    if info.isUnsafe || info.isPartial then throwError "CONTROL_UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "CONTROL_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "CONTROL_MISSING_VALUE {name}"
    | _ => pure ()
  unless closure.contains ``SaturationMonoid.PhysicsCore.Stage10.Runtime.sameOccurrenceActivation do
    throwError "COMPLETE_ORIGINAL_ACTIVATION_MISSING"
  logInfo m!"FIXED_MOTHER_CONSUMERS count={controls.length} single_mouth=1 closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0 full_metadata=1"
'''
p.write_text(s)

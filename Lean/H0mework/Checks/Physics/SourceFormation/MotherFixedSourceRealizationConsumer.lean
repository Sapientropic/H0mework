import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.FixedMother.CompleteRealization
import Lean

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherConsumers
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion ZeroLawRootAdmission
open FixedMotherRealization Stage9C.Revision
noncomputable section

theorem original_world (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (root : SourceNativeAuthoritativeRootClosure N V) (state : LawfulWorldStateAt root) :
    ∃ origin : MotherAdmittedWorld.Origin (⟨V, root, state⟩ : MotherAdmittedWorld.StateAt N),
      origin.material ∈ closure (Set.range (lowProgramme origin.rank)) ∧
      MotherAdmittedWorld.formState origin.presentation.restrictHeader
        (MotherArenaHigher.split origin.rank origin.material).2 = some ⟨V, root, state⟩ ∧
      origin.world = ⟨N, V, root, state⟩ ∧
      HEq origin.read.2.2.registeredOccurrence.2.wholeLedgerWriteBack
        state.registeredOccurrence.2.wholeLedgerWriteBack ∧
      HEq (origin.read.2.1.toRoot.evolutionAt origin.read.2.2.current).nextCurrent?
        (root.toRoot.evolutionAt state.current).nextCurrent? := by
  obtain ⟨origin, realized⟩ := root_admission_fixed_mother_complete_realization.1 N V root state
  exact ⟨origin, realized.formation, realized.formed, realized.world, realized.wholeLedger, realized.next⟩

theorem original_inquiry (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ origin : MotherCompleteInquiry.Origin state,
      origin.material ∈ closure (Set.range (highProgramme origin.rank)) ∧
      ParentsRetained origin.highRank origin.lowRank ∧
      origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ ∧
      origin.clauses = MotherNativeClause.ofState state ∧
      ∀ event : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit,
        ∀ query : state.Query, HEq ((origin.clauses query).program.compile event) (state.compileInquiry query) := by
  obtain ⟨origin, realized⟩ := root_admission_fixed_mother_complete_realization.2.1 N V state
  exact ⟨origin, realized.formation, realized.parents, realized.world, realized.clauses, realized.everyEvent⟩

theorem original_process (original : SourceNativeInquiryEngineProcess.{0}) :
    ∃ origin : MotherMacroSource.Origin original,
      origin.material ∈ closure (Set.range (highProgramme origin.rank)) ∧
      ParentsRetained origin.highRank origin.lowRank ∧
      origin.form = some origin.process ∧ origin.restrict = original ∧
      origin.restrict.State = original.State ∧ HEq origin.restrict.stateAt original.stateAt ∧
      HEq origin.restrict.initial original.initial ∧ HEq origin.restrict.successorAt original.successorAt ∧
      ∀ index : origin.process.State, ∀ query : (origin.process.stateAt index).Query,
        HEq (MotherRegistryRecovery.compile (origin.process.stateAt index) query)
          (MotherRegistryRecovery.compile (original.stateAt (origin.presentation.state index))
            (origin.presentation.query index query)) := by
  obtain ⟨origin, realized⟩ := root_admission_fixed_mother_complete_realization.2.2 original
  exact ⟨origin, realized.formation, realized.parents, realized.formed, realized.process,
    realized.states, realized.stateAt, realized.initial, realized.successorAt, realized.compile⟩

theorem original_physical_seal_and_whole_law :
    ∃ origin : MotherMacroSource.Origin physicalInquiryProcess,
      HighFormation origin.rank origin.material ∧
      let state := physicalInquiryRuntime.stateAt 16
      let same := origin.restrict_eq.symm
      let actual := (MotherMacroRuntime.transportEngine same state.engine).ask
        (MotherMacroRuntime.transportActivation same state.activation)
      let prior := state.engine.ask state.activation
      let law := MotherMacroRuntime.transportLaw same physicalInquiryRuntime.activationLaw
      HEq actual prior ∧ actual.next = MotherMacroRuntime.transportEngine same prior.next ∧
      HEq law physicalInquiryRuntime.activationLaw ∧
      HEq law.initial physicalInquiryRuntime.activationLaw.initial ∧
      HEq law.nextAt physicalInquiryRuntime.activationLaw.nextAt := by
  obtain ⟨origin, realized⟩ := root_admission_fixed_mother_complete_realization.2.2 physicalInquiryProcess
  obtain ⟨ask, next⟩ := realized.ask (physicalInquiryRuntime.stateAt 16).engine
    (physicalInquiryRuntime.stateAt 16).activation
  obtain ⟨law, initial, nextAt⟩ := realized.law physicalInquiryRuntime.activationLaw
  exact ⟨origin, realized.formation, ask, next, law, initial, nextAt⟩

theorem original_physical_tick_and_history (depth : Nat) :
    ∃ origin : MotherMacroSource.Origin physicalInquiryProcess,
      HighFormation origin.rank origin.material ∧
      let same := origin.restrict_eq.symm
      let actual := (MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt 16)).tick
      HEq actual Runtime.tick ∧
      actual.nextState = MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt 17) ∧
      (origin.runtime physicalInquiryRuntime).stateAt depth =
        MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt depth) ∧
      HEq ((origin.runtime physicalInquiryRuntime).tickAt depth) (physicalInquiryRuntime.tickAt depth) ∧
      ((origin.runtime physicalInquiryRuntime).tickAt depth).nextState =
        MotherMacroRuntime.transportState same (physicalInquiryRuntime.tickAt depth).nextState ∧
      Runtime.visit = SpinPair.visit 10 ∧ Runtime.SameOccurrenceActivation := by
  obtain ⟨origin, realized⟩ := root_admission_fixed_mother_complete_realization.2.2 physicalInquiryProcess
  obtain ⟨tick, nextState⟩ := realized.tick physicalInquiryRuntime (physicalInquiryRuntime.stateAt 16)
  obtain ⟨state, history, nextHistory⟩ := realized.history physicalInquiryRuntime depth
  exact ⟨origin, realized.formation, tick, nextState, state, history, nextHistory,
    rfl, Runtime.sameOccurrenceActivation⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FixedMotherConsumers

open Lean Elab Command
open SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
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

import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.MacroProcess.Operations.Consumer
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.InquiryPrograms
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.MacroProcess.Nodes.Source
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.MacroProcess.Runtime.Canonical
import SaturationMonoid.PhysicsCore.Stage10.Runtime.Activation
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.MacroProcess.Consumer
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroOperationsControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherMacroOperations Stage9C.Revision
noncomputable section

def OnGivenNodes (original : SourceNativeInquiryEngineProcess.{0}) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ domain : MotherArenaHigher.Material rank,
    ∃ state : State domain ≃ original.State,
    ∃ event : Event (fun current => original.stateAt (state current)) ↪ MotherArenaHigher.Base rank,
    ∃ material : MotherArenaHigher.Material rank,
    ∃ available : (formProcess domain (fun current => original.stateAt (state current)) event material).isSome,
    ∃ presentation : MotherRegistryRecovery.Presentation
      ((formProcess domain (fun current => original.stateAt (state current)) event material).get available) original,
      restrict presentation = original ∧ HEq (restrict presentation).successorAt original.successorAt

theorem whole_given_node_family (original : SourceNativeInquiryEngineProcess.{0}) : OnGivenNodes original := by
  obtain ⟨rank, domain, state, event, _fieldsMaterial, _fieldsFormed⟩ :=
    every_indexed_fields original.State original.stateAt original.initial
      (fun current query => (original.successorAt current query).val)
  obtain ⟨material, available, presentation, recovered, nextRecovered⟩ :=
    every_original_on_nodes_consumed domain (fun current => original.stateAt (state current)) event
      original state (fun _ => rfl)
  exact ⟨rank, domain, state, event, material, available, presentation, recovered, nextRecovered⟩

def prior : RootInquiryStatePresentation :=
  ⟨_, _, RootInquiryEngineStateAt.create (SpinPair.readInquiryState 10)⟩

def nodes : Option Bool → RootInquiryProcessNode
  | none => .active prior
  | some _ => .answered prior PUnit.unit

def repeatedAnswered (selected : Bool) : SourceNativeInquiryEngineProcess where
  State := Option Bool
  stateAt := nodes
  erase_injective := by
    intro left right leftState rightState leftActive rightActive _erased
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some _ => cases rightActive
    | some _ => cases leftActive
  initial := none
  successorAt := by
    intro state query
    cases state with
    | none =>
        change PUnit at query
        cases query
        exact ⟨some selected, rfl, trivial⟩
    | some _ =>
        change PEmpty at query
        exact nomatch query

theorem duplicate_answered_and_unvisited_state_retained (selected : Bool) :
    OnGivenNodes (repeatedAnswered selected) ∧
    (repeatedAnswered selected).stateAt (some false) = (repeatedAnswered selected).stateAt (some true) ∧
    (some false : (repeatedAnswered selected).State) ≠ some true ∧
    ((repeatedAnswered selected).successorAt none PUnit.unit).val = some selected :=
  ⟨whole_given_node_family _, rfl, by decide, rfl⟩

private theorem successor_heq_of_process_eq {first last : SourceNativeInquiryEngineProcess}
    (same : first = last) : HEq first.successorAt last.successorAt := by
  cases same
  rfl

theorem same_erasure_different_successor_index :
    (nodes (some false)).erase = (nodes (some true)).erase ∧
    repeatedAnswered false ≠ repeatedAnswered true := by
  refine ⟨rfl, ?_⟩
  intro same
  have whole : HEq (repeatedAnswered false).successorAt (repeatedAnswered true).successorAt :=
    successor_heq_of_process_eq (first := repeatedAnswered false) (last := repeatedAnswered true) same
  have successors : (repeatedAnswered false).successorAt = (repeatedAnswered true).successorAt :=
    eq_of_heq whole
  have indices := congrArg Subtype.val (congrFun (congrFun successors none) PUnit.unit)
  change (some false : Option Bool) = some true at indices
  cases indices

theorem original_single_inquiry_process : OnGivenNodes prior.oneShotProcess :=
  whole_given_node_family _

theorem invalid_duplicate_active_registry_rejected :
    ∃ rank : Ordinal.{0}, ∃ domain : MotherArenaHigher.Material rank,
      ∃ state : State domain ≃ Bool,
      ∃ event : Event (fun _ : State domain => RootInquiryProcessNode.active prior) ↪ MotherArenaHigher.Base rank,
      ∃ material : MotherArenaHigher.Material rank,
        formFields domain (fun _ => RootInquiryProcessNode.active prior) event material =
          some ⟨state.symm false, fun _ _ => state.symm false⟩ ∧
        formProcess domain (fun _ => RootInquiryProcessNode.active prior) event material = none := by
  obtain ⟨rank, domain, state, event, material, formed⟩ :=
    every_indexed_fields Bool (fun _ => RootInquiryProcessNode.active prior) false (fun _ _ => false)
  have invalid : ¬ Admissible domain (fun _ => RootInquiryProcessNode.active prior)
      (⟨state.symm false, fun _ _ => state.symm false⟩ : Fields (fun _ : State domain => RootInquiryProcessNode.active prior)) := by
    intro accepted
    have equal := accepted.1 (left := state.symm false) (right := state.symm true) rfl rfl rfl
    have impossible := congrArg state equal
    simp only [Equiv.apply_symm_apply] at impossible
    cases impossible
  refine ⟨rank, domain, state, event, material, formed, ?_⟩
  simp only [formProcess, formed, Option.bind_some, dif_neg invalid]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroOperationsControls
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroNodesControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherMacroNodes Stage9C.Revision
open scoped Classical
noncomputable section

def Joined (node : RootInquiryProcessNode.{0}) : Prop :=
  ∃ origin : Origin node,
    origin.read = node ∧
    MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank () origin.material = origin.inquiry.material ∧
    form origin.inquiry.readWorld (queryCode (headerOf node) origin.inquiry)
      (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () origin.material) = some node ∧
    origin.inquiry.readWorld = headerOf node

theorem all_whole_nodes (node : RootInquiryProcessNode.{0}) : Joined node := by
  obtain ⟨origin⟩ := every_node node
  refine ⟨origin, origin.read_eq, origin.retained.1, ?_, presentation_recovers (headerOf node) origin.inquiry⟩
  exact (congrArg (form origin.inquiry.readWorld (queryCode (headerOf node) origin.inquiry))
    origin.retained.2).trans origin.formed

def actionHeader : RootInquiryStatePresentation :=
  ⟨_, _, RootInquiryEngineStateAt.create SpinPair.inquiryState⟩
def answeredHeader : RootInquiryStatePresentation :=
  ⟨_, _, RootInquiryEngineStateAt.create (SpinPair.readInquiryState 10)⟩

theorem active_actual_action_whole : Joined (.active actionHeader) := all_whole_nodes _
theorem answered_keeps_complete_prior :
    Joined (.answered answeredHeader PUnit.unit) ∧
    IsEmpty ((RootInquiryProcessNode.answered answeredHeader PUnit.unit).Query) :=
  ⟨all_whole_nodes _, by change IsEmpty PEmpty; infer_instance⟩

theorem distinct_prior_queries_retained (header : RootInquiryStatePresentation.{0})
    (first last : header.Query) (different : first ≠ last)
    (firstOrigin : Origin (.answered header first)) (lastOrigin : Origin (.answered header last)) :
    firstOrigin.read ≠ lastOrigin.read := by
  rw [firstOrigin.read_eq, lastOrigin.read_eq]
  intro same
  have querySame : first = last := by cases same; rfl
  exact different querySame

abbrev ProbeRank := MotherArenaHigher.carrierRank answeredHeader.Query
def zeroMaterial : MotherArenaHigher.Material ProbeRank :=
  (MotherArenaHigher.readEquiv ProbeRank).symm (fun _ _ => 0)

theorem ambiguous_active_answered_selector_rejected :
    form answeredHeader (MotherArenaHigher.carrierAddress answeredHeader.Query) zeroMaterial = none := by
  have reader : MotherArenaHigher.read ProbeRank zeroMaterial = fun _ _ => 0 :=
    (MotherArenaHigher.readEquiv ProbeRank).apply_symm_apply _
  have relation (selection : Selection answeredHeader) :
      MotherArenaNetwork.r2 zeroMaterial 0 (MotherActionTranslation.unitAddress ProbeRank ())
        (selectionCode answeredHeader (MotherArenaHigher.carrierAddress answeredHeader.Query) selection) := by
    simp only [MotherArenaNetwork.r2, MotherArenaNetwork.bit, reader]
  have rejected : ¬ MotherArenaReceipts.NativeSection.Check
      (MotherActionTranslation.unitAddress ProbeRank)
      (fun _ => selectionCode answeredHeader (MotherArenaHigher.carrierAddress answeredHeader.Query)) zeroMaterial := by
    intro checked
    obtain ⟨chosen, _valid, unique⟩ := checked ()
    have impossible : (Sum.inl () : Selection answeredHeader) = .inr PUnit.unit :=
      (unique (.inl ()) (relation (.inl ()))).trans (unique (.inr PUnit.unit) (relation (.inr PUnit.unit))).symm
    cases impossible
  simp only [form, MotherArenaReceipts.NativeSection.form, dif_neg rejected, Option.map_none]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroNodesControls
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroRuntimeControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherMacroRuntime Stage9C.Revision
universe u

theorem existing_seals_and_whole_law {source target : SourceNativeInquiryEngineProcess.{u}}
    (same : source = target) (engine : Engine source)
    (activation : Engine.SourceNativeInquiryActivationAt engine)
    (law : Engine.SourceNativeInquiryActivationLaw source) :
    (transportEngine same engine).ask (transportActivation same activation) =
      transportOccurrence same activation (engine.ask activation) ∧
    HEq (transportLaw same law) law ∧
    HEq (transportLaw same law).initial law.initial ∧
    HEq (transportLaw same law).nextAt law.nextAt ∧
    HEq ((transportLaw same law).nextAfter (transportActivation same activation))
      (transportActivation same (law.nextAfter activation)) :=
  ⟨ask_commutes same engine activation, (law_recovers same law).1,
    (law_recovers same law).2.1, (law_recovers same law).2.2,
    nextAfter_commutes same law activation⟩

theorem original_physical_full_readouts {target : SourceNativeInquiryEngineProcess.{0}}
    (same : physicalInquiryProcess = target) :
    let actual := (transportState same (physicalInquiryRuntime.stateAt 16)).tick
    HEq actual.answer Runtime.tick.answer ∧
    HEq actual.receipt Runtime.tick.receipt ∧
    actual.next = transportEngine same Runtime.tick.next ∧
    actual.nextState = transportState same (physicalInquiryRuntime.stateAt 17) := by
  obtain ⟨_whole, _raw, _resolution, answer, receipt, _kind, next, nextState⟩ :=
    tick_readouts same (physicalInquiryRuntime.stateAt 16)
  exact ⟨answer, receipt, next, nextState⟩

theorem complete_original_finite_history {target : SourceNativeInquiryEngineProcess.{0}}
    (same : physicalInquiryProcess = target) (depth : Nat) :
    (transportRuntime same physicalInquiryRuntime).stateAt depth = transportState same (physicalInquiryRuntime.stateAt depth) ∧
    HEq ((transportRuntime same physicalInquiryRuntime).tickAt depth) (physicalInquiryRuntime.tickAt depth) ∧
    ((transportRuntime same physicalInquiryRuntime).tickAt depth).nextState =
      transportState same (physicalInquiryRuntime.tickAt depth).nextState :=
  history_commutes same physicalInquiryRuntime depth

theorem fixed_visit_and_complete_activation :
    Runtime.visit = SpinPair.visit 10 ∧ Runtime.SameOccurrenceActivation ∧
    Runtime.tick = physicalInquiryRuntime.tickAt 16 ∧ Runtime.nextTick = physicalInquiryRuntime.tickAt 17 :=
  ⟨rfl, Runtime.sameOccurrenceActivation, rfl, rfl⟩

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroRuntimeControls
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroSourceControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherMacroSource Stage9C.Revision
noncomputable section

def Produced (original : SourceNativeInquiryEngineProcess.{0}) : Prop :=
  ∃ origin : Origin original,
    origin.form = some origin.process ∧
    origin.restrict = original ∧
    HEq origin.restrict.successorAt original.successorAt ∧
    (∀ index : origin.process.State, ∀ query : (origin.process.stateAt index).Query,
      HEq (MotherRegistryRecovery.compile (origin.process.stateAt index) query)
        (MotherRegistryRecovery.compile (original.stateAt (origin.presentation.state index))
          (origin.presentation.query index query))) ∧
    (∀ index, MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank index origin.material =
      (origin.nodes index).material) ∧
    MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank () origin.material =
      MotherArenaHigher.pack origin.lower (origin.domain, origin.operations)

theorem whole_process_from_one_material (original : SourceNativeInquiryEngineProcess.{0}) : Produced original := by
  obtain ⟨origin, recovered, nextRecovered, compiled⟩ := every_original_process original
  refine ⟨origin, ?_, recovered, nextRecovered, compiled, origin.retained.1, origin.retained.2⟩
  exact (Option.some_get _).symm

def prior : RootInquiryStatePresentation :=
  ⟨_, _, RootInquiryEngineStateAt.create (SpinPair.readInquiryState 10)⟩

def nodes : Option Bool → RootInquiryProcessNode
  | none => .active prior
  | some _ => .answered prior PUnit.unit

def repeatedAnswered (selected : Bool) : SourceNativeInquiryEngineProcess where
  State := Option Bool
  stateAt := nodes
  erase_injective := by
    intro left right leftState rightState leftActive rightActive _erased
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some _ => cases rightActive
    | some _ => cases leftActive
  initial := none
  successorAt := by
    intro state query
    cases state with
    | none =>
        change PUnit at query
        cases query
        exact ⟨some selected, rfl, trivial⟩
    | some _ =>
        change PEmpty at query
        exact nomatch query

private theorem successor_heq_of_process_eq {first last : SourceNativeInquiryEngineProcess}
    (same : first = last) : HEq first.successorAt last.successorAt := by
  cases same
  rfl

private theorem same_erasure_different_successor_index :
    (nodes (some false)).erase = (nodes (some true)).erase ∧
    repeatedAnswered false ≠ repeatedAnswered true := by
  refine ⟨rfl, ?_⟩
  intro same
  have whole : HEq (repeatedAnswered false).successorAt (repeatedAnswered true).successorAt :=
    successor_heq_of_process_eq (first := repeatedAnswered false) (last := repeatedAnswered true) same
  have successors : (repeatedAnswered false).successorAt = (repeatedAnswered true).successorAt :=
    eq_of_heq whole
  have indices := congrArg Subtype.val (congrFun (congrFun successors none) PUnit.unit)
  change (some false : Option Bool) = some true at indices
  cases indices


theorem duplicate_answered_unvisited_states_preserved (selected : Bool) :
    Produced (repeatedAnswered selected) ∧
    ∃ origin : Origin (repeatedAnswered selected), ∃ first last : origin.process.State,
      first ≠ last ∧ origin.process.stateAt first = origin.process.stateAt last ∧
      origin.presentation.state first = some false ∧
      origin.presentation.state last = some true := by
  refine ⟨whole_process_from_one_material _, ?_⟩
  obtain ⟨origin⟩ := every_source (repeatedAnswered selected)
  let first := origin.presentation.state.symm (some false)
  let last := origin.presentation.state.symm (some true)
  refine ⟨origin, first, last, ?_, ?_, origin.presentation.state.apply_symm_apply _, origin.presentation.state.apply_symm_apply _⟩
  · intro same
    have impossible : (some false : Option Bool) = some true :=
      origin.presentation.state.symm.injective same
    cases impossible
  · have leftNode : origin.process.stateAt first = nodes (some false) :=
      (origin.presentation.node first).trans
        (congrArg (repeatedAnswered selected).stateAt (origin.presentation.state.apply_symm_apply _))
    have rightNode : origin.process.stateAt last = nodes (some true) :=
      (origin.presentation.node last).trans
        (congrArg (repeatedAnswered selected).stateAt (origin.presentation.state.apply_symm_apply _))
    exact leftNode.trans rightNode.symm

theorem same_erasure_different_generated_successor_indices :
    ∃ first : Origin (repeatedAnswered false), ∃ last : Origin (repeatedAnswered true),
      (nodes (some false)).erase = (nodes (some true)).erase ∧ first.restrict ≠ last.restrict := by
  obtain ⟨first⟩ := every_source (repeatedAnswered false)
  obtain ⟨last⟩ := every_source (repeatedAnswered true)
  refine ⟨first, last, rfl, ?_⟩
  rw [first.restrict_eq, last.restrict_eq]
  exact same_erasure_different_successor_index.2

theorem missing_family_member_rejected (ranks : Bool → Ordinal.{3}) (low : Unit → Ordinal.{0})
    (material : MotherReceiptHigher.Material (MotherMaterialJoin.Mixed.sharedRank ranks low))
    (node : RootInquiryProcessNode.{0}) :
    MotherMacroFamily.formNodes ranks low (fun index _ => if index then none else some node) material = none := by
  have unavailable : ¬ ∀ index, ((fun (index : Bool) (_ : MotherReceiptHigher.Material (ranks index)) =>
      if index then none else some node) index (MotherMaterialJoin.Mixed.restrictHigh ranks low index material)).isSome := by
    intro all
    have bad := all true
    simp at bad
  exact dif_neg unavailable

def physicalOrigin : Origin physicalInquiryProcess := Classical.choice (every_source physicalInquiryProcess)

theorem actual_physical_ask_and_whole_law :
    let state := physicalInquiryRuntime.stateAt 16
    let same := physicalOrigin.restrict_eq.symm
    let actual := (MotherMacroRuntime.transportEngine same state.engine).ask
      (MotherMacroRuntime.transportActivation same state.activation)
    let prior := state.engine.ask state.activation
    HEq actual prior ∧ HEq actual.resolution prior.resolution ∧
    HEq actual.answer prior.answer ∧ HEq actual.receipt prior.receipt ∧
    actual.next = MotherMacroRuntime.transportEngine same prior.next ∧
    HEq (MotherMacroRuntime.transportLaw same physicalInquiryRuntime.activationLaw).initial
      physicalInquiryRuntime.activationLaw.initial ∧
    HEq (MotherMacroRuntime.transportLaw same physicalInquiryRuntime.activationLaw).nextAt
      physicalInquiryRuntime.activationLaw.nextAt := by
  obtain ⟨whole, resolution, answer, receipt, next⟩ :=
    physicalOrigin.ask_recovers (physicalInquiryRuntime.stateAt 16).engine (physicalInquiryRuntime.stateAt 16).activation
  obtain ⟨_law, initial, nextAt⟩ :=
    MotherMacroRuntime.law_recovers physicalOrigin.restrict_eq.symm physicalInquiryRuntime.activationLaw
  exact ⟨whole, resolution, answer, receipt, next, initial, nextAt⟩

theorem actual_physical_tick_and_all_history (depth : Nat) :
    let same := physicalOrigin.restrict_eq.symm
    let actual := (MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt 16)).tick
    HEq actual.answer Runtime.tick.answer ∧ HEq actual.receipt Runtime.tick.receipt ∧
    actual.nextState = MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt 17) ∧
    (physicalOrigin.runtime physicalInquiryRuntime).stateAt depth =
      MotherMacroRuntime.transportState same (physicalInquiryRuntime.stateAt depth) ∧
    HEq ((physicalOrigin.runtime physicalInquiryRuntime).tickAt depth) (physicalInquiryRuntime.tickAt depth) ∧
    ((physicalOrigin.runtime physicalInquiryRuntime).tickAt depth).nextState =
      MotherMacroRuntime.transportState same (physicalInquiryRuntime.tickAt depth).nextState ∧
    Runtime.visit = SpinPair.visit 10 ∧ Runtime.SameOccurrenceActivation := by
  obtain ⟨_whole, _raw, _resolution, answer, receipt, _kind, _next, nextState⟩ :=
    physicalOrigin.runtime_tick physicalInquiryRuntime (physicalInquiryRuntime.stateAt 16)
  obtain ⟨state, tick, nextHistory⟩ := physicalOrigin.runtime_history physicalInquiryRuntime depth
  exact ⟨answer, receipt, nextState, state, tick, nextHistory, rfl, Runtime.sameOccurrenceActivation⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MacroSourceControls
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
  let controls := [``MacroOperationsControls.whole_given_node_family, ``MacroOperationsControls.duplicate_answered_and_unvisited_state_retained, ``MacroOperationsControls.same_erasure_different_successor_index, ``MacroOperationsControls.original_single_inquiry_process, ``MacroOperationsControls.invalid_duplicate_active_registry_rejected, ``MacroNodesControls.all_whole_nodes, ``MacroNodesControls.active_actual_action_whole, ``MacroNodesControls.answered_keeps_complete_prior, ``MacroNodesControls.distinct_prior_queries_retained, ``MacroNodesControls.ambiguous_active_answered_selector_rejected, ``MacroRuntimeControls.existing_seals_and_whole_law, ``MacroRuntimeControls.original_physical_full_readouts, ``MacroRuntimeControls.complete_original_finite_history, ``MacroRuntimeControls.fixed_visit_and_complete_activation, ``MacroSourceControls.whole_process_from_one_material, ``MacroSourceControls.duplicate_answered_unvisited_states_preserved, ``MacroSourceControls.same_erasure_different_generated_successor_indices, ``MacroSourceControls.missing_family_member_rejected, ``MacroSourceControls.actual_physical_ask_and_whole_law, ``MacroSourceControls.actual_physical_tick_and_all_history]
  let closure := recoveryClosure env controls
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "CONTROL_MISSING {name}"
    if info.isUnsafe || info.isPartial then throwError "CONTROL_UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "CONTROL_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "CONTROL_MISSING_VALUE {name}"
    | _ => pure ()
  for name in controls do
    let used ← collectAxioms name
    logInfo m!"CONTROL {name} axioms={used}"
  logInfo m!"CONTROLS_PASS count={controls.length} closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0"

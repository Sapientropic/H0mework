import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.AnswerQueries.Consumer
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.InquiryPrograms
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.CompleteInquiry.Consumer
import SaturationMonoid.LivingLawRootInquiryU8CompletionRegression
import SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AnswerQueriesControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherAnswerQueries Stage9C.Revision
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {I : Type}

def Recovered (state : RootInquiryStateAt N V) (label : I → state.Query) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
    ∃ origin : Origin (rank := rank) state label,
      unpack material = origin.materials ∧
      (∀ query : state.Query, origin.queries.symm (origin.queries query) = query) ∧
      (∀ index, origin.value.1 (origin.indices index) = origin.queries (label index)) ∧
      (∀ index, origin.readLabel index = label index) ∧
      (∀ index (exactEvent : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit),
        HEq ((origin.readClauses index).program.compile exactEvent) (state.compileInquiry (label index))) ∧
      (∀ first last : I, first ≠ last → (origin.indices first).val ≠ (origin.indices last).val) ∧
      origin.readWorldCurrent = ⟨N, MotherInquirySource.currentOf state⟩ ∧
      origin.header.read = ⟨state.U7, state.calculus⟩

theorem full_query_actual_labels_and_every_event (state : RootInquiryStateAt N V)
    (label : I → state.Query)
    (answering : ∀ index, MotherInquiryAnswerClause.Answering state.calculus (label index)
      (state.compileInquiry (label index))) : Recovered state label := by
  obtain ⟨rank, material, origin, packed, _clauses, labels, world, header, _old⟩ :=
    every_answering_source N V state I label answering
  refine ⟨rank, material, origin, packed, origin.queries.symm_apply_apply,
    origin.labelsRecovered, labels, origin.compile_at_every_event, ?_, world, header⟩
  intro first last different same
  exact different (origin.indices.injective (Subtype.ext same))

theorem original_visit10_two_fragment_indices :
    Recovered (SpinPair.readInquiryState 10) (fun _ : Bool => PUnit.unit) := by
  apply full_query_actual_labels_and_every_event
  intro index
  trivial

theorem original_arbitrary_state_answering_fragment (state : RootInquiryStateAt N V) :
    Recovered state (Subtype.val : AnsweringIndex state → state.Query) := by
  obtain ⟨rank, material, origin, packed, _clauses, labels, world, header, _old⟩ :=
    every_answering_fragment N V state
  refine ⟨rank, material, origin, packed, origin.queries.symm_apply_apply,
    origin.labelsRecovered, labels, origin.compile_at_every_event, ?_, world, header⟩
  intro first last different same
  exact different (origin.indices.injective (Subtype.ext same))

theorem empty_answer_fragment_keeps_original_nonempty_query :
    IsEmpty (AnsweringIndex SpinPair.inquiryState) ∧
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ origin : Origin (rank := rank) SpinPair.inquiryState
        (Subtype.val : AnsweringIndex SpinPair.inquiryState → SpinPair.inquiryState.Query),
        unpack material = origin.materials ∧
        Nonempty (MotherAuthorityFamilies.Member origin.materials.queries) ∧
        IsEmpty (MotherAuthorityFamilies.Member origin.materials.indices) ∧
        origin.readWorldCurrent = ⟨MaterialN, MotherInquirySource.currentOf SpinPair.inquiryState⟩ := by
  have empty : IsEmpty (AnsweringIndex SpinPair.inquiryState) := ⟨by
    rintro ⟨query, answering⟩
    cases query
    exact answering⟩
  refine ⟨empty, ?_⟩
  obtain ⟨rank, material, origin, packed, _clauses, _labels, world, _header, _old⟩ :=
    every_answering_fragment MaterialN MaterialV SpinPair.inquiryState
  exact ⟨rank, material, origin, packed, ⟨origin.queries PUnit.unit⟩,
    ⟨fun index => empty.false (origin.indices.symm index)⟩, world⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AnswerQueriesControls
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CompleteInquiryControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherCompleteInquiry Stage9C.Revision
open SaturationMonoid.ProcessGame.Society
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {state : RootInquiryStateAt N V}

def Joined (origin : Origin state) : Prop :=
  MotherAnswerQueries.unpack
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank .answer origin.material) = origin.answer.materials ∧
  MotherU8Compiler.unpackParts
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank .revision origin.material) = origin.revision.parts ∧
  MotherActionQueries.readLower origin.action.originalAddress
    (MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank () origin.material) =
      MotherActionQueries.packLower origin.action.materials ∧
  (∀ index, MotherActionQueries.readChild
    (MotherMaterialJoin.Mixed.restrictHigh origin.highRank origin.lowRank () origin.material)
    (origin.action.originalAddress (origin.action.queries index).val) = origin.action.targetMaterials index) ∧
  formMixed state origin.answer.readClauses origin.action.readClauses origin.revision.readClause origin.queryCode origin.indexCode
    (MotherMaterialJoin.Mixed.restrictLow origin.highRank origin.lowRank .routing origin.material) =
      some (MotherNativeClause.ofState state) ∧
  origin.readWorld = ⟨N, V, RootInquiryEngineStateAt.create state⟩ ∧
  (∀ query (event : ExactTemporalCausalRootEventAt state.root.toAuthoritativeRoot.toLedgerRoot state.visit),
    HEq ((origin.clauses query).program.compile event) (state.compileInquiry query))

theorem all_actual_joined_operands (origin : Origin state) : Joined origin := by
  obtain ⟨high, low⟩ := origin.all_materials_retained
  refine ⟨?_, ?_, ?_, ?_, ?_, origin.readWorld_eq, origin.compile_at_every_event⟩
  · exact (congrArg (@MotherAnswerQueries.unpack origin.answerRank) (low .answer)).trans
      (MotherAnswerQueries.unpack_pack origin.answer.materials)
  · exact (congrArg (@MotherU8Compiler.unpackParts origin.revisionRank) (low .revision)).trans
      origin.revision.material_parts
  · exact (congrArg (MotherActionQueries.readLower origin.action.originalAddress) (high ())).trans origin.action_parent
  · intro index
    exact (congrArg (fun material => MotherActionQueries.readChild material
      (origin.action.originalAddress (origin.action.queries index).val)) (high ())).trans (origin.action_children index)
  · exact (congrArg (formMixed state origin.answer.readClauses origin.action.readClauses origin.revision.readClause
      origin.queryCode origin.indexCode) (low .routing)).trans origin.routed

theorem every_original_full_inquiry (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) : ∃ origin : Origin state, Joined origin := by
  obtain ⟨origin⟩ := every_source N V state
  exact ⟨origin, all_actual_joined_operands origin⟩

theorem original_answered_visit10 : ∃ origin : Origin (SpinPair.readInquiryState 10), Joined origin :=
  every_original_full_inquiry _ _ _

theorem original_action_complete : ∃ origin : Origin SpinPair.inquiryState, Joined origin :=
  every_original_full_inquiry _ _ _

theorem original_exact_U8_complete : ∃ origin : Origin RootInquiryU8CompletionRegression.state, Joined origin :=
  every_original_full_inquiry _ _ _

theorem original_richer_U8_complete : ∃ origin : Origin M9ProofCarryingRenewalInquiryRuntime.jointState, Joined origin :=
  every_original_full_inquiry _ _ _

abbrev ProbeRank := MotherArenaHigher.carrierRank (PUnit ⊕ Bool)
def queryCode : PUnit ↪ MotherArenaHigher.Base ProbeRank :=
  Function.Embedding.inl.trans (MotherArenaHigher.carrierAddress (PUnit ⊕ Bool))
def indexCode : Bool ↪ MotherArenaHigher.Base ProbeRank :=
  Function.Embedding.inr.trans (MotherArenaHigher.carrierAddress (PUnit ⊕ Bool))
def ambiguous : MotherArenaHigher.Material ProbeRank :=
  (MotherArenaHigher.readEquiv ProbeRank).symm (fun _ _ => 0)

theorem ambiguous_routing_rejected :
    formSection (fun _ : Bool => PUnit.unit)
      (fun _ => MotherNativeClause.ofState (SpinPair.readInquiryState 10) PUnit.unit)
      queryCode indexCode ambiguous = none := by
  have readZero : MotherArenaHigher.read ProbeRank ambiguous = fun _ _ => 0 :=
    (MotherArenaHigher.readEquiv ProbeRank).apply_symm_apply _
  have relation (index : Bool) : MotherArenaNetwork.r2 ambiguous 0 (queryCode PUnit.unit) (indexCode index) := by
    simp only [MotherArenaNetwork.r2, MotherArenaNetwork.bit, readZero]
  have rejected : ¬ MotherArenaReceipts.NativeSection.Check queryCode (fun _ => indexCode) ambiguous := by
    intro checked
    obtain ⟨chosen, _valid, unique⟩ := checked PUnit.unit
    have impossible : false = true := (unique false (relation false)).trans (unique true (relation true)).symm
    cases impossible
  simp only [formSection, MotherArenaReceipts.NativeSection.form, dif_neg rejected, Option.bind_none]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CompleteInquiryControls
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
  let controls := [``AnswerQueriesControls.full_query_actual_labels_and_every_event, ``AnswerQueriesControls.original_visit10_two_fragment_indices, ``AnswerQueriesControls.original_arbitrary_state_answering_fragment, ``AnswerQueriesControls.empty_answer_fragment_keeps_original_nonempty_query, ``CompleteInquiryControls.all_actual_joined_operands, ``CompleteInquiryControls.every_original_full_inquiry, ``CompleteInquiryControls.original_answered_visit10, ``CompleteInquiryControls.original_action_complete, ``CompleteInquiryControls.original_exact_U8_complete, ``CompleteInquiryControls.original_richer_U8_complete, ``CompleteInquiryControls.ambiguous_routing_rejected]
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

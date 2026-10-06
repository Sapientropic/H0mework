import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.ActionQueries.Consumer
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.InquiryPrograms
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.U8Compiler.Consumer
import SaturationMonoid.LivingLawRootInquiryU8CompletionRegression
import SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRuntime
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.MaterialJoin.Consumers
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionQueriesControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision MotherActionQueries
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {I : Type}

def Recovered (state : RootInquiryStateAt N V) (label : I → state.Query) : Prop :=
  ∃ lower : Ordinal.{0}, ∃ upper : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material upper,
    ∃ targets : Targets state label, ∃ origin : Origin lower upper state label targets,
      unpackLower (readLower origin.originalAddress material) = origin.materials ∧
      (∀ index, readChild material (origin.originalAddress (origin.queries index).val) = origin.targetMaterials index) ∧
      context (origin.currents (.inl ())) = ⟨N, V, state.root⟩ ∧
      (∀ index, (origin.targetOrigin index).read = targets index) ∧
      (∀ index, HEq (origin.readClauses index).program.generate.output (state.compileInquiry (label index))) ∧
      (∀ first last : I, first ≠ last → (origin.queries first).val ≠ (origin.queries last).val) ∧
      Function.LeftInverse (MotherReceiptHigher.restrictArena lower upper origin.originalAddress)
        (MotherReceiptHigher.includeArena lower upper origin.originalAddress)

theorem actual_material_family (state : RootInquiryStateAt N V) (label : I → state.Query)
    (actions : ∀ index, IsAction state.calculus (label index) (state.compileInquiry (label index))) :
    Recovered state label := by
  obtain ⟨lower, upper, material, targets, origin, parent, children, _clauses, retains, _old⟩ :=
    every_action_source N V state I label actions
  refine ⟨lower, upper, material, targets, origin, ?_, children, context_eq (origin.currents (.inl ())),
    fun index => (origin.targetOrigin index).read_eq, origin.compile_recovers, ?_, retains⟩
  · rw [parent, unpack_packLower]
  · intro first last different same
    exact different (origin.queries.injective (Subtype.ext same))

theorem full_fragment_of_arbitrary_state (state : RootInquiryStateAt N V) :
    Recovered state (Subtype.val : ActionIndex state → state.Query) := by
  obtain ⟨lower, upper, material, targets, origin, parent, children, compiled, retains⟩ :=
    every_action_fragment N V state
  refine ⟨lower, upper, material, targets, origin, ?_, children, context_eq (origin.currents (.inl ())),
    fun index => (origin.targetOrigin index).read_eq, compiled, ?_, retains⟩
  · rw [parent, unpack_packLower]
  · intro first last different same
    exact different (origin.queries.injective (Subtype.ext same))

theorem duplicate_labels_keep_two_material_indices :
    Recovered SpinPair.inquiryState (fun _ : Bool => PUnit.unit) := by
  apply actual_material_family
  intro index
  trivial

theorem original_action_state_entire_record :
    ∃ lower : Ordinal.{0}, ∃ upper : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material upper,
      ∃ targets : Targets SpinPair.inquiryState id,
      ∃ origin : Origin lower upper SpinPair.inquiryState id targets,
        readLower origin.originalAddress material = packLower origin.materials ∧
        (∀ index, readChild material (origin.originalAddress (origin.queries index).val) = origin.targetMaterials index) ∧
        origin.readInquiry = ⟨MaterialV, SpinPair.inquiryState⟩ := by
  obtain ⟨lower, upper, material, targets, origin, parent, children, _same, _retains, _old⟩ :=
    every_action_source MaterialN MaterialV SpinPair.inquiryState SpinPair.inquiryState.Query id
      (fun query => by cases query; trivial)
  exact ⟨lower, upper, material, targets, origin, parent, children, origin.readInquiry_eq⟩

theorem answered_state_has_empty_action_fragment :
    IsEmpty (ActionIndex (SpinPair.readInquiryState 10)) ∧
    Recovered (SpinPair.readInquiryState 10) (Subtype.val : ActionIndex (SpinPair.readInquiryState 10) → _) := by
  refine ⟨⟨?_⟩, full_fragment_of_arbitrary_state _⟩
  rintro ⟨query, action⟩
  cases query
  exact action

theorem complete_different_child_materials {lower : Ordinal.{0}} {upper : Ordinal.{3}}
    (address : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper)
    (lowerMaterial : MotherArenaHigher.Material lower)
    (indices : Bool ↪ MotherReceiptHigher.Base upper)
    (children : Bool → MotherReceiptHigher.Material upper)
    (different : children false ≠ children true) :
    ∃ material : MotherReceiptHigher.Material upper,
      readLower address material = lowerMaterial ∧
      (∀ index, readChild material (indices index) = children index) ∧
      readChild material (indices false) ≠ readChild material (indices true) := by
  obtain ⟨material, retained, allChildren⟩ := every_material_bundle address lowerMaterial indices children
  refine ⟨material, retained, allChildren, ?_⟩
  rw [allChildren, allChildren]
  exact different

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionQueriesControls
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U8CompilerControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherU8Compiler
open Stage9C.Revision
open SaturationMonoid.ProcessGame.Society
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {I : Type}

def Recovered (state : RootInquiryStateAt N V) (label : I → state.Query) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
    ∃ data : (index : I) → Data (MotherNativeClause.ofState state (label index)),
    ∃ origin : Origin rank state label data,
      unpackParts material = origin.parts ∧
      MotherU8Revision.readHeader (origin.roots (.inl ())) = ⟨N, V, state.root⟩ ∧
      readCalculus origin.header = state.calculus ∧
      (∀ index, readCalculus (origin.face index) = (data index).core.frontier.face.calculus) ∧
      (∀ index, (childAt origin.parts.children (origin.indices index).val).face =
        ((origin.face index).demandMaterial, (origin.face index).eventMaterial, (origin.face index).compilerMaterial)) ∧
      (∀ index, MotherU8Revision.readHeader (origin.roots (.inr index)) =
        ⟨(data index).core.revision.generate.NewN, (data index).core.revision.generate.NewV,
          (data index).core.revision.generate.newLivingRoot⟩) ∧
      (∀ index, HEq (origin.readClause index).program.generate.output (state.compileInquiry (label index))) ∧
      (∀ first last : I, first ≠ last → (origin.indices first).val ≠ (origin.indices last).val) ∧
      ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
        Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
          (MotherArenaHigher.includeOriginal rank originalAddress)

theorem whole_labelled_family (state : RootInquiryStateAt N V) (label : I → state.Query)
    (u8 : ∀ index, IsU8 (state.compileInquiry (label index))) : Recovered state label := by
  obtain ⟨rank, material, data, origin, packed, _clauses, oldAddress, retained⟩ :=
    every_u8_source state I label u8
  refine ⟨rank, material, data, origin, packed,
    MotherU8Revision.readHeader_eq (origin.roots (.inl ())), readCalculus_eq origin.header,
    fun index => readCalculus_eq (origin.face index), origin.face_materials,
    fun index => MotherU8Revision.readHeader_eq (origin.roots (.inr index)),
    origin.compile_recovers, ?_, oldAddress, retained⟩
  intro first last different same
  exact different (origin.indices.injective (Subtype.ext same))

theorem arbitrary_state_u8_subfamily (state : RootInquiryStateAt N V) :
    Recovered state (Subtype.val : U8Index state → state.Query) := by
  obtain ⟨rank, material, data, origin, packed, compiled, oldAddress, retained⟩ :=
    every_u8_fragment N V state
  refine ⟨rank, material, data, origin, packed,
    MotherU8Revision.readHeader_eq (origin.roots (.inl ())), readCalculus_eq origin.header,
    fun index => readCalculus_eq (origin.face index), origin.face_materials,
    fun index => MotherU8Revision.readHeader_eq (origin.roots (.inr index)),
    compiled, ?_, oldAddress, retained⟩
  intro first last different same
  exact different (origin.indices.injective (Subtype.ext same))

theorem duplicate_labels_retain_two_face_materials :
    Recovered RootInquiryU8CompletionRegression.state (fun _ : Bool => ()) := by
  apply whole_labelled_family
  intro index
  trivial

theorem original_u8_state_complete_record :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ data : (query : RootInquiryU8CompletionRegression.state.Query) → Data
        (MotherNativeClause.ofState RootInquiryU8CompletionRegression.state query),
      ∃ origin : Origin rank RootInquiryU8CompletionRegression.state id data,
        unpackParts material = origin.parts ∧
        origin.readInquiry = ⟨RootInquiryU8CompletionRegression.V, RootInquiryU8CompletionRegression.state⟩ := by
  obtain ⟨rank, material, data, origin, packed, _clauses, _oldAddress, _retained⟩ :=
    every_u8_source RootInquiryU8CompletionRegression.state
      RootInquiryU8CompletionRegression.state.Query id (fun query => by cases query; trivial)
  exact ⟨rank, material, data, origin, packed, origin.readInquiry_eq⟩

theorem richer_original_subfamily :
    Recovered M9ProofCarryingRenewalInquiryRuntime.jointState
      (Subtype.val : U8Index M9ProofCarryingRenewalInquiryRuntime.jointState → _) :=
  arbitrary_state_u8_subfamily _

theorem answered_state_not_misclassified :
    IsEmpty (U8Index (SpinPair.readInquiryState 10)) ∧
    Recovered (SpinPair.readInquiryState 10) (Subtype.val : U8Index (SpinPair.readInquiryState 10) → _) := by
  refine ⟨⟨?_⟩, arbitrary_state_u8_subfamily _⟩
  rintro ⟨query, u8⟩
  cases query
  exact u8

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U8CompilerControls
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MaterialJoinControls
open scoped Classical
noncomputable section

abbrev highRanks (_ : Bool) : Ordinal.{3} := 0
abbrev lowRanks (_ : Nat) : Ordinal.{0} := 0
def highProfile (index : Bool) (_ : MotherReceiptHigher.Base (0 : Ordinal.{3})) (coordinate : Nat) : ℝ :=
  coordinate + if index then 41 else 37
def lowProfile (index : Nat) (_ : MotherArenaHigher.Base (0 : Ordinal.{0})) (coordinate : Nat) : ℝ :=
  index + coordinate

def highMaterials (index : Bool) : MotherReceiptHigher.Material (highRanks index) :=
  (MotherReceiptHigher.readEquiv 0).symm (highProfile index)
def lowMaterials (index : Nat) : MotherArenaHigher.Material (lowRanks index) :=
  (MotherArenaHigher.readEquiv 0).symm (lowProfile index)
abbrev merged := MotherMaterialJoin.Mixed.combine highRanks lowRanks highMaterials lowMaterials

theorem high_read_profile (index : Bool) : MotherReceiptHigher.read 0 (highMaterials index) = highProfile index :=
  (MotherReceiptHigher.readEquiv 0).apply_symm_apply _
theorem low_read_profile (index : Nat) : MotherArenaHigher.read 0 (lowMaterials index) = lowProfile index :=
  (MotherArenaHigher.readEquiv 0).apply_symm_apply _

theorem infinite_family_whole_materials :
    (fun index => MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks index merged) = highMaterials ∧
    (fun index => MotherMaterialJoin.Mixed.restrictLow highRanks lowRanks index merged) = lowMaterials ∧
    (∀ index base coordinate,
      MotherReceiptHigher.read 0 (MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks index merged) base coordinate = highProfile index base coordinate) ∧
    (∀ index base coordinate,
      MotherArenaHigher.read 0 (MotherMaterialJoin.Mixed.restrictLow highRanks lowRanks index merged) base coordinate = lowProfile index base coordinate) := by
  have recovered := MotherMaterialJoin.Mixed.whole_family_leftInverse highRanks lowRanks (highMaterials, lowMaterials)
  refine ⟨congrArg Prod.fst recovered, congrArg Prod.snd recovered, ?_, ?_⟩
  · intro index base coordinate
    rw [MotherMaterialJoin.Mixed.restrictHigh_combine, high_read_profile]
  · intro index base coordinate
    rw [MotherMaterialJoin.Mixed.restrictLow_combine, low_read_profile]

def probe : MotherReceiptHigher.Base (0 : Ordinal.{3}) :=
  (MotherReceiptHigher.baseReadEquiv 0).symm (fun _ _ => 0)

theorem distinct_high_materials_retained :
    MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks false merged ≠
      MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks true merged := by
  intro equal
  have sampled := congrFun (congrFun (congrArg (MotherReceiptHigher.read 0) equal) probe) 0
  rw [MotherMaterialJoin.Mixed.restrictHigh_combine, MotherMaterialJoin.Mixed.restrictHigh_combine,
    high_read_profile, high_read_profile] at sampled
  norm_num [highProfile] at sampled

def fullConsumer (material : MotherReceiptHigher.Material (0 : Ordinal.{3})) :
    Option (ULift.{9} (MotherReceiptHigher.Base (0 : Ordinal.{3}) → Nat → ℝ)) :=
  some ⟨MotherReceiptHigher.read 0 material⟩

theorem high_universe_whole_output (index : Bool) :
    MotherMaterialJoin.Mixed.getHigh highRanks lowRanks highMaterials lowMaterials index fullConsumer (by rfl) =
      ULift.up.{9} (highProfile index) := by
  exact (MotherMaterialJoin.Mixed.getHigh_eq highRanks lowRanks highMaterials lowMaterials
    index fullConsumer (by rfl)).trans (congrArg ULift.up (high_read_profile index))

def selecting (material : MotherReceiptHigher.Material (0 : Ordinal.{3})) : Option ℝ :=
  if MotherReceiptHigher.read 0 material probe 0 = 37 then some 37 else none

theorem successful_and_rejected_outputs :
    selecting (MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks false merged) = some 37 ∧
    selecting (MotherMaterialJoin.Mixed.restrictHigh highRanks lowRanks true merged) = none := by
  constructor
  · rw [MotherMaterialJoin.Mixed.restrictHigh_combine]
    norm_num [selecting, high_read_profile, highProfile]
  · rw [MotherMaterialJoin.Mixed.restrictHigh_combine]
    norm_num [selecting, high_read_profile, highProfile]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MaterialJoinControls
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
  let controls := [``ActionQueriesControls.actual_material_family, ``ActionQueriesControls.full_fragment_of_arbitrary_state, ``ActionQueriesControls.duplicate_labels_keep_two_material_indices, ``ActionQueriesControls.original_action_state_entire_record, ``ActionQueriesControls.answered_state_has_empty_action_fragment, ``ActionQueriesControls.complete_different_child_materials, ``U8CompilerControls.whole_labelled_family, ``U8CompilerControls.arbitrary_state_u8_subfamily, ``U8CompilerControls.duplicate_labels_retain_two_face_materials, ``U8CompilerControls.original_u8_state_complete_record, ``U8CompilerControls.richer_original_subfamily, ``U8CompilerControls.answered_state_not_misclassified, ``MaterialJoinControls.infinite_family_whole_materials, ``MaterialJoinControls.distinct_high_materials_retained, ``MaterialJoinControls.high_universe_whole_output, ``MaterialJoinControls.successful_and_rejected_outputs]
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

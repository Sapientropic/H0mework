import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.ProgramConsumer
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.AtRank
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.Action
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.U8Revision.Consumer
import SaturationMonoid.LivingLawRootInquiryU8CompletionRegression
import SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8Revision
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionTargetControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
local notation "Program" => SourceNativeSequentialActualActionProgramAt root visit entry authority
local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit
  (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) entry authority

theorem receipt_heq_of_eq {first last : Target} (same : first = last) : HEq first.receipt last.receipt := by
  cases same
  rfl

def FullyConsumed (original : Program) (actual : Target) : Prop :=
  actual = MotherNativeAction.read original ∧ MotherNativeAction.restore actual = original ∧
  ∀ {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {oldTheory : TheoryState N} {Query : Type} {query : Query}
    {InquiryEvent : Type 1} {event : InquiryEvent}
    (exactEvent : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit)
    (generated : SourceGeneratedSequentialActualActionAt original exactEvent),
    (SourceNativeInquiryCompilationAt.actualAction
      ((MotherNativeAction.restore actual).generate exactEvent) :
        SourceNativeInquiryCompilationAt root visit U7 calculus oldTheory query event entry authority) =
      .actualAction generated

def Recovered (original : Program) {oldRank : Ordinal.{0}}
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) N)
    (newCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) (MotherNativeAction.read original).TargetN)
    (oldOccurrence : MotherActionBody.SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base oldRank)
    (newOccurrence : MotherActionBody.TargetOccurrence (MotherNativeAction.read original).targetRoot ↪ MotherArenaHigher.Base oldRank) : Prop :=
  ∃ rank : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material rank,
    ∃ address : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank,
    ∃ available : (MotherReceiptPayload.formJoint material).isSome,
    ∃ receipt : MotherReceiptPayload.Presentation (MotherNativeAction.read original).Answer
      (MotherNativeAction.read original).Receipt
      ⟨(MotherNativeAction.read original).answer, (MotherNativeAction.read original).receipt⟩
      ((MotherReceiptPayload.formJoint material).get available),
    ∃ bodyAvailable : (MotherActionBody.form
      (event := root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) (entry := entry)
      (MotherNativeAction.read original).targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
      (MotherReceiptPayload.readArena oldRank address material)).isSome,
    FullyConsumed original (MotherActionBody.assemble
      ((MotherActionBody.form
        (event := root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit) (entry := entry)
        (MotherNativeAction.read original).targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
        (MotherReceiptPayload.readArena oldRank address material)).get bodyAvailable)
      (MotherNativeAction.read original).Answer (MotherNativeAction.read original).Receipt receipt.restrict)

theorem all_exact_events_from_actual_material (original : Program) {oldRank : Ordinal.{0}}
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) N)
    (newCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) (MotherNativeAction.read original).TargetN)
    (oldOccurrence : MotherActionBody.SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base oldRank)
    (newOccurrence : MotherActionBody.TargetOccurrence (MotherNativeAction.read original).targetRoot ↪ MotherArenaHigher.Base oldRank) :
    Recovered original oldCoordinates newCoordinates oldOccurrence newOccurrence := by
  obtain ⟨rank, material, address, available, receipt, bodyAvailable, same⟩ :=
    MotherActionBody.every_target_fields (MotherNativeAction.read original)
      oldCoordinates newCoordinates oldOccurrence newOccurrence
  refine ⟨rank, material, address, available, receipt, bodyAvailable, same,
    MotherActionBody.program_recovers original _ same, ?_⟩
  intro U7 calculus oldTheory Query query InquiryEvent event exactEvent generated
  exact MotherActionBody.compilation_recovers original _ same exactEvent generated

def coordinatesFromTotal {rank : Ordinal.{0}} {network : WorldRelationNetwork.{0}}
    (address : MotherNetworkOrigin.Total network ↪ MotherArenaHigher.Base rank) :
    MotherActionTranslation.Coordinates (rank := rank) network :=
  let encoding := MotherArenaNetworkOrigin.Encoding.ofTotal address
  { support := encoding.support
    anchor := encoding.anchor
    incidence := encoding.incidence
    lineage := encoding.lineage
    responsibility := encoding.responsibility
    claim := encoding.claim
    entry := fun support => (Function.Embedding.sigmaMk support).trans encoding.openAt
    holds := encoding.holdsAt
    disposition := encoding.dispositionAt }

abbrev SpinOldOccurrence := MotherActionBody.SourceOccurrence
  (root := materialLivingRoot) (visit := SpinPair.sourceVisit)
abbrev SpinNewOccurrence := MotherActionBody.TargetOccurrence (MotherNativeAction.read SpinPair.actionProgram).targetRoot
abbrev SpinTotal := MotherNetworkOrigin.Total MaterialN ⊕ (SpinOldOccurrence ⊕ SpinNewOccurrence)
def SpinRank := MotherArenaHigher.carrierRank SpinTotal
def spinCoordinates : MotherActionTranslation.Coordinates (rank := SpinRank) MaterialN :=
  coordinatesFromTotal (Function.Embedding.inl.trans (MotherArenaHigher.carrierAddress SpinTotal))
def spinOld : SpinOldOccurrence ↪ MotherArenaHigher.Base SpinRank :=
  (Function.Embedding.inl.trans Function.Embedding.inr).trans (MotherArenaHigher.carrierAddress SpinTotal)
def spinNew : SpinNewOccurrence ↪ MotherArenaHigher.Base SpinRank :=
  (Function.Embedding.inr.trans Function.Embedding.inr).trans (MotherArenaHigher.carrierAddress SpinTotal)

theorem actual_spin_pair_root_program_and_whole_compilation :
    Recovered SpinPair.actionProgram spinCoordinates spinCoordinates spinOld spinNew :=
  all_exact_events_from_actual_material SpinPair.actionProgram spinCoordinates spinCoordinates spinOld spinNew

abbrev SpinTarget := SourceNativeSequentialActualActionTargetAt materialLivingRoot
  SpinPair.sourceVisit SpinPair.sourceEvent SpinPair.sourceEntry SpinPair.sourceAuthority

def alternateReceipt (value : Nat) : SpinTarget :=
  { MotherNativeAction.read SpinPair.actionProgram with
      Answer := Bool, answer := true, Receipt := fun _ => ULift.{3} Nat, receipt := ⟨value⟩ }

abbrev HighTotal := ULift.{3} Bool ⊕ ((Bool × ULift.{3} Nat) ⊕ ULift.{3} (MotherArenaHigher.Base SpinRank))
def HighRank := MotherReceiptHigher.carrierRank HighTotal
def highIndex : Bool ↪ MotherReceiptHigher.Base HighRank where
  toFun := fun value => MotherReceiptHigher.carrierAddress HighTotal (.inl ⟨value⟩)
  inj' := fun _ _ same => congrArg ULift.down (Sum.inl.inj ((MotherReceiptHigher.carrierAddress HighTotal).injective same))
def highReceipt : (Sigma fun _ : Bool => ULift.{3} Nat) ↪ MotherReceiptHigher.Base HighRank where
  toFun := fun value => MotherReceiptHigher.carrierAddress HighTotal (.inr (.inl (value.1, value.2)))
  inj' := by
    intro first last same
    have pairSame := Sum.inl.inj (Sum.inr.inj ((MotherReceiptHigher.carrierAddress HighTotal).injective same))
    cases first
    cases last
    cases pairSame
    rfl
def highOriginal : MotherArenaHigher.Base SpinRank ↪ MotherReceiptHigher.Base HighRank where
  toFun := fun value => MotherReceiptHigher.carrierAddress HighTotal (.inr (.inr ⟨value⟩))
  inj' := fun _ _ same => congrArg ULift.down (Sum.inr.inj (Sum.inr.inj ((MotherReceiptHigher.carrierAddress HighTotal).injective same)))

def FixedReceiptRecovered (value : Nat) : Prop :=
  ∃ material : MotherReceiptHigher.Material HighRank,
    ∃ available : (MotherReceiptPayload.formJoint material).isSome,
    ∃ receipt : MotherReceiptPayload.Presentation Bool (fun _ => ULift.{3} Nat)
      ⟨true, ⟨value⟩⟩ ((MotherReceiptPayload.formJoint material).get available),
    ∃ bodyAvailable : (MotherActionBody.form
      (root := materialLivingRoot) (visit := SpinPair.sourceVisit)
      (event := SpinPair.sourceEvent) (entry := SpinPair.sourceEntry)
      (alternateReceipt value).targetRoot spinCoordinates spinCoordinates spinOld spinNew
      (MotherReceiptPayload.readArena SpinRank highOriginal material)).isSome,
    let actual := MotherActionBody.assemble
      ((MotherActionBody.form
        (root := materialLivingRoot) (visit := SpinPair.sourceVisit)
        (event := SpinPair.sourceEvent) (entry := SpinPair.sourceEntry)
        (alternateReceipt value).targetRoot spinCoordinates spinCoordinates spinOld spinNew
        (MotherReceiptPayload.readArena SpinRank highOriginal material)).get bodyAvailable)
      Bool (fun _ => ULift.{3} Nat) receipt.restrict
    actual = alternateReceipt value ∧ HEq actual.receipt (ULift.up.{3} value)

theorem fixed_rank_complete_receipt (value : Nat) : FixedReceiptRecovered value := by
  obtain ⟨material, available, receipt, bodyAvailable, same⟩ :=
    MotherActionBody.target_fields_at (alternateReceipt value) spinCoordinates spinCoordinates
      spinOld spinNew highIndex highReceipt highOriginal
  refine ⟨material, available, receipt, bodyAvailable, same, ?_⟩
  exact receipt_heq_of_eq same

theorem two_distinct_nontrivial_receipts_same_rank :
    FixedReceiptRecovered 37 ∧ FixedReceiptRecovered 41 ∧ (37 : Nat) ≠ 41 :=
  ⟨fixed_rank_complete_receipt 37, fixed_rank_complete_receipt 41, by decide⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionTargetControls
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U8RevisionControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open SaturationMonoid.ProcessGame.Society
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {oldTheory : TheoryState N} {Query : Type} {query : Query}
    {Event : Type 1} {event : Event}
    {entry : OpenResponsibilityAt N (MotherInquiryAnswerOperands.Support root visit)}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    {obstruction : N.ObstructionAt (MotherInquiryAnswerOperands.Support root visit)}
    {gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "Core" => SourceGeneratedInquiryU8RevisionCoreAt root visit U7 calculus oldTheory query event entry authority obstruction gate failure

def Consumed (core : Core) : Prop :=
  ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
    ∃ origin : MotherU8Revision.SourceOrigin (⟨V, root, visit⟩ : SourceNativeLivingRootCurrentAt N) core.revision (rank := rank),
      MotherArenaHigher.split rank material = (origin.familyMaterial, origin.bodyMaterial) ∧
      MotherU8Revision.readHeader origin.oldCurrent = ⟨N, V, root⟩ ∧
      MotherU8Revision.readHeader origin.newCurrent =
        ⟨core.revision.generate.NewN, core.revision.generate.NewV, core.revision.generate.newLivingRoot⟩ ∧
      origin.read = core.revision ∧
      (SourceNativeInquiryCompilationAt.requiresU8 obstruction gate failure
        ⟨core.frontier, origin.read⟩ : SourceNativeInquiryCompilationAt root visit U7 calculus oldTheory query event entry authority) =
        .requiresU8 obstruction gate failure core ∧
      ∃ address : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
        Function.LeftInverse (MotherArenaHigher.restrictOriginal rank address)
          (MotherArenaHigher.includeOriginal rank address)

theorem complete_actual_headers_and_compilation (core : Core) : Consumed core := by
  obtain ⟨rank, material, origin, packed, same, address, retains⟩ :=
    MotherU8Revision.every_revision_source (⟨V, root, visit⟩ : SourceNativeLivingRootCurrentAt N) core.revision
  refine ⟨rank, material, origin, ?_, MotherU8Revision.readHeader_eq origin.oldCurrent,
    MotherU8Revision.readHeader_eq origin.newCurrent, same,
    MotherU8Revision.complete_branch_recovers core origin, address, retains⟩
  rw [← packed]
  exact origin.material_components

theorem original_exact_revision_source :
    Consumed RootInquiryU8CompletionRegression.generatedRevisionCore :=
  complete_actual_headers_and_compilation RootInquiryU8CompletionRegression.generatedRevisionCore

theorem original_richer_revision_source :
    Consumed M9ProofCarryingRenewalU8Revision.jointCore :=
  complete_actual_headers_and_compilation M9ProofCarryingRenewalU8Revision.jointCore

theorem both_grounding_branches_recover :
    MotherU8Revision.ground RootInquiryU8CompletionRegression.typedRevisionSource.generate =
      some RootInquiryU8CompletionRegression.typedRevisionSource ∧
    MotherU8Revision.ground M9ProofCarryingRenewalU8Revision.jointCore.revision.generate =
      some M9ProofCarryingRenewalU8Revision.jointCore.revision :=
  ⟨MotherU8Revision.ground_recovers _, MotherU8Revision.ground_recovers _⟩

theorem root_semantic_failure_rejected (network : WorldRelationNetwork.{0})
    {support : network.Support} (problem : network.ObstructionAt support) :
    letI := TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty network problem
    MotherU8Revision.uniqueMember
      (A := ActualExpressibilityFailure (TheoryState.rootSemantic network) problem) = none := by
  let := TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty network problem
  have absent : ¬ Nonempty (ActualExpressibilityFailure (TheoryState.rootSemantic network) problem) := by
    rintro ⟨impossible⟩
    exact isEmptyElim impossible
  exact dif_neg absent

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.U8RevisionControls
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
  let controls := [``ActionTargetControls.all_exact_events_from_actual_material, ``ActionTargetControls.actual_spin_pair_root_program_and_whole_compilation, ``ActionTargetControls.fixed_rank_complete_receipt, ``ActionTargetControls.two_distinct_nontrivial_receipts_same_rank, ``U8RevisionControls.complete_actual_headers_and_compilation, ``U8RevisionControls.original_exact_revision_source, ``U8RevisionControls.original_richer_revision_source, ``U8RevisionControls.both_grounding_branches_recover, ``U8RevisionControls.root_semantic_failure_rejected]
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

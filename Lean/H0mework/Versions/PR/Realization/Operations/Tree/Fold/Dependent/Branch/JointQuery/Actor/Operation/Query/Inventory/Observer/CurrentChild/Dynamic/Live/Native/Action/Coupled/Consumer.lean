import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
local instance : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
def birthCount : Nat → Nat
 | 0 => Cat.D.Parent.birthCount root visit rec U7 calculus anchor sourceStage stage
 | offset+1 => Cat.nextCount root visit rec
  (frameAt root visit rec U7 calculus anchor sourceStage stage offset) (birthCount offset)

theorem frames_succ (offset : Nat) : frameAt root visit rec U7 calculus anchor sourceStage stage (offset+1)=
 A.Shared.next (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
 (configuration root visit rec U7 calculus anchor sourceStage stage) := rfl

theorem uniform_initial : Cat.UniformAt root visit rec
 (initial root visit rec U7 calculus anchor sourceStage stage)
 (Cat.D.Parent.birthCount root visit rec U7 calculus anchor sourceStage stage) := by
 intro current supplied datum
 change SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.environmentAt root visit rec
  (A.epoch (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage))
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
   (initial root visit rec U7 calculus anchor sourceStage stage).registered
   (initial root visit rec U7 calculus anchor sourceStage stage).packetAt supplied)
  (Cat.D.coreSlot root rec) (datum,.old) (0:Fin 2)=_
 exact Cat.D.Parent.Origin.uniform_origin root visit rec U7 calculus anchor sourceStage stage _ _ datum

theorem uniform_source (offset : Nat) : Cat.UniformAt root visit rec
 (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
 (birthCount root visit rec U7 calculus anchor sourceStage stage offset) := by
 induction offset with
 | zero => exact uniform_initial root visit rec U7 calculus anchor sourceStage stage
 | succ offset previous =>
  rw [frames_succ]
  dsimp only [configuration,birthCount]
  exact Cat.uniform_next root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
   (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
   (birthCount root visit rec U7 calculus anchor sourceStage stage offset) previous

theorem actor_word_source (offset : Nat) : Cat.actorWord root visit rec
 (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
 (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))=
 Finsupp.single (Cat.D.actorAtCount root visit rec (birthCount root visit rec U7 calculus anchor sourceStage stage offset+1)) 1 :=
 Cat.actor_word_of_uniform root visit rec
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (birthCount root visit rec U7 calculus anchor sourceStage stage offset)
  (uniform_source root visit rec U7 calculus anchor sourceStage stage offset)

theorem support_source (offset : Nat) : Cat.support root visit rec
 (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
 (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))=
 [Cat.D.actorAtCount root visit rec (birthCount root visit rec U7 calculus anchor sourceStage stage offset+1)] := by
 classical
 unfold Cat.support
 rw [actor_word_source]
 simp

theorem target_root (event : Rep.Event root visit rec U7 calculus anchor sourceStage stage) :
 (targetAt root visit rec U7 calculus anchor sourceStage stage event).targetRoot=
 A.Shared.root (initial root visit rec U7 calculus anchor sourceStage stage)
  (configuration root visit rec U7 calculus anchor sourceStage stage) := rfl

theorem target_next (event : Rep.Event root visit rec U7 calculus anchor sourceStage stage) :
 (targetAt root visit rec U7 calculus anchor sourceStage stage event).targetAnswerAndNext.nextCurrent=
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (initial root visit rec U7 calculus anchor sourceStage stage).registered
  (initial root visit rec U7 calculus anchor sourceStage stage).packetAt,
 (A.Shared.root (initial root visit rec U7 calculus anchor sourceStage stage)
  (configuration root visit rec U7 calculus anchor sourceStage stage)).toAuthoritativeRoot,
 A.Shared.visit (initial root visit rec U7 calculus anchor sourceStage stage)
  (configuration root visit rec U7 calculus anchor sourceStage stage)⟩ := by
 change (A.Shared.root (initial root visit rec U7 calculus anchor sourceStage stage)
  (configuration root visit rec U7 calculus anchor sourceStage stage)).generatedNextCurrentAt
  (.finite (A.Shared.root (initial root visit rec U7 calculus anchor sourceStage stage)
   (configuration root visit rec U7 calculus anchor sourceStage stage)).toAuthoritativeRoot.toRoot.initialVisit)=_
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl

theorem source_environment_literal
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage).registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage) (current:=current)) :
 ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (Rep.configuration root visit rec U7 calculus anchor sourceStage)).reader supplied).environment =
 ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
  (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.originalConfiguration
   root visit rec U7 calculus anchor sourceStage)).reader supplied).environment := rfl

theorem compiles : (state root visit rec U7 calculus anchor sourceStage stage).compileInquiry
 (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
  (Rep.configuration root visit rec U7 calculus anchor sourceStage))=
 .debtAdmission (generatedAction root visit rec U7 calculus anchor sourceStage stage) := rfl

theorem successor_valid : (targetPresentation root visit rec U7 calculus anchor sourceStage stage).erase=
 (RootInquiryProcessNode.answered (sourcePresentation root visit rec U7 calculus anchor sourceStage stage)
  (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage))).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation root visit rec U7 calculus anchor sourceStage stage)).PreservesGeneratedLivingLawAt
  (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage))
  (.active (targetPresentation root visit rec U7 calculus anchor sourceStage stage)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid
  (sourcePresentation root visit rec U7 calculus anchor sourceStage stage)
  (targetPresentation root visit rec U7 calculus anchor sourceStage stage)
  (A.Shared.query (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
   (Rep.configuration root visit rec U7 calculus anchor sourceStage))
  (generatedAction root visit rec U7 calculus anchor sourceStage stage)
  (compiles root visit rec U7 calculus anchor sourceStage stage)
 · exact (congrArg (fun current =>
    (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World
      (initial root visit rec U7 calculus anchor sourceStage stage).registered,current⟩ : AnyAuthoritativeRootCurrent.{u}))
   (target_next root visit rec U7 calculus anchor sourceStage stage
    (SourceGeneratedInquiryReceiptAction.sourceEvent
     (Rep.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
     (Rep.configuration root visit rec U7 calculus anchor sourceStage)))).symm
 · exact HEq.rfl

theorem whole_first (event : Rep.Event root visit rec U7 calculus anchor sourceStage stage) : type_of%
 (targetAt root visit rec U7 calculus anchor sourceStage stage event).firstDestination_heq :=
 (targetAt root visit rec U7 calculus anchor sourceStage stage event).firstDestination_heq

theorem old_outcome (event : Rep.Event root visit rec U7 calculus anchor sourceStage stage)
 (projection : (Rep.old root visit rec U7 calculus anchor sourceStage stage).root.toAuthoritativeRoot.source.projectionLaw.Projection) : type_of%
 ((targetAt root visit rec U7 calculus anchor sourceStage stage event).oldOutcome_heq projection) :=
 (targetAt root visit rec U7 calculus anchor sourceStage stage event).oldOutcome_heq projection

theorem source_root : (state root visit rec U7 calculus anchor sourceStage stage).root=
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).root := rfl

theorem source_visit : (state root visit rec U7 calculus anchor sourceStage stage).visit=
 (Rep.old root visit rec U7 calculus anchor sourceStage stage).visit := rfl

theorem raw_pair_preserved (offset : Nat) (event)
 (paid : event ∈ (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.pairWritten
  root visit rec (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))).trace) :
 event ∈ (Cat.pairWritten root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset))).trace :=
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.old_pair_preserved
  root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset)) event paid)

theorem receiver_strict : type_of% (Rep.receiver_strict root visit rec U7 calculus anchor sourceStage stage) :=
 Rep.receiver_strict root visit rec U7 calculus anchor sourceStage stage
theorem actual_initial : (runtime root visit rec U7 calculus anchor sourceStage stage).initialState.engine.node=
 .active (targetPresentation root visit rec U7 calculus anchor sourceStage stage) := rfl
theorem actual_query (offset : Nat) : type_of% (A.Shared.actual_query
 (initial root visit rec U7 calculus anchor sourceStage stage)
 (configuration root visit rec U7 calculus anchor sourceStage stage) offset) := A.Shared.actual_query _ _ _
theorem actual_next (offset : Nat) : type_of% (A.Shared.actual_next
 (initial root visit rec U7 calculus anchor sourceStage stage)
 (configuration root visit rec U7 calculus anchor sourceStage stage) offset) := A.Shared.actual_next _ _ _
theorem actual_query_raw (offset : Nat) : (A.Shared.query (frameAt root visit rec U7 calculus anchor sourceStage stage offset)
 (configuration root visit rec U7 calculus anchor sourceStage stage)).raw=
 Cat.queryRaw root visit rec U7 calculus anchor (sourceSeed root visit rec U7 calculus anchor sourceStage stage)
  (A.epoch (frameAt root visit rec U7 calculus anchor sourceStage stage offset))
  (A.Shared.actualOccurrence (frameAt root visit rec U7 calculus anchor sourceStage stage offset)) := rfl
theorem inverse_recovered (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_execution
 (runtime root visit rec U7 calculus anchor sourceStage stage) (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_execution _ _ _
theorem inverse_whole (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (runtime root visit rec U7 calculus anchor sourceStage stage) (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (runtime root visit rec U7 calculus anchor sourceStage stage) (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue.Orbit
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance : ∀ slot, AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor : Nat)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Act.LowValue root visit rec) (Act.LowVar root visit rec) (Act.sort root rec))))
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=Act.LowValue root visit rec) (Var:=Act.LowVar root visit rec) (sort:=Act.sort root rec))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
variable (sourceStage stage : Nat)
theorem actual_query_raw : (A.Shared.query frame (configuration root visit rec U7 calculus anchor seed)).raw =
 queryRaw root visit rec U7 calculus anchor seed (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl
theorem born_environment : (A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)).environment
 ((A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)).old.root.emitted
  (A.Shared.nextBorn frame (configuration root visit rec U7 calculus anchor seed)).old.visit.current)=
 Act.physicalNext root visit rec (A.epoch frame) (A.Shared.actualOccurrence frame) := rfl
theorem old_pair_preserved (event) (paid : event ∈ (Act.pairWritten root visit rec seed frame actual).trace) :
 event ∈ (pairWritten root visit rec U7 calculus anchor seed frame actual).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event paid
theorem new_pair_preserved (event) (paid : event ∈ (pairAdded root visit rec U7 calculus anchor seed frame actual).trace) :
 event ∈ (pairWritten root visit rec U7 calculus anchor seed frame actual).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event paid
theorem actual_query (offset : Nat) : type_of% (A.Shared.actual_query (initial root visit rec U7 calculus anchor sourceStage stage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage) offset) := A.Shared.actual_query _ _ _
theorem actual_next (offset : Nat) : type_of% (A.Shared.actual_next (initial root visit rec U7 calculus anchor sourceStage stage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage) offset) := A.Shared.actual_next _ _ _

theorem inverse_recovered (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_execution
 (runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_execution _ _ _
theorem inverse_whole (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_write
 (runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (offset : Nat) : type_of% (SourceOperationInquiry.Context.Faces.Reverse.source_next
 (runtime root visit rec U7 calculus anchor sourceStage stage)
 (rawSource root visit rec U7 calculus anchor sourceStage stage)
 ((runtime root visit rec U7 calculus anchor sourceStage stage).stateAt offset)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _

theorem intake_successor_valid : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower.successor_valid
 (Act.Owned.sourceFrame root visit rec U7 calculus anchor sourceStage stage)
 (Act.Owned.sourceProgramme root visit rec U7 calculus anchor sourceStage)
 (sourceConfiguration root visit rec U7 calculus anchor sourceStage stage)) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower.successor_valid _ _ _
theorem intake_whole_first : type_of% (intakeAction root visit rec U7 calculus anchor sourceStage stage).target.firstDestination_heq :=
 (intakeAction root visit rec U7 calculus anchor sourceStage stage).target.firstDestination_heq

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Catalogue
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

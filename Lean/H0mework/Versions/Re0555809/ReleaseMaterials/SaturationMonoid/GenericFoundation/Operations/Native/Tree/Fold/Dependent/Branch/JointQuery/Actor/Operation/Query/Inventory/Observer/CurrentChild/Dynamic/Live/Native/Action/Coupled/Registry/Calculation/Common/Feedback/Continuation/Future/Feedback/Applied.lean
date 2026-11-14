import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Written
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Binding
import H0mework.Versions.Re0555809.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Entry
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Future.Replay
namespace Applied
namespace OriginalBinding
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action (lowBinding)
end OriginalBinding
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance sourceGroups : ∀ slot,AddCommGroup (Act.PhysicalValue root visit rec slot) := inferInstance
local instance stageGroups (n : Nat) (slot : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n slot) := Lower.groups (Act.LowValue root visit rec) n slot
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count n : Nat)
abbrev sourceBinding := Binding.at (OriginalBinding.lowBinding root visit rec) (n+1)
abbrev frame := actualFrame root visit rec U7 calculus anchor sourceStage stage count (n+1)
abbrev seed := (Lower.tailData (initial root visit rec U7 calculus anchor sourceStage stage count)
 (firstCfg root visit rec U7 calculus anchor sourceStage stage) (language root visit rec U7 calculus anchor sourceStage stage) n).2
abbrev nativeCfg := Installed.programme (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
abbrev cfg := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.configuration
 (nativeCfg root visit rec U7 calculus anchor sourceStage stage count n)
abbrev supplied := Installed.Q.actualOccurrence (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev material := Source.material (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame root visit rec U7 calculus anchor sourceStage stage count n))
 (supplied root visit rec U7 calculus anchor sourceStage stage count n)

theorem actual_value : type_of% (Read.source_value (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame root visit rec U7 calculus anchor sourceStage stage count n))
 (supplied root visit rec U7 calculus anchor sourceStage stage count n)) := Read.source_value _ _ _ _

theorem actual_inverse : type_of% (Read.source_inverse (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame root visit rec U7 calculus anchor sourceStage stage count n))
 (supplied root visit rec U7 calculus anchor sourceStage stage count n)) := Read.source_inverse _ _ _ _

theorem actual_raw : type_of% (Read.actual_raw
 (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Read.actual_raw _ _ _

theorem complete_paid (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.result (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
   (frame root visit rec U7 calculus anchor sourceStage stage count n)
   (supplied root visit rec U7 calculus anchor sourceStage stage count n)).2.1.2).trace) : type_of%
 (Ledger.all_new_paid (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n) event present) := Ledger.all_new_paid _ _ _ _ present

theorem complete_replay (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.replayTrace (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
   (frame root visit rec U7 calculus anchor sourceStage stage count n)
   (supplied root visit rec U7 calculus anchor sourceStage stage count n))).trace) : type_of%
 (Ledger.all_new_replay (sourceBinding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
  (frame root visit rec U7 calculus anchor sourceStage stage count n) event present) := Ledger.all_new_replay _ _ _ _ present

abbrev sourceReceipt := Move.generated (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)

theorem actual_whole : type_of% (sourceReceipt root visit rec U7 calculus anchor sourceStage stage count n).target.firstDestination_heq :=
 (sourceReceipt root visit rec U7 calculus anchor sourceStage stage count n).target.firstDestination_heq

theorem canonical_next : type_of% (Move.canonical_next (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Move.canonical_next _ _ _

theorem actual_target_root : type_of% (Move.target_root (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Move.target_root _ _ _

theorem actual_next_reader : type_of% (Move.next_reader (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)) := Move.next_reader _ _ _

abbrev sourceFaces := Move.sourceFaces (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev nextFaces := Move.nextFaces (sourceBinding root visit rec n)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)

end Applied
end Future.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

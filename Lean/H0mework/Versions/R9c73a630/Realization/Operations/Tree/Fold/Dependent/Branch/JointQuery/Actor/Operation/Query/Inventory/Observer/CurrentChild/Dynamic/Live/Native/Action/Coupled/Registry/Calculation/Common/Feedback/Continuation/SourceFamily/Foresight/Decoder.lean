import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Operator
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] sourceGroups
variable (binding : ∀ t,X t → Expr W X t) (state : L.State (W:=W) (X:=X) (s:=s))
def physicalDecoder (k : Nat) : Env (value binding state k) X := fun t name =>
 (recoveredCurrent binding state k t name).1+(recoveredCurrent binding state k t name).2

theorem decoder_source (k : Nat) : physicalDecoder binding state k=
 Future.Replay.Source.physicalNext (Future.Replay.Binding.at binding (stage binding state k))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k))
  (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) := by
 unfold physicalDecoder
 rw [recovered_current]
 have actual := congrArg (fun query => query.raw.environment)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated
   (frame binding state k) (cfg binding state k))
 have generated : environment binding state k=
  Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding (stage binding state k))
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k))
   (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) := actual
 funext t name
 have slot := congrArg (fun observed : Env (PairValue (value binding state k)) X =>
  (observed t name).1+(observed t name).2) generated
 apply slot.trans
 change Future.Replay.Source.environment (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k)) (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) t name+
  (Future.Replay.Source.physicalNext (Future.Replay.Binding.at binding (stage binding state k)) (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k)) (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) t name-
   Future.Replay.Source.environment (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k)) (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) t name)=_
 simpa only [← add_sub_assoc] using add_sub_cancel_left
  (Future.Replay.Source.environment
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k))
   (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) t name)
  (Future.Replay.Source.physicalNext (Future.Replay.Binding.at binding (stage binding state k))
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (frame binding state k))
   (Future.Replay.Installed.Q.actualOccurrence (frame binding state k)) t name)
end Lower.SourceFamily.Foresight
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

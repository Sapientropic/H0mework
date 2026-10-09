import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Environment.Generated
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Erasure
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
theorem receipt_packet_parent_target
 (cfg : A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s))
 (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :
 (SourceGeneratedInquiryReceiptAction.packetAt frame cfg current).targetCurrent=
 RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.targetCurrent
  frame.registered frame.packetAt current := rfl

theorem receipt_packet_parent_whole
 (cfg : A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s))
 (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :
 (SourceGeneratedInquiryReceiptAction.packetAt frame cfg current).ledgerEvolution=
 RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.whole
  frame.registered frame.packetAt current :=
 RootGeneratedDebtActivationJointSource.Successor.Inquiry.programme_whole
  frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt current

theorem receipt_original_projection
 (cfg : A.Programme (PhysicalValue:=Lower.Value W n) (PhysicalVar:=X) (sort:=s))
 (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :
 (SourceGeneratedInquiryReceiptAction.packetAt frame cfg current).targetCurrent.1=
 (frame.packetAt current.1).targetCurrent := rfl
abbrev beforeCfg:=Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding) n seed
abbrev actualCfg:=Lower.SourceFamily.cfg (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n seed
variable (index:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
theorem reader_environment :
 (((actualCfg binding n seed).datum frame).reader index.2).environment=
 (((beforeCfg binding n seed).datum frame).reader index.2).environment :=
 Lower.SourceFamily.Foresight.Contextual.Reader.raw_environment binding n seed frame index

theorem birth_callback_environment
 {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 (SourceGeneratedInquiryReceiptAction.bornFrame frame (actualCfg binding n seed)).environment supplied=
 (SourceGeneratedInquiryReceiptAction.bornFrame frame (beforeCfg binding n seed)).environment supplied :=
 reader_environment binding n seed frame ⟨current,supplied⟩

theorem actual_after_environment
 (paid:DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression)
  frame.event.state) (selected:frame.action=.inr paid) :
 SourceGeneratedInquiryReceiptAction.afterEnvironment frame (actualCfg binding n seed)=
 SourceGeneratedInquiryReceiptAction.afterEnvironment frame (beforeCfg binding n seed) :=by
 unfold SourceGeneratedInquiryReceiptAction.afterEnvironment
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 rw [selected]
 change (((actualCfg binding n seed).datum (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame.mathNext)).reader
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame.mathNext)).environment=_
 exact reader_environment binding n seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame.mathNext)
  ⟨(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame.mathNext).current,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame.mathNext⟩
end Lower.SourceFamily.Foresight.Contextual.Profile.Erasure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

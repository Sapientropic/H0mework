import H0mework.Versions.MF.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Completion.CommonRaw
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Source
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport
namespace P
export Lower.SourceFamily.Foresight.Contextual.Psi (receipt endpointFrame installedFace source_clock written cfg0)
end P
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal (receiver endpointFrame endpointFace source_clock written)
end T
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query query_generated actualOccurrence next nextBorn datum)
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end Q
namespace New
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.Installation (configuration original_reader original_decoder)
end New
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial afterEnvironment actual_updated_environment)
end R
namespace C
export Lower.SourceFamily.Foresight.Contextual (factory)
end C
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

abbrev oldRaw:=RegisteredRawTrace.raw (P.receipt binding n packet.2 packet.1).old.root.toAuthoritativeRoot
 (P.receipt binding n packet.2 packet.1).registered
abbrev newRaw:=RegisteredRawTrace.raw (T.receiver binding n packet).old.root.toAuthoritativeRoot
 (T.receiver binding n packet).registered

theorem old_endpoint:P.written binding n packet.2 packet.1=RegisteredRawTrace.rawWritten (oldRaw binding n packet):=
 RegisteredRawTrace.frame_written (P.endpointFrame binding n packet.2 packet.1)
  (P.source_clock binding n packet.2 packet.1)
theorem new_endpoint:T.written binding n packet=RegisteredRawTrace.rawWritten (newRaw binding n packet):=
 RegisteredRawTrace.frame_written (T.endpointFrame binding n packet) (T.source_clock binding n packet)

abbrev before:=packet.1
abbrev cfg:=Lower.SourceFamily.cfg (C.factory (s:=s) binding) n packet.2

private theorem configuration_same :
 P.cfg0 binding n packet.2 = cfg binding n packet := by
 rfl


abbrev actualQuery:=Q.query (before n packet) (cfg binding n packet)

theorem query_raw:(actualQuery binding n packet).raw=
 (Q.query (before n packet) (P.cfg0 binding n packet.2)).raw:=by
 have h := configuration_same binding n packet
 cases h
 rfl

theorem after_raw:(Q.query (Q.next (before n packet) (cfg binding n packet)) (cfg binding n packet)).raw.environment=
 (Q.query (Q.next (before n packet) (P.cfg0 binding n packet.2)) (P.cfg0 binding n packet.2)).raw.environment:=by
 have h := configuration_same binding n packet
 cases h
 rfl

theorem same_environment:(oldRaw binding n packet).environment=(newRaw binding n packet).environment:=by
 have h := configuration_same binding n packet
 cases h
 rfl

theorem same_expression:(oldRaw binding n packet).expression=(newRaw binding n packet).expression:=by
 have h := configuration_same binding n packet
 cases h
 rfl

theorem same_raw:oldRaw binding n packet=newRaw binding n packet:=by
 cases left:oldRaw binding n packet with
 | mk env expression=>
  cases right:newRaw binding n packet with
  | mk otherEnv otherExpression=>
   have environments:=same_environment binding n packet
   have expressions:=same_expression binding n packet
   rw [left,right] at environments expressions
   cases environments
   cases expressions
   rfl

theorem terminal_written:P.written binding n packet.2 packet.1=T.written binding n packet:=
 (old_endpoint binding n packet).trans
  ((congrArg RegisteredRawTrace.rawWritten (same_raw binding n packet)).trans
   (new_endpoint binding n packet).symm)

end Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

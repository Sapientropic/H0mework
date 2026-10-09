import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Completion
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
 (cfg material activeEnv activeExpression activeWord input_environment input_expression paidSource payment actual_claim_equation)
end Claim
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (receiver)
end Wr
namespace Sealed
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceRegisteredClaimClock
 (currentRuntime sourceRemainder sourceBudget suffixHistory current_event source_suffix_factorizes suffix_no_restart)
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock (active_remainder_positive active_clock active_suffix_completed)
end Sealed
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry
 (mathState mathAnswerFace mathConsumer math_compiles math_read)
end J
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
 (runtime event completedEvent completedRuntime completed completed_value completed_budget completed_history_length)
end C
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment (debtCurrent process debt_current_actual)
end Pay
namespace IP
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment
 (mathEntry mathCurrent debtCurrent no_paid_of_zero rowLineage canonicalSuccessor canonical_next actual_tick_receipt)
end IP
namespace FaceProjection
export SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceRegisteredClaimCompletion
 (state value debt_budget terminal_state terminal_budget terminal_fee terminal_debt_budget terminal_no_paid)
end FaceProjection
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev receiver := Wr.receiver binding n packet
abbrev budget := remaining (receiver binding n packet).registered.input.expression
abbrev endpointDepth := budget binding n packet-1
def endpointFrame := {receiver binding n packet with depth:=endpointDepth binding n packet}
abbrev completedEvent := C.completedEvent (receiver binding n packet).old.root.toAuthoritativeRoot
 (receiver binding n packet).registered (receiver binding n packet).packetAt
abbrev completed := C.completed (receiver binding n packet).old.root.toAuthoritativeRoot
 (receiver binding n packet).registered (receiver binding n packet).packetAt
abbrev endpointState := J.mathState (receiver binding n packet).old (receiver binding n packet).registered
 (receiver binding n packet).packetAt (endpointDepth binding n packet)
abbrev endpointFace := J.mathAnswerFace (receiver binding n packet).old (receiver binding n packet).registered
 (receiver binding n packet).packetAt (endpointDepth binding n packet)
abbrev answerConsumer := J.mathConsumer (receiver binding n packet).old (receiver binding n packet).registered
 (receiver binding n packet).packetAt (endpointDepth binding n packet)

theorem endpoint_clock : endpointDepth binding n packet+1=budget binding n packet := by
 have positive := Sealed.active_remainder_positive binding n packet
 have clock := Sealed.active_clock binding n packet
 change 1+Sealed.sourceRemainder (receiver binding n packet)=budget binding n packet at clock
 unfold endpointDepth
 omega

theorem endpoint_event : (endpointFrame binding n packet).event.state=(completedEvent binding n packet).state := by
 have same := Sealed.current_event (endpointFrame binding n packet)
 change (endpointFrame binding n packet).event.state=
  (C.event (receiver binding n packet).old.root.toAuthoritativeRoot
   (receiver binding n packet).registered (receiver binding n packet).packetAt
   (endpointDepth binding n packet+1)).state at same
 rw [endpoint_clock] at same
 exact same

theorem source_clock : (endpointFrame binding n packet).depth+1=
 remaining (endpointFrame binding n packet).registered.input.expression := endpoint_clock binding n packet

theorem source_endpoint_state : type_of% (FaceProjection.terminal_state (endpointFrame binding n packet)
 (source_clock binding n packet)) := FaceProjection.terminal_state _ (source_clock binding n packet)

theorem endpoint_budget : type_of% (FaceProjection.terminal_budget (endpointFrame binding n packet)
 (source_clock binding n packet)) := FaceProjection.terminal_budget _ (source_clock binding n packet)

theorem terminal_value : (completed binding n packet).1=
 (Claim.activeExpression binding n packet).eval (Claim.activeEnv binding n packet) :=
 C.completed_value (receiver binding n packet).old.root.toAuthoritativeRoot
 (receiver binding n packet).registered (receiver binding n packet).packetAt

theorem answer_value : type_of% (FaceProjection.value (endpointFrame binding n packet)) :=
 FaceProjection.value (endpointFrame binding n packet)

theorem compiled : type_of% (J.math_compiles (receiver binding n packet).old (receiver binding n packet).registered
 (receiver binding n packet).packetAt (endpointDepth binding n packet)) := J.math_compiles _ _ _ _

abbrev written := SourceOperationPaidRelations.exposure (endpointFace binding n packet).rootRead.state.2

theorem completed_fee : type_of% (FaceProjection.terminal_fee (endpointFrame binding n packet)
 (source_clock binding n packet)) := FaceProjection.terminal_fee _ (source_clock binding n packet)

abbrev endpointDebt := Pay.debtCurrent (endpointFrame binding n packet)

theorem endpoint_debt_budget : type_of% (FaceProjection.terminal_debt_budget (endpointFrame binding n packet)
 (source_clock binding n packet)) := FaceProjection.terminal_debt_budget _ (source_clock binding n packet)

theorem no_paid : type_of% (FaceProjection.terminal_no_paid (endpointFrame binding n packet)
 (source_clock binding n packet)) := FaceProjection.terminal_no_paid _ (source_clock binding n packet)

abbrev sameDebt := (endpointDebt binding n packet).sameDebt

theorem actual_tick (depth : Nat) : type_of% (IP.actual_tick_receipt (receiver binding n packet).old
 (receiver binding n packet).registered (receiver binding n packet).packetAt depth) := IP.actual_tick_receipt _ _ _ depth

theorem canonical_next : type_of% (IP.canonical_next (receiver binding n packet).old
 (receiver binding n packet).registered (receiver binding n packet).packetAt (endpointDepth binding n packet)) :=
 IP.canonical_next _ _ _ _
end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

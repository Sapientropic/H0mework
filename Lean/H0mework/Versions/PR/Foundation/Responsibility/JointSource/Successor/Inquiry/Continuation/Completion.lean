import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace SourceRegisteredClaimCompletion
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathAnswerFace)
end J
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
 (runtime event completedEvent completed_budget completed_history_length)
end C
namespace Pay
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment (debtCurrent)
end Pay
namespace Sealed
export SourceRegisteredClaimClock (current_event)
end Sealed

variable {S : Type u} {U X : S → Type u} [∀t,AddCommGroup (U t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
theorem state : (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead.state=
 frame.event.state := rfl
theorem value : (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead.value=
 frame.registered.input.expression.eval frame.registered.input.environment := frame.event.state.2.sound.symm

theorem debt_budget : (Pay.debtCurrent frame).budget=
 remaining (C.event frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)).state.1 := by
 change remaining (RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
  frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)).current.2.state.1=_
 have depth := RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime_depth
  frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)
 change _=remaining (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
  frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
  (C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1))).2.state.1
 rw [RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent,depth]
variable (clock : frame.depth+1=remaining frame.registered.input.expression)
include clock in
theorem terminal_state : (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead.state=
 (C.completedEvent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt).state :=
 (state frame).trans ((Sealed.current_event frame).trans
  (congrArg (fun count=>(C.event frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).state) clock))

include clock in
theorem terminal_budget : remaining
 (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead.state.1=0 :=
 (congrArg (fun state=>remaining state.1) (terminal_state frame clock)).trans
 (C.completed_budget frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt)

include clock in
theorem terminal_fee : (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead.state.2.length=
 remaining frame.registered.input.expression :=
 (congrArg (fun state=>state.2.length) (terminal_state frame clock)).trans
 (C.completed_history_length frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt)

include clock in
theorem terminal_debt_budget : (Pay.debtCurrent frame).budget=0 :=
 (debt_budget frame).trans
 ((congrArg (fun count=>remaining (C.event frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count).state.1) clock).trans
 (C.completed_budget frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt))

include clock in
theorem terminal_no_paid : type_of% (no_paidRootDebtMacroContinuation_of_budget_eq_zero
 (Pay.debtCurrent frame) (terminal_debt_budget frame clock)) :=
 no_paidRootDebtMacroContinuation_of_budget_eq_zero _ (terminal_debt_budget frame clock)

end SourceRegisteredClaimCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Completion
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace SourceRegisteredClaimBoundary
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathAnswerFace)
end J
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion (completed completed_value)
end C
variable {T:Type u} {U Y:T→Type u} [∀t,AddCommGroup (U t)] {sort:T}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=Y) (sort:=sort))
variable (clock:frame.depth+1=remaining frame.registered.input.expression)
abbrev face:=J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth
include clock in
theorem endpoint : (face frame).rootRead.state.1=Expr.const (face frame).rootRead.value :=by
 have state:=SourceRegisteredClaimCompletion.terminal_state frame clock
 have value:=SourceRegisteredClaimCompletion.value frame
 let completed:=C.completed frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
 have endpoint:=(completed).2.down
 have result:=C.completed_value frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
 exact (congrArg Sigma.fst state).trans (endpoint.trans (congrArg Expr.const (result.trans value.symm)))
include clock in
theorem boundary : relationMap (R:=ℤ) frame.registered.input.environment
 ((face frame).rootRead.state.2.relationWords (R:=ℤ))=
 Finsupp.single frame.registered.input.expression (1:ℤ)-
 Finsupp.single (Expr.const (face frame).rootRead.value) (1:ℤ) :=by
 have source:=((face frame).rootRead.state.2).relation_boundary (R:=ℤ)
 exact source.trans (congrArg
  (fun expression=>Finsupp.single frame.registered.input.expression (1:ℤ)-Finsupp.single expression (1:ℤ))
  (endpoint frame clock))
end SourceRegisteredClaimBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

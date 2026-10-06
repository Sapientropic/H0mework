import H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Completion

/-! The actual recursive material's paid relation, updated effect and inverse
fibre feed the next executable request of the same macro source. -/

set_option autoImplicit false
universe u r
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceGeneratedScalarDifferentialResidual RootInquiryCompletion
noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def relations := Native.ResidualRequest.relations (R := R) frame.actualMaterial

theorem relation_boundary :
    relationMap (R := R) frame.rawRead.environment (frame.relations (R := R)) =
      Finsupp.single frame.rawRead.expression (1 : R) - Finsupp.single frame.paidRead.state.1 (1 : R) :=
  Native.ResidualRequest.relation_boundary (R := R) frame.actualMaterial

theorem request_effect :
    frame.request.input.expression.eval frame.request.input.environment =
      effectEvaluator (R := R) frame.rawRead.environment
        (frame.activeEnvironment - frame.rawRead.environment)
        (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))) :=
  Native.ResidualRequest.updated_value (R := R) frame.actualMaterial

theorem request_inverse_fibre :
    (residualEquivRange (evaluation (R := R) frame.request.input.environment)
      (canonicalResidual (evaluation (R := R) frame.request.input.environment)
        (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))))).val =
      frame.request.input.expression.eval frame.request.input.environment :=
  Native.ResidualRequest.residual_value (R := R) frame.actualMaterial

theorem request_residual_zero_iff :
    canonicalResidual (evaluation (R := R) frame.request.input.environment)
        (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))) = 0 ↔
      frame.request.input.expression.eval frame.request.input.environment = 0 :=
  Native.ResidualRequest.residual_zero_iff (R := R) frame.actualMaterial

theorem relation_cochain :
    SourceOperationScalarCochain.boundary (R := R)
        (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))) ∈
      LinearMap.range (relationMap (R := R)
        (mixedEnvironment frame.rawRead.environment (frame.activeEnvironment - frame.rawRead.environment))) :=
  frame.actualMaterial.state.2.relation_cochain (R := R) frame.actualMaterial.increment

def completedRequest := Inquiry.Completion.completed frame.currentState
  (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request

theorem completed_request_effect : frame.completedRequest.1 =
    effectEvaluator (R := R) frame.rawRead.environment
      (frame.activeEnvironment - frame.rawRead.environment)
      (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))) :=
  (Inquiry.Completion.completed_value frame.currentState
    (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request).trans
    (frame.request_effect (R := R))

theorem completed_request_inverse_fibre :
    (residualEquivRange (evaluation (R := R) frame.request.input.environment)
      (canonicalResidual (evaluation (R := R) frame.request.input.environment)
        (relationMap (R := R) frame.rawRead.environment (frame.relations (R := R))))).val =
      frame.completedRequest.1 :=
  (frame.request_inverse_fibre (R := R)).trans
    (Inquiry.Completion.completed_value frame.currentState
      (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request).symm

end Frame

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

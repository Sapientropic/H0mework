import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Payment.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer

/-! Same-debt payment consumes the original whole row at the actual
activation root. Birth remains a different source-generated debt, while the
original row budget is conserved rather than refilled. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Payment
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
namespace SharedPayment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared (current_actual no_refill paidContinuation wellFounded no_paid_of_zero macro_current)
end SharedPayment
variable (frame : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev current_actual := SharedPayment.current_actual programme frame
abbrev no_refill := SharedPayment.no_refill programme frame
abbrev paidContinuation := SharedPayment.paidContinuation programme frame
abbrev wellFounded := SharedPayment.wellFounded programme frame
abbrev no_paid_of_zero := SharedPayment.no_paid_of_zero programme frame

abbrev macro_current (initial : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :=
  SharedPayment.macro_current programme initial

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

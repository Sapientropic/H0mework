import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Runtime
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Source

/-! The actual source cofaces transport the paid epoch restriction to the
activation root. The original registry state, successor and whole row are
retained; no authority is reconstructed from an erased ledger. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Payment
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (World JointV)
end J
namespace P
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Payment
  (process stateAt debtCurrent debtStep payment)
end P
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
namespace A
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root presentation)
end S
namespace SharedPayment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared (baseProcess stateAt process debtCurrent debtStep payment generatePayment process_state_preserved process_successor_preserved receipt_preserved)
end SharedPayment
variable (frame : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev baseProcess := SharedPayment.baseProcess frame
abbrev stateAt := SharedPayment.stateAt programme frame
abbrev process := SharedPayment.process programme frame
abbrev debtCurrent := SharedPayment.debtCurrent programme frame
abbrev debtStep := SharedPayment.debtStep programme frame
abbrev payment := SharedPayment.payment programme frame
abbrev generatePayment := SharedPayment.generatePayment programme frame
abbrev process_state_preserved := SharedPayment.process_state_preserved programme frame
abbrev process_successor_preserved := SharedPayment.process_successor_preserved programme frame
abbrev receipt_preserved := SharedPayment.receipt_preserved programme frame

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

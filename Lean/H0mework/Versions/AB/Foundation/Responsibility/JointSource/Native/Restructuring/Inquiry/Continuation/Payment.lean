import H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Runtime
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Payment

/-! The actual macro node restricts to the existing fixed-root debt process.
Only its generated paid branch emits a same-debt payment receipt. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution DebtActivationWorld RootInquiryCompletion
noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def debtCurrent := Inquiry.Payment.debtCurrent frame.old frame.program frame.registered frame.depth

theorem debt_current_actual :
    (⟨World frame.registered, frame.debtCurrent.rooted.erase⟩ : AnyAuthoritativeRootCurrent.{u}) =
      frame.presentation.erase := frame.presentation_erase.symm

def generatePayment : SourceOperationExecutionDebt.Settlement frame.event.state ⊕
    SourceNativeRootDebtPaymentStepAt frame.debtCurrent :=
  Inquiry.Payment.generatePayment frame.old frame.program frame.registered frame.depth

variable (paid : DebtActivationWorld.GeneratedStepAt
  (Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state)
variable (action : frame.action = .inr paid)

def paidContinuation : SourceNativePaidRootDebtMacroContinuationAt frame.debtCurrent :=
  Inquiry.Payment.paidContinuation frame.old frame.program frame.registered frame.depth paid action

include action in
theorem actual_paid_receipt :
    HEq (Inquiry.Payment.canonicalSuccessor frame.old frame.program frame.registered frame.depth).ledgerEvolution.destination
      (DebtActivationLedger.jointStepLedgerEvolution
        (law := Idle.law frame.registered.input.environment frame.registered.input.expression)
        (native frame.program frame.registered (Inquiry.mathCurrent frame.old frame.program frame.registered frame.depth)).baseLedger
        frame.event.owner paid.2).destination :=
  Inquiry.Payment.canonical_paid_receipt frame.old frame.program frame.registered frame.depth paid action

theorem no_paid_of_zero (zero : remaining frame.event.state.1 = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt frame.debtCurrent) :=
  Inquiry.Payment.no_paid_of_zero frame.old frame.program frame.registered frame.depth zero

end Frame

variable (initial : Frame (Value := Value) (Var := Var) (sort := sort))

theorem runtime_debt_current_actual (count : Nat) :
    ((runtime initial).stateAt count).engine.node.erase =
      (⟨World (frames initial count).registered,
        (frames initial count).debtCurrent.rooted.erase⟩ : AnyAuthoritativeRootCurrent.{u}) :=
  (actual_current initial count).trans
    ((frames initial count).presentation_erase.symm.trans
      (frames initial count).debt_current_actual.symm)

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

/-! The actual charged calculation pays through its own complete patch.
This is the existing OwnerFree process, read at its source-generated clock;
its receipt agrees with the mother face without replacing the mother ledger. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Noetherian
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment
  (debtCurrent debtStep payment generatePayment paidContinuation wellFounded no_refill no_paid_of_zero current_state)
end P
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualVisit)
end S
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))

abbrev old := (S.baseRoot frame chargedProgramme).toAuthoritativeRoot
abbrev origin : (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame).registered
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame).packetAt).Current := (S.actualVisit frame).current
abbrev sourceReader := commonReader frame
abbrev current (count : Nat) := P.debtCurrent (old frame) (origin frame) (sourceReader frame) count
abbrev step (count : Nat) := P.debtStep (old frame) (origin frame) (sourceReader frame) count
abbrev generatedPayment (count : Nat) := P.generatePayment (old frame) (origin frame) (sourceReader frame) count

theorem no_refill (count : Nat) : (step frame count).targetEntry.progressBudget ≤ (current frame count).budget :=
  P.no_refill (old frame) (origin frame) (sourceReader frame) count

theorem wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process:=RootGeneratedDebtActivationJointSource.OwnerFree.process (old frame) (origin frame) (sourceReader frame))
    (origin:=RootGeneratedDebtActivationJointSource.OwnerFree.Payment.entry (old frame) (origin frame) (sourceReader frame) 0)) :=
  P.wellFounded (old frame) (origin frame) (sourceReader frame)

theorem source_state (count : Nat) :
    (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit (old frame) (origin frame) (sourceReader frame) count).current =
      chargedState frame count := P.current_state (old frame) (origin frame) (sourceReader frame) count

private theorem sameWhole {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
    {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
    (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
      RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value) (Var:=Var) (sort:=sort))
    (left right : RootGeneratedDebtActivationJointSource.OwnerFree.Current old origin reader) (same : left=right) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole old origin reader left)
      (RootGeneratedDebtActivationJointSource.OwnerFree.whole old origin reader right) := by
  cases same
  rfl

theorem source_receipt (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole (old frame) (origin frame) (sourceReader frame)
      (RootGeneratedDebtActivationJointSource.OwnerFree.finiteVisit (old frame) (origin frame) (sourceReader frame) count.1).current)
      ((receipts frame).whole count) :=
  (sameWhole (old frame) (origin frame) (sourceReader frame) _ _ (source_state frame count.1)).trans
    (charged_write_receipt frame count)

def activePayment (count : Fin (remaining (receipts frame).raw.expression)) :
    SourceNativeRootDebtPaymentStepAt (current frame count.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
    (old frame) (origin frame) (sourceReader frame) count

def activeContinuation (count : Fin (remaining (receipts frame).raw.expression)) :
    SourceNativePaidRootDebtMacroContinuationAt (current frame count.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activeContinuation
    (old frame) (origin frame) (sourceReader frame) count

theorem budget (count : Nat) : (current frame count).budget =
    remaining (receipts frame).raw.expression - count :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.budget (old frame) (origin frame) (sourceReader frame) count

theorem endpoint_no_paid : IsEmpty (SourceNativePaidRootDebtMacroContinuationAt
    (current frame (remaining (receipts frame).raw.expression))) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.endpoint_no_paid (old frame) (origin frame) (sourceReader frame)

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Noetherian
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

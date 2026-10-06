import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Source

/-! Same-debt payment consumes the original whole row at the actual
activation root. Birth remains a different source-generated debt, while the
original row budget is conserved rather than refilled. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Payment
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution DebtActivationWorld
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
namespace Shared
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root presentation frames runtime actual_node)
end A
variable (programme : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem current_actual :
    (⟨J.World frame.registered, (debtCurrent programme frame).rooted.erase⟩ : AnyAuthoritativeRootCurrent.{u}) =
      (A.presentation frame programme).erase := by
  apply congrArg (fun visit =>
    (⟨J.World frame.registered, ⟨J.JointV frame.registered frame.packetAt,
      (A.root frame programme).toAuthoritativeRoot, visit⟩⟩ : AnyAuthoritativeRootCurrent.{u}))
  have visits : (count : Nat) →
      RootGeneratedDebtActivationJointSource.Successor.Restructuring.finiteVisit
        frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count =
      RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit
        frame.old frame.registered frame.packetAt count := by
    intro count
    induction count with
    | zero => rfl
    | succ count prior => exact congrArg (fun visit => visit.next (by rfl)) prior
  exact congrArg SourceNativeTemporalVisitAt.finite (visits (frame.depth + 1))

theorem no_refill : (debtStep programme frame).targetEntry.progressBudget ≤ (debtCurrent programme frame).budget :=
  (debtStep programme frame).progressBudget_not_refilled

def paidContinuation (paid : GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment
      frame.registered.input.expression) frame.event.state)
    (actual : frame.action = .inr paid) : SourceNativePaidRootDebtMacroContinuationAt (debtCurrent programme frame) :=
  .ofPayment .refl (payment programme frame paid actual) .refl

theorem wellFounded : WellFounded (SourceNativePaidRootDebtContinuationRel
    (process := process programme frame)
    (origin := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Payment.mathEntry
      frame.old frame.registered frame.packetAt 0)) :=
  sourceNativePaidRootDebtContinuationRel_wellFounded

theorem no_paid_of_zero (zero : (debtCurrent programme frame).budget = 0) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt (debtCurrent programme frame)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero _ zero

theorem macro_current (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
    (count : Nat) : ((A.runtime initial programme).stateAt count).engine.node.erase =
      (⟨J.World (A.frames initial programme count).registered, (debtCurrent programme (A.frames initial programme count)).rooted.erase⟩ :
        AnyAuthoritativeRootCurrent.{u}) :=
  (congrArg RootInquiryProcessNode.erase (A.actual_node initial programme count)).trans
    (current_actual programme (A.frames initial programme count)).symm

end Shared

variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
abbrev current_actual := Shared.current_actual originalProgramme frame
abbrev no_refill := Shared.no_refill originalProgramme frame
abbrev paidContinuation := Shared.paidContinuation originalProgramme frame
abbrev wellFounded := Shared.wellFounded originalProgramme frame
abbrev no_paid_of_zero := Shared.no_paid_of_zero originalProgramme frame

abbrev macro_current (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.macro_current originalProgramme initial

end SourceOperationInquiry.Context.Faces.Execution.Activation.Payment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

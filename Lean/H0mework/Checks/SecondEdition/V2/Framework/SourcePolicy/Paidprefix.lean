import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix
import H0mework.Checks.SecondEdition.V2.Framework.SourcePolicy.Selectedstockbirth

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyPaidPrefixControls
open SourceOperationEffects SourceOperationExecution
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme M.Frame)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames)
end A
namespace C
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt receipt_next receipt_compiles)
end C
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
  (prefix_budget paid_at_offset receipt_distance_exact receipt_paid_prefix receipt_read receipt_environment)
end P
namespace B
export SourceOperationInquiry.Context.Native.Frame.Stock.Birth (index after)
end B
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme)
end I
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (initial : A.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

theorem actual_birth_after_positive (ordinal : Nat) :
    0 < remaining (B.after initial configuration ordinal).event.state.1 := by
  have generated := SourcePolicySelectedStockBirthControls.actual_paid_after_birth initial configuration ordinal
  generalize frameEq : B.after initial configuration ordinal = frame at generated ⊢
  rcases generated with ⟨paid, _actual⟩
  have strict := (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment
    frame.registered.input.expression).step_budget_lt paid.2
  change remaining paid.1.1 < remaining frame.event.state.1 at strict
  exact Nat.zero_lt_of_lt strict

/-- The full actual paid Step is returned by the prefix producer in Type. -/
def actual_first_paid (ordinal : Nat) :=
  P.receipt_paid_prefix (I.programme configuration) initial (B.index initial configuration ordinal + 1)
    ⟨0, by
      have positive := actual_birth_after_positive initial configuration ordinal
      have distance := P.receipt_distance_exact (I.programme configuration) initial (B.index initial configuration ordinal + 1)
      change 0 < remaining (A.frames initial (I.programme configuration) (B.index initial configuration ordinal + 1)).event.state.1 at positive
      omega⟩

theorem actual_settled_zero (start : Nat) :
    (C.receipt configuration initial (start + (C.receipt configuration initial start).1)).1 = 0 := by
  have zero : remaining (A.frames initial configuration (start + (C.receipt configuration initial start).1)).event.state.1 = 0 := by
    rw [(C.receipt configuration initial start).2.1.2.down]
    rfl
  exact (P.receipt_distance_exact configuration initial _).trans zero
theorem actual_settled_next (start : Nat) : type_of%
    (C.receipt_next configuration initial (start + (C.receipt configuration initial start).1)) :=
  C.receipt_next configuration initial (start + (C.receipt configuration initial start).1)
theorem actual_settled_compiles (start : Nat) : type_of%
    (C.receipt_compiles configuration initial (start + (C.receipt configuration initial start).1)) :=
  C.receipt_compiles configuration initial (start + (C.receipt configuration initial start).1)
theorem actual_environment {env : Env Value Var}
    (same : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At initial env)
    (start : Nat) : type_of% (P.receipt_environment configuration initial same start) :=
  P.receipt_environment configuration initial same start

#print axioms P.prefix_budget
#print axioms P.paid_at_offset
#print axioms P.receipt_distance_exact
#print axioms P.receipt_paid_prefix
#print axioms P.receipt_read
#print axioms P.receipt_environment
#print axioms actual_birth_after_positive
#print axioms actual_first_paid
#print axioms actual_settled_zero
#print axioms actual_settled_next
#print axioms actual_settled_compiles
#print axioms actual_environment
end SourcePolicyPaidPrefixControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

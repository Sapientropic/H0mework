import H0mework.Versions.AB.Realization.Operations.Tree.Installation.Runtime
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Completion
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.Native.Request.Payment

/-! Independent consumers read the completed tree value and its paid
history from the original registered runtime; each whole write and canonical
next retain both physical and mathematical source rows. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Installation.Fock
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
namespace C
export RootGeneratedDebtActivationJointSource.Native.Request.Completion
  (event completed completedEvent completed_value completed_history_length budget)
end C
namespace P
export RootGeneratedDebtActivationJointSource.Native.Request.Payment
  (canonicalSuccessor canonical_next generatePayment debtCurrent paidContinuation_wellFounded
   registered_macro_next_actual)
end P
variable (runtime : LivingRuntimeState process) (depth : Nat)

abbrev actualRegistered := inputs runtime depth (actualInput runtime depth).query
theorem registered_expression : (actualRegistered runtime depth).input.expression =
    program (actualTree runtime depth) := by
  unfold actualRegistered inputs registered RootGeneratedDebtActivationJointSource.register
  rfl

theorem registered_environment : (actualRegistered runtime depth).input.environment = environment := by
  unfold actualRegistered inputs registered RootGeneratedDebtActivationJointSource.register
  rfl

abbrev completed := C.completed (old runtime depth) (nativeProgram runtime depth)
  (actualRegistered runtime depth) (nativeScope runtime depth)

theorem completed_value : (completed runtime depth).1 =
    Finsupp.single (CanonicalUnitArithmeticRoot.nativeActionTarget (actualTree runtime depth)) 1 :=
by
  have value := C.completed_value (old runtime depth) (nativeProgram runtime depth)
    (actualRegistered runtime depth) (nativeScope runtime depth)
  have source := congrArg₂ (fun expression env => expression.eval env)
    (registered_expression runtime depth) (registered_environment runtime depth)
  exact value.trans (source.trans (program_source _))

theorem completed_original_write : (completed runtime depth).1 =
    Finsupp.single
      (RootGeneratedDebtActivationJointSource.Unit.originalOccurrence
        (SourcePhysicalCalculationAdmission.registered runtime)
        ((original runtime depth).root.emitted (original runtime depth).visit.current)).2.write.target 1 := by
  have source := completed_value runtime depth
  rw [tree_source] at source
  exact source.trans (congrArg (fun value => Finsupp.single value (1 : ℤ))
    (RootGeneratedDebtActivationJointSource.Unit.originalOccurrence
      (SourcePhysicalCalculationAdmission.registered runtime)
      ((original runtime depth).root.emitted (original runtime depth).visit.current)).2.action_operation_agree.1.symm)

theorem completed_physical_source :
    (completed runtime depth).1 =
      Finsupp.single (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).nativeWrite.target 1 ∧
    (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).targetState =
      (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).sourceState +
      (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).forcedTrace := by
  constructor
  · exact (completed_original_write runtime depth).trans
      (congrArg (fun write => Finsupp.single write.target (1 : ℤ))
        (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).nativeWrite_source.symm)
  · exact (SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload runtime depth).stateUpdate

theorem completed_cost :
    (C.completedEvent (old runtime depth) (nativeProgram runtime depth)
      (actualRegistered runtime depth) (nativeScope runtime depth)).state.2.length = budget (actualTree runtime depth) :=
by
  have cost := C.completed_history_length (old runtime depth) (nativeProgram runtime depth)
    (actualRegistered runtime depth) (nativeScope runtime depth)
  exact cost.trans ((congrArg remaining (registered_expression runtime depth)).trans
    (program_budget _))

theorem actual_budget (count : Nat) :
    remaining (C.event (old runtime depth) (nativeProgram runtime depth)
      (actualRegistered runtime depth) (nativeScope runtime depth) count).state.1 = budget (actualTree runtime depth) - count :=
by
  have generated := C.budget (old runtime depth) (nativeProgram runtime depth)
    (actualRegistered runtime depth) (nativeScope runtime depth) count
  exact generated.trans ((congrArg (fun expression => remaining expression - count)
    (registered_expression runtime depth)).trans
      (congrArg (fun budget => budget - count) (program_budget _)))

abbrev wholeReceipt (count : Nat) := P.canonicalSuccessor (old runtime depth) (nativeProgram runtime depth)
  (actualRegistered runtime depth) (nativeScope runtime depth) count

theorem actual_next (count : Nat) : (wholeReceipt runtime depth count).targetCurrent =
    RootGeneratedDebtActivationJointSource.Native.Request.mathCurrent (old runtime depth) (nativeProgram runtime depth)
      (actualRegistered runtime depth) (nativeScope runtime depth) (count + 1) :=
  P.canonical_next (old runtime depth) (nativeProgram runtime depth)
    (actualRegistered runtime depth) (nativeScope runtime depth) count

def generatedPayment (count : Nat) := P.generatePayment (old runtime depth) (nativeProgram runtime depth)
  (actualRegistered runtime depth) (nativeScope runtime depth) count

def strictPayment (count : Nat) (sourceBudget : count + 1 < budget (actualTree runtime depth)) :
    SourceNativeRootDebtPaymentStepAt
      (P.debtCurrent (old runtime depth) (nativeProgram runtime depth)
        (actualRegistered runtime depth) (nativeScope runtime depth) count) := by
  cases generated : generatedPayment runtime depth count with
  | inr paid => exact paid
  | inl settled =>
      have zero := (RootGeneratedDebtActivationJointSource.Idle.law
        (actualRegistered runtime depth).input.environment
        (actualRegistered runtime depth).input.expression).settlement_budget_zero settled
      have currentBudget := actual_budget runtime depth (count + 1)
      change remaining (C.event (old runtime depth) (nativeProgram runtime depth)
        (actualRegistered runtime depth) (nativeScope runtime depth) (count + 1)).state.1 = 0 at zero
      omega

theorem same_debt_wellFounded : type_of% (P.paidContinuation_wellFounded
    (old runtime depth) (nativeProgram runtime depth) (actualRegistered runtime depth)
      (nativeScope runtime depth)) :=
  P.paidContinuation_wellFounded (old runtime depth) (nativeProgram runtime depth)
    (actualRegistered runtime depth) (nativeScope runtime depth)

theorem macro_next (count : Nat) : type_of% (P.registered_macro_next_actual
    (old runtime depth) (nativeProgram runtime depth) (nativeScope runtime depth)
    (inputs runtime depth) (owners runtime depth) (payments runtime depth)
    (actions runtime depth) (audits runtime depth) (actualInput runtime depth) count) :=
  P.registered_macro_next_actual (old runtime depth) (nativeProgram runtime depth) (nativeScope runtime depth)
    (inputs runtime depth) (owners runtime depth) (payments runtime depth)
    (actions runtime depth) (audits runtime depth) (actualInput runtime depth) count

end SourceOperationNative.Tree.Installation.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

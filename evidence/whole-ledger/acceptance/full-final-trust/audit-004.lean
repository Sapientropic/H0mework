import H0mework.Papers.WholeLedgerAccountingRc19e94a5
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointOldEvolution", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointOldEvolution_transferred", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_debt_sameDebt", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_debt_strict", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_debt", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_debt_evolution", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_old", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_destination_old_evolution", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_debt", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_old", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.DebtActivationLedger.jointStepLedgerEvolution_origin_old_evolution", "H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.CompleteImageAt", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Image"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.CompleteImageAt.target_emitted", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Image"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.IdentityScope", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.MathReadout", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.Program", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Image"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.RawIncidenceAt", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.RawRowAt", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.authoritativeRoot", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.authoritySource", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.compile_emitted", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.coverage", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerCompiler", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerRoot", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.ledgerSource", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.livingRoot", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathReadout", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathRowEvolution", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathSource", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.mathTargetEntry", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldEntry_injective", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldFold_destination_injective", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.oldFold_origin_injective", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.originalOccurrence", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.original_projection_outcome", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch_destination_injective", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.patch_origin_injective", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Scope"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.projectionLaw", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Projection"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.read?", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Image"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringCertification", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringLaw", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.restructuringSource", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Authority"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rowEvolution", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rowSource", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rows", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.rows_size", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Compiler"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.sourceRow", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Native.targetRow", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Native.Rows"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed_next_state", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completed_source_value", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completionRuntime", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.completion_budget", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathContinuation", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathCurrent", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathCurrent_budget", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathOrigin", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathPaidContinuation_wellFounded", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathPayment", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.mathStep", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Noetherian"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget_advance", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootGeneratedDebtActivationJointSource.Unit.runtimeBudget_tick", "H0mework.Versions.Rc19e94a5.Foundation.Responsibility.JointSource.Unit.Completion"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Advance", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.Settlement", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.State", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.advance", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.completed_value", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.generate", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.initial", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationExecutionDebt.law", "H0mework.Realization.Operations.Execution.Debt.Source"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.actual_node", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.boundary", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.budget", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.budget_eq", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.canonicalSuccessor", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.canonical_next", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.current_original", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.current_pair_read", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.debtCurrent", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.debtStep", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.history", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.macro_next_actual", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.occurrence", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.originalOccurrence", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.paidContinuation", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.paidContinuation_wellFounded", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.payment", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalActive", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalEnvironment", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPair", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPair_eq", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalPayload", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physicalProjection", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_inverse", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_outcome", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.physical_pair_inverse", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.pinned_pair", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.postBirthProcess", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.postBirthProcess_actual", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.receipt", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_inventory", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_read", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.residual_zero_iff", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.trace_accounting", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Consumer.zero_budget_residual", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Consumer"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.Phase", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.birth_successor", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.bornResumption", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.firstTick", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initialQuery", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initialQuery_unique", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_next", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_next_living_law", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_resolution", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.initial_resolution_kind", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.inquiryProcess", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.inquiryRuntime", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.math_successor", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.nextQueryAt", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.nextQuery_unique", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.presentationAt", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.presentationAt_erase_injective", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Inquiry.stateAt_afterBirth_node", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Runtime"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.firstSuccessor", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.generated", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.initialBornRow", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.initialOldRow", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.program", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceAuthority", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceEntry", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceEvent", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceRoot", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceSuccessor", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.sourceVisit", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.targetAt", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourcePhysicalCalculationAdmission.Target.targetInitialVisit", "H0mework.Versions.Rc19e94a5.Fock.SourceHistory.Operation.Calculation.Admission.Target"),
    ("SaturationMonoid.SourceOperationExecution.Step.relationWords", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Step.relation_boundary", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relationWords", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relationWords_append", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_boundary", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_cochain", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_inventory", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.relation_old", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.updated_residual", "H0mework.Realization.Operations.Execution.Relations"),
    ("SaturationMonoid.SourceOperationExecution.Trace.updated_zero_iff", "H0mework.Realization.Operations.Execution.Relations")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "b04408e7eda029f92e278629da9434c1e10b0e73c9c2d39d7a747d493df11c9f"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"

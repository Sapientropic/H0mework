import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (write : PairValue Value sort → Env (PairValue Value) cfg.LowVar)

theorem old_paid_const : (material frame cfg).state.1 = .const (oldPaid frame cfg) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame cfg).toAuthoritativeRoot
    (S.visit frame cfg).current (fun _ => R.actionReader frame cfg (S.actualOccurrence frame))

theorem old_paid_value : oldPaid frame cfg =
    (material frame cfg).raw.eval (material frame cfg).environment :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame cfg).toAuthoritativeRoot
    (R.actionReader frame cfg) (S.actualOccurrence frame)

theorem selected_raw : (selected frame cfg write).rawRead = (initial frame cfg).rawRead := by
  apply Prefix.receipt_read (programme frame cfg write) (initial frame cfg)
    (fun stage => (S.frames (initial frame cfg) (programme frame cfg write) stage).rawRead)
  intro stage paid actual
  have next : S.frames (initial frame cfg) (programme frame cfg write) (stage + 1) =
      (S.frames (initial frame cfg) (programme frame cfg write) stage).mathNext := by
    change S.next _ _ = _
    unfold S.next
    rw [actual]
  exact (congrArg (fun candidate : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
    (Value := PairValue Value) (Var := cfg.LowVar) (sort := sort) => candidate.rawRead) next).trans rfl

theorem native_value : nativeValue frame cfg write =
    (N.expression (material frame cfg)).eval (N.input (material frame cfg)).environment := by
  have paid := SourceOperationExecutionDebt.completed_value
    (selected frame cfg write).event.state (receipt frame cfg write).2.1
  change nativeValue frame cfg write = (selected frame cfg write).rawRead.expression.eval
    (selected frame cfg write).rawRead.environment at paid
  rw [selected_raw] at paid
  exact paid

theorem updated_total : oldPaid frame cfg + nativeValue frame cfg write =
    (material frame cfg).raw.eval (N.input (material frame cfg)).environment := by
  let env := (N.input (material frame cfg)).environment
  have native : nativeValue frame cfg write = (material frame cfg).raw.eval env -
      (material frame cfg).state.1.eval env :=
    (native_value frame cfg write).trans (N.expression_eval (material frame cfg) env)
  have old : (material frame cfg).state.1.eval env = oldPaid frame cfg :=
    (congrArg (fun expression : Expr (PairValue Value) cfg.LowVar sort =>
      expression.eval env) (old_paid_const frame cfg)).trans rfl
  calc
    oldPaid frame cfg + nativeValue frame cfg write =
        oldPaid frame cfg + ((material frame cfg).raw.eval env - (material frame cfg).state.1.eval env) :=
      congrArg (fun value => oldPaid frame cfg + value) native
    _ = (material frame cfg).raw.eval env := by rw [old]; abel

theorem born_environment :
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At (born frame cfg write)
      (write (oldPaid frame cfg + nativeValue frame cfg write)) := by
  intro current occurrence
  change write (oldPaid frame cfg + nativeEventValue
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit (selected frame cfg write)).current.2) = _
  have eventEq :
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit (selected frame cfg write)).current.2 =
        (selected frame cfg write).event := rfl
  have same := congrArg nativeEventValue eventEq
  have actual : nativeEventValue (selected frame cfg write).event = nativeValue frame cfg write := by
    unfold nativeEventValue
    have action := (receipt frame cfg write).2.2.2
    dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action] at action
    rw [action]
    rfl
  exact congrArg (fun value : PairValue Value sort => write (oldPaid frame cfg + value)) (same.trans actual)

theorem source_target_root : type_of% (Intake.target_root frame cfg (programme frame cfg write)
    (SourceGeneratedInquiryReceiptAction.sourceEvent frame cfg)) :=
  Intake.target_root frame cfg (programme frame cfg write) (SourceGeneratedInquiryReceiptAction.sourceEvent frame cfg)
theorem source_target_next : type_of% (Intake.target_next frame cfg (programme frame cfg write)
    (SourceGeneratedInquiryReceiptAction.sourceEvent frame cfg)) :=
  Intake.target_next frame cfg (programme frame cfg write) (SourceGeneratedInquiryReceiptAction.sourceEvent frame cfg)
theorem source_compiles : type_of% (Intake.compiles frame cfg (programme frame cfg write)) :=
  Intake.compiles frame cfg (programme frame cfg write)
theorem source_whole : type_of% (sourceTarget frame cfg write).target.firstDestination_heq :=
  (sourceTarget frame cfg write).target.firstDestination_heq

theorem actual_receipt_compiles : type_of% (Complete.receipt_compiles
    (programme frame cfg write) (initial frame cfg) 0) := Complete.receipt_compiles _ _ _
theorem actual_receipt_next : type_of% (Complete.receipt_next
    (programme frame cfg write) (initial frame cfg) 0) := Complete.receipt_next _ _ _

theorem born_inventory : (born frame cfg write).inventory =
    (CF.lowProgramme frame cfg).nextInventory (selected frame cfg write) := rfl
theorem born_pair_inventory : (born frame cfg write).pairInventory =
    (CF.lowProgramme frame cfg).nextPairInventory (selected frame cfg write) := rfl

theorem native_effect : nativeValue frame cfg write =
    SourceOperationScalarRelations.effectEvaluator (R := ℤ)
      (material frame cfg).environment (material frame cfg).increment
      (SourceOperationScalarPresentation.relationMap (R := ℤ) (material frame cfg).environment
        (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relations (R := ℤ) (material frame cfg))) :=
  (native_value frame cfg write).trans (N.updated_value (R := ℤ) (material frame cfg))

theorem native_inverse :
    (SourceGeneratedScalarDifferentialResidual.residualEquivRange
      (SourceOperationScalarRelations.evaluation (R := ℤ) (N.input (material frame cfg)).environment)
      (SourceGeneratedScalarDifferentialResidual.canonicalResidual
        (SourceOperationScalarRelations.evaluation (R := ℤ) (N.input (material frame cfg)).environment)
        (SourceOperationScalarPresentation.relationMap (R := ℤ) (material frame cfg).environment
          (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relations (R := ℤ) (material frame cfg))))).val =
      nativeValue frame cfg write :=
  (N.residual_value (R := ℤ) (material frame cfg)).trans (native_value frame cfg write).symm

theorem configured_actual_paid_pair_writeback :
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At (born frame cfg write)
      (write ((material frame cfg).raw.eval (N.input (material frame cfg)).environment)) := by
  intro current occurrence
  exact ((born_environment frame cfg write) occurrence).trans
    (congrArg write (updated_total frame cfg write))
end SourceGeneratedInquiryReceiptAction.Configured.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

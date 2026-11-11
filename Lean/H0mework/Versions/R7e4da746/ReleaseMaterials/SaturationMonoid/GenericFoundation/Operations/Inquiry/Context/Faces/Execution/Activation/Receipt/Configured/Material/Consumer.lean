import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Material.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Material
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
 (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next nextBorn actualVisit)
end Q
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
 (input expression expression_eval updated_value residual_value relations)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
 (programme oldPaid old_paid_const old_paid_value nativeAt nativeEventValue)
end WB
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
variable (baseProgramme : A.Programme (PhysicalValue := PairValue Value) (PhysicalVar := cfg.LowVar) (sort := sort))

abbrev material := (nextMaterialFace frame cfg baseProgramme).rootRead.prefixMaterial
abbrev oldPaid := (nextMaterialFace frame cfg baseProgramme).rootRead.prefixResult.2.2.1
abbrev receipt := Complete.receipt (programme frame cfg baseProgramme) (initial frame cfg) 0
abbrev selected := Complete.atReceipt (programme frame cfg baseProgramme) (initial frame cfg) 0
def nativeValue := (receipt frame cfg baseProgramme).2.1.1
abbrev born := Q.nextBorn (selected frame cfg baseProgramme) (programme frame cfg baseProgramme)

theorem old_paid_const : (material frame cfg baseProgramme).state.1 = .const (oldPaid frame cfg baseProgramme) :=
 WB.old_paid_const frame cfg

theorem old_paid_value : oldPaid frame cfg baseProgramme =
 (material frame cfg baseProgramme).raw.eval (material frame cfg baseProgramme).environment :=
 WB.old_paid_value frame cfg

theorem selected_raw : (selected frame cfg baseProgramme).rawRead = (initial frame cfg).rawRead := by
 apply Prefix.receipt_read (programme frame cfg baseProgramme) (initial frame cfg)
  (fun stage => (Q.frames (initial frame cfg) (programme frame cfg baseProgramme) stage).rawRead)
 intro stage paid actual
 have step : Q.frames (initial frame cfg) (programme frame cfg baseProgramme) (stage+1) =
   (Q.frames (initial frame cfg) (programme frame cfg baseProgramme) stage).mathNext := by
  change Q.next _ _ = _
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  rw [actual]
 exact (congrArg (fun candidate : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PairValue Value) (Var := cfg.LowVar) (sort := sort) => candidate.rawRead) step).trans rfl

theorem native_value : nativeValue frame cfg baseProgramme =
 (N.expression (material frame cfg baseProgramme)).eval (N.input (material frame cfg baseProgramme)).environment := by
 have paid := SourceOperationExecutionDebt.completed_value
  (selected frame cfg baseProgramme).event.state (receipt frame cfg baseProgramme).2.1
 change nativeValue frame cfg baseProgramme = (selected frame cfg baseProgramme).rawRead.expression.eval
  (selected frame cfg baseProgramme).rawRead.environment at paid
 rw [selected_raw] at paid
 exact paid

theorem updated_total : oldPaid frame cfg baseProgramme + nativeValue frame cfg baseProgramme =
 (material frame cfg baseProgramme).raw.eval
  ((material frame cfg baseProgramme).environment+(material frame cfg baseProgramme).increment) := by
 let env := (N.input (material frame cfg baseProgramme)).environment
 have native : nativeValue frame cfg baseProgramme =
   (material frame cfg baseProgramme).raw.eval env-(material frame cfg baseProgramme).state.1.eval env :=
  (native_value frame cfg baseProgramme).trans (N.expression_eval (material frame cfg baseProgramme) env)
 have old : (material frame cfg baseProgramme).state.1.eval env = oldPaid frame cfg baseProgramme :=
  (congrArg (fun expression : Expr (PairValue Value) cfg.LowVar sort => expression.eval env)
   (old_paid_const frame cfg baseProgramme)).trans rfl
 change oldPaid frame cfg baseProgramme+nativeValue frame cfg baseProgramme =
  (material frame cfg baseProgramme).raw.eval env
 rw [native,old]
 abel

theorem native_effect : nativeValue frame cfg baseProgramme =
 SourceOperationScalarRelations.effectEvaluator (R := ℤ)
  (material frame cfg baseProgramme).environment (material frame cfg baseProgramme).increment
  (SourceOperationScalarPresentation.relationMap (R := ℤ) (material frame cfg baseProgramme).environment
   (N.relations (R := ℤ) (material frame cfg baseProgramme))) :=
 (native_value frame cfg baseProgramme).trans (N.updated_value (R := ℤ) (material frame cfg baseProgramme))

theorem native_inverse :
 (SourceGeneratedScalarDifferentialResidual.residualEquivRange
  (SourceOperationScalarRelations.evaluation (R := ℤ) (N.input (material frame cfg baseProgramme)).environment)
  (SourceGeneratedScalarDifferentialResidual.canonicalResidual
   (SourceOperationScalarRelations.evaluation (R := ℤ) (N.input (material frame cfg baseProgramme)).environment)
   (SourceOperationScalarPresentation.relationMap (R := ℤ) (material frame cfg baseProgramme).environment
    (N.relations (R := ℤ) (material frame cfg baseProgramme))))).val = nativeValue frame cfg baseProgramme :=
 (N.residual_value (R := ℤ) (material frame cfg baseProgramme)).trans (native_value frame cfg baseProgramme).symm

theorem actual_receipt_compiles : type_of% (Complete.receipt_compiles
 (programme frame cfg baseProgramme) (initial frame cfg) 0) := Complete.receipt_compiles _ _ _

theorem actual_receipt_next : type_of% (Complete.receipt_next
 (programme frame cfg baseProgramme) (initial frame cfg) 0) := Complete.receipt_next _ _ _

theorem born_inventory : (born frame cfg baseProgramme).inventory =
 baseProgramme.nextInventory (selected frame cfg baseProgramme) := rfl

theorem born_pair_inventory : (born frame cfg baseProgramme).pairInventory =
 baseProgramme.nextPairInventory (selected frame cfg baseProgramme) := rfl

variable (write : PairValue Value sort → Env (PairValue Value) cfg.LowVar)

theorem actual_writeback :
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
  (born frame cfg (WB.programme frame cfg write))
  (write ((material frame cfg (WB.programme frame cfg write)).raw.eval
    ((material frame cfg (WB.programme frame cfg write)).environment+
     (material frame cfg (WB.programme frame cfg write)).increment))) := by
 intro current occurrence
 change write (oldPaid frame cfg (WB.programme frame cfg write)+WB.nativeEventValue
  (Q.actualVisit (selected frame cfg (WB.programme frame cfg write))).current.2) = _
 have eventEq : (Q.actualVisit (selected frame cfg (WB.programme frame cfg write))).current.2 =
   (selected frame cfg (WB.programme frame cfg write)).event := rfl
 have same := congrArg WB.nativeEventValue eventEq
 have actual : WB.nativeEventValue (selected frame cfg (WB.programme frame cfg write)).event =
   nativeValue frame cfg (WB.programme frame cfg write) := by
  unfold SourceGeneratedInquiryReceiptAction.Configured.Writeback.nativeEventValue
  have action := (receipt frame cfg (WB.programme frame cfg write)).2.2.2
  dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action] at action
  rw [action]
  rfl
 exact (congrArg (fun value : PairValue Value sort =>
  write (oldPaid frame cfg (WB.programme frame cfg write)+value)) (same.trans actual)).trans
  (congrArg write (updated_total frame cfg (WB.programme frame cfg write)))

end SourceGeneratedInquiryReceiptAction.Configured.Material
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

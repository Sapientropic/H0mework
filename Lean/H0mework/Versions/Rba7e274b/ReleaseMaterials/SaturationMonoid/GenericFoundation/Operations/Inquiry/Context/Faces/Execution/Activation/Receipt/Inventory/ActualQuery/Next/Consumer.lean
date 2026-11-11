import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query resultFace actualOccurrence root visit)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial sourceEvent)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input)
end N
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : A.Programme
  (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def commonFace : SourceNativeRootSemanticFaceAt (target frame configuration).targetRoot
    (target frame configuration).targetVisit where
  projection := projection frame configuration
  active := PUnit.unit
  classifier_eq := rfl

theorem common_at_actual_next : (commonFace frame configuration).rootRead = commonAtNext frame configuration := rfl

theorem query_action_raw :
    (S.query (receiver frame configuration) (programme frame configuration)).raw = actionRaw frame configuration := rfl

theorem result_action : HEq (S.resultFace (receiver frame configuration) (programme frame configuration)).rootRead
    (R.actionResultAt (receiver frame configuration) (programme frame configuration)
      (S.actualOccurrence (receiver frame configuration))) := HEq.rfl

private theorem effect_zero (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := configuration.LowVar) (sort := sort)) :
    raw.expression.effect raw.environment 0 = 0 := by
  have generated := Expr.eval_update raw.expression raw.environment 0
  rw [add_zero] at generated
  exact add_left_cancel (generated.symm.trans (add_zero _).symm)

theorem action_value : (actionRaw frame configuration).expression.eval (actionRaw frame configuration).environment =
    ((fullRaw frame configuration).expression.eval (fullRaw frame configuration).environment, 0) :=
  (eval_liftExpr (fullRaw frame configuration).expression (fullRaw frame configuration).environment 0).trans
    (congrArg (fun increment => ((fullRaw frame configuration).expression.eval (fullRaw frame configuration).environment, increment))
      (effect_zero configuration (fullRaw frame configuration)))

theorem actual_pair : (S.resultFace (receiver frame configuration) (programme frame configuration)).rootRead.2.2.1 =
    ((fullRaw frame configuration).expression.eval (fullRaw frame configuration).environment, 0) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
      (receiver frame configuration) (programme frame configuration)).toAuthoritativeRoot
    (R.actionReader (receiver frame configuration) (programme frame configuration))
    (S.actualOccurrence (receiver frame configuration))).trans (action_value frame configuration)

theorem actual_trace : (S.resultFace (receiver frame configuration) (programme frame configuration)).rootRead.2.1.2.length =
    remaining (actionRaw frame configuration).expression :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
      (receiver frame configuration) (programme frame configuration)).toAuthoritativeRoot
    (R.actionReader (receiver frame configuration) (programme frame configuration))
    (S.actualOccurrence (receiver frame configuration))

theorem updated_pair : (R.actualMaterial (receiver frame configuration) (programme frame configuration)).raw.eval
    (N.input (R.actualMaterial (receiver frame configuration) (programme frame configuration))).environment =
      ((fullRaw frame configuration).expression.eval (fullRaw frame configuration).environment, 0) := by
  have same : (N.input (R.actualMaterial (receiver frame configuration) (programme frame configuration))).environment =
      (actionRaw frame configuration).environment := add_sub_cancel _ _
  exact (congrArg (fun env => (actionRaw frame configuration).expression.eval env) same).trans
    (action_value frame configuration)

theorem admitted_full_raw : (admittedCommon frame configuration).2.1 = fullRaw frame configuration := rfl

theorem reader_admitted_source :
    (S.query (receiver frame configuration) (programme frame configuration)).raw =
      (⟨pairEnvironment (admittedCommon frame configuration).2.1.environment 0,
        liftExpr (admittedCommon frame configuration).2.1.expression⟩ :
        RootGeneratedDebtActivationJointSource.OwnerFree.Raw
          (Value := PairValue (PairValue PhysicalValue)) (Var := configuration.LowVar) (sort := sort)) := rfl

theorem emitter_root : (admitted frame configuration).target.targetRoot =
    S.root (receiver frame configuration) (programme frame configuration) :=
  Intake.target_root frame (sourceCfg configuration) (programme frame configuration)
    (R.sourceEvent frame (sourceCfg configuration))

theorem emitter_current : (admitted frame configuration).target.targetAnswerAndNext.nextCurrent =
    ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
       (receiver frame configuration).registered (receiver frame configuration).packetAt,
     (S.root (receiver frame configuration) (programme frame configuration)).toAuthoritativeRoot,
     S.visit (receiver frame configuration) (programme frame configuration)⟩ :=
  Intake.target_next frame (sourceCfg configuration) (programme frame configuration)
    (R.sourceEvent frame (sourceCfg configuration))

theorem emitter_compiles : type_of%
    (Intake.compiles frame (sourceCfg configuration) (programme frame configuration)) :=
  Intake.compiles frame (sourceCfg configuration) (programme frame configuration)

theorem emitter_successor : type_of%
    (Intake.successor_valid frame (sourceCfg configuration) (programme frame configuration)) :=
  Intake.successor_valid frame (sourceCfg configuration) (programme frame configuration)

theorem emitter_whole : type_of% (admitted frame configuration).target.firstDestination_heq :=
  (admitted frame configuration).target.firstDestination_heq

theorem original_residual : (receiver frame configuration).registered.input.expression =
    N.expression (R.actualMaterial frame (sourceCfg configuration)) := rfl

theorem original_owner : HEq (receiver frame configuration).registered.input.owner
    (R.actualMaterial frame (sourceCfg configuration)).owner := HEq.rfl

end SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

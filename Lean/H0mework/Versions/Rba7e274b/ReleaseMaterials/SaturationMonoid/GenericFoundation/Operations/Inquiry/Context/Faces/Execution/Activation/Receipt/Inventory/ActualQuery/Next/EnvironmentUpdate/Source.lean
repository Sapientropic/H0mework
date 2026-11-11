import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualQueryBornEnvironmentUpdate
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
 (born receiver nextCfg scalar pair)
end SS
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme)
end Q
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial sourceEvent)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (datum root visit query resultFace actualOccurrence)
end S
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory Packet)
end SF
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission (sourceEvent generatedAction target_root target_current compiles successor_valid)
end Admission
variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
local instance levelGroups (n : Nat) (t : PUnit.{u+1}) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)

-- Source input and born Env remain different coordinates of the original receipt.
def fullRaw := R.actionReader data.1 sourceCfg (S.actualOccurrence data.1)
def bornEnv := (SS.born factory n data sourceCfg language).activeEnvironment
def increment := bornEnv factory n data sourceCfg language - (fullRaw n data sourceCfg).environment

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue (PairValue (L.Value W n))) (Var := sourceCfg.LowVar) (sort := PUnit.unit) :=
 ⟨pairEnvironment (fullRaw n data sourceCfg).environment (increment factory n data sourceCfg language),
  liftExpr (fullRaw n data sourceCfg).expression⟩

def lowProgramme := { SS.nextCfg factory n data sourceCfg language with
 datum := fun currentFrame => { (SS.nextCfg factory n data sourceCfg language).datum currentFrame with
  calculationReader := some (fun {_current} _supplied => raw factory n data sourceCfg language) } }

def programme := Q.programme (lowProgramme factory n data sourceCfg language)
abbrev receiver := SS.receiver factory n data sourceCfg language
abbrev generated := Admission.generatedAction data.1 sourceCfg (SS.scalar factory n data sourceCfg language)
 (SS.pair factory n data sourceCfg language) (programme factory n data sourceCfg language)

theorem actual_emitter_root : type_of% (Admission.target_root data.1 sourceCfg
 (SS.scalar factory n data sourceCfg language) (SS.pair factory n data sourceCfg language)
 (programme factory n data sourceCfg language) (Admission.sourceEvent data.1 sourceCfg)) := by
 exact Admission.target_root data.1 sourceCfg (SS.scalar factory n data sourceCfg language)
  (SS.pair factory n data sourceCfg language) (programme factory n data sourceCfg language) (Admission.sourceEvent data.1 sourceCfg)

theorem source_env_update : (fullRaw n data sourceCfg).environment + increment factory n data sourceCfg language =
 bornEnv factory n data sourceCfg language := add_sub_cancel _ _

theorem raw_pair : (raw factory n data sourceCfg language).expression.eval (raw factory n data sourceCfg language).environment =
 ((fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment,
  (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
   (increment factory n data sourceCfg language)) := eval_liftExpr _ _ _

theorem effect_actual : (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
 (increment factory n data sourceCfg language) =
 (fullRaw n data sourceCfg).expression.eval (bornEnv factory n data sourceCfg language) -
 (fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment := by
 have actual := Expr.eval_update (fullRaw n data sourceCfg).expression (fullRaw n data sourceCfg).environment
  (increment factory n data sourceCfg language)
 rw [source_env_update] at actual
 exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans actual.symm)

theorem source_sum_actual :
 (fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment +
  (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
   (increment factory n data sourceCfg language) =
 (fullRaw n data sourceCfg).expression.eval (bornEnv factory n data sourceCfg language) :=
 (add_comm _ _).trans (eq_sub_iff_add_eq.mp (effect_actual factory n data sourceCfg language))

theorem raw_pair_total_actual :
 ((raw factory n data sourceCfg language).expression.eval
  (raw factory n data sourceCfg language).environment).1 +
 ((raw factory n data sourceCfg language).expression.eval
  (raw factory n data sourceCfg language).environment).2 =
 (fullRaw n data sourceCfg).expression.eval (bornEnv factory n data sourceCfg language) :=
 (congrArg (fun value : PairValue (PairValue (L.Value W n)) PUnit.unit => value.1 + value.2)
  (raw_pair factory n data sourceCfg language)).trans
  (source_sum_actual factory n data sourceCfg language)

-- Own query executes the source-generated full old/effect AST.
theorem own_pair : (S.resultFace (receiver factory n data sourceCfg language)
 (programme factory n data sourceCfg language)).rootRead.2.2.1 =
 ((fullRaw n data sourceCfg).expression.eval (fullRaw n data sourceCfg).environment,
  (fullRaw n data sourceCfg).expression.effect (fullRaw n data sourceCfg).environment
   (increment factory n data sourceCfg language)) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
   (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language)).toAuthoritativeRoot
  (R.actionReader (receiver factory n data sourceCfg language) (programme factory n data sourceCfg language))
  (S.actualOccurrence (receiver factory n data sourceCfg language))).trans
  (raw_pair factory n data sourceCfg language)

end ActualQueryBornEnvironmentUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

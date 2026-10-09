import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Installation
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual
namespace Req
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
 (MaterialAt input updated_value residual_value residual_zero_iff)
end Req
namespace Residual
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (actualRequest pairInventory)
end Residual
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end Joint
namespace Retarget
variable {S : Type u} {V X : S→Type u} [∀ t, AddCommGroup (V t)] {s:S}
variable {N : WorldRelationNetwork.{u}} {L : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure N L} {current : L.Current}
variable {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
variable (original : Req.MaterialAt (Value:=V) (Var:=X) (sort:=s) occurrence)
variable (environment : Env V X)
def material : Req.MaterialAt (Value:=V) (Var:=X) (sort:=s) occurrence :=
 {original with increment:=environment-original.environment}
theorem input_environment : (Req.input (material original environment)).environment=environment :=add_sub_cancel _ _
theorem fields_preserved : (material original environment).environment=original.environment ∧
 (material original environment).raw=original.raw ∧ (material original environment).state=original.state ∧
 (material original environment).owner=original.owner :=⟨rfl,rfl,rfl,rfl⟩
theorem generated_effect : type_of% (Req.updated_value (R:=ℤ) (material original environment)) :=
 Req.updated_value (R:=ℤ) (material original environment)
theorem generated_residual : type_of% (Req.residual_value (R:=ℤ) (material original environment)) :=
 Req.residual_value (R:=ℤ) (material original environment)
theorem generated_zero_iff : type_of% (Req.residual_zero_iff (R:=ℤ) (material original environment)) :=
 Req.residual_zero_iff (R:=ℤ) (material original environment)
end Retarget

variable {S : Type u} {W X : S→Type u} [∀ t, AddCommGroup (W t)] {s:S}
local instance groups (n:Nat) (t:S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀t,X t→Expr W X t) (n:Nat) (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index : Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
def low := ((Lower.SourceFamily.Foresight.Installed.component binding n seed frame).project
 PUnit.unit index.2 PUnit.unit).1
def sourceEnvironment : Env (PairValue (Lower.Value W n)) X :=
 (low binding n seed frame index).2.2.2.2.2.2.1.environment

theorem projection_material : low binding n seed frame index=
 Future.Replay.Source.material (Future.Replay.Binding.at binding n) seed frame index.2 :=rfl
theorem projection_environment : sourceEnvironment binding n seed frame index=
 Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n) frame index.2 :=rfl

def request := Retarget.material (Residual.actualRequest seed frame index.2)
 (sourceEnvironment binding n seed frame index)

theorem request_environment : (Req.input (request binding n seed frame index)).environment=
 Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n) frame index.2 :=
 (Retarget.input_environment _ _).trans (projection_environment binding n seed frame index)

theorem request_fields : type_of% (Retarget.fields_preserved (Residual.actualRequest seed frame index.2)
 (sourceEnvironment binding n seed frame index)) :=
 Retarget.fields_preserved (Residual.actualRequest seed frame index.2) (sourceEnvironment binding n seed frame index)

theorem source_effect : type_of% (Req.updated_value (R:=ℤ) (request binding n seed frame index)) :=
 Req.updated_value (R:=ℤ) (request binding n seed frame index)
theorem source_residual : type_of% (Req.residual_value (R:=ℤ) (request binding n seed frame index)) :=
 Req.residual_value (R:=ℤ) (request binding n seed frame index)
theorem source_zero_iff : type_of% (Req.residual_zero_iff (R:=ℤ) (request binding n seed frame index)) :=
 Req.residual_zero_iff (R:=ℤ) (request binding n seed frame index)

def actualIndex : Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) :=
 ⟨(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current,
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame⟩
abbrev actualRequest := request binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)
theorem actual_environment : type_of% (request_environment binding n seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)) :=
 request_environment binding n seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)
end Lower.SourceFamily.Foresight.Contextual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end

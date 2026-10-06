import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Disposition.Consumer
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt input expression relations budget updated_value residual_value residual_zero_iff)
end R
variable (frame : Frame.{u})
def old := (Shared.baseRoot frame Disposition.programme).toAuthoritativeRoot
abbrev origin := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
abbrev reader := fun (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=origin frame)) =>
 (Shared.datum frame Disposition.programme).reader supplied
abbrev calculationRoot := RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot (old frame) (origin frame) (reader frame)
abbrev endpoint := (Shared.resultFace frame Disposition.programme).rootRead.2.1
abbrev Occurrence := (calculationRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt (endpoint frame)
def afterEnvironment := (Disposition.queryRaw (A.epoch (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme))
 (Shared.actualOccurrence (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme))
 (Disposition.selected (A.epoch (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme))
 (Shared.actualOccurrence (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme)))).environment
def material (supplied : Occurrence frame) : R.MaterialAt
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) supplied := by
 rcases supplied with ⟨support,event⟩
 cases event
 let raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme).raw
 exact {
  environment:=raw.environment
  increment:=afterEnvironment frame-raw.environment
  raw:=raw.expression
  state:=endpoint frame
  owner:=RootGeneratedDebtActivationJointSource.OwnerFree.mathEntry (old frame) (origin frame) (reader frame) (endpoint frame) }
def registered := RootGeneratedDebtActivationJointSource.register (fun supplied : Occurrence frame => R.input (material frame supplied))
abbrev actualMaterial := material frame ((calculationRoot frame).emitted (endpoint frame))
theorem actual_next_environment : (registered frame).input.environment=afterEnvironment frame := add_sub_cancel _ _
theorem effect_generated : type_of% (R.updated_value (R:=ℤ) (actualMaterial frame)) := R.updated_value (R:=ℤ) (actualMaterial frame)
theorem inverse_generated : type_of% (R.residual_value (R:=ℤ) (actualMaterial frame)) := R.residual_value (R:=ℤ) (actualMaterial frame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

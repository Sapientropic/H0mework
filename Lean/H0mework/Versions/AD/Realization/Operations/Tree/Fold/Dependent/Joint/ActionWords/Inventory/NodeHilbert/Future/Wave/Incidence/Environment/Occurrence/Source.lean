import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Request.Update.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable (frame : Frame.{u})
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev physical := SourceOperationInquiry.Context.Installation.materialAt frame occurrence
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
 ⟨pairEnvironment (physical frame occurrence).raw.environment
   ((physical frame occurrence).nextRaw.environment-(physical frame occurrence).raw.environment),
  liftExpr (physical frame occurrence).raw.expression⟩
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) := raw frame supplied
def result {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) supplied
def written := SourceHistoryCommon.seed (Request.written frame)
 (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure (physical frame occurrence).pairTrace)
  (SourceOperationPaidRelations.exposure (result frame occurrence).2.1.2))
def material := (((Request.Update.component frame).project PUnit.unit occurrence PUnit.unit),
 physical frame occurrence,raw frame occurrence,result frame occurrence,written frame occurrence)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

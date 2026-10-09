import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable (frame : Frame.{u})
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
def history := RootGeneratedCofinalHistoryAt.generate
 (rootOccurrence:=RootedAccountedUnfolding.zero occurrence)
 (seedOccurrence:=Relations.written frame occurrence)
 (continuationOccurrence:=SourceOperationPaidRelations.continuation
  (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit))
def evaluator := SourceOperationPaidRelations.evaluator (sort:=Slot.orbit) (Relations.raw frame occurrence).environment
def face := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
 (history:=history frame occurrence) (evaluatorOccurrence:=evaluator frame occurrence)
def selected := (face frame occurrence).settleWithResidual
def kernelWord (sound : GeneratedRelationSoundnessAt (face frame occurrence))
 (coordinate : GeneratedKernelResidualCoordinateAt (face frame occurrence) sound) :
 (history frame occurrence).generatorClosure :=
 Classical.choose (Submodule.Quotient.mk_surjective (history frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)
def queryRaw (disposition : ResidualDispositionOutcome (face frame occurrence)) :
 RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
 match disposition with
 | .faithful _ _ _ => Relations.raw frame occurrence
 | .unsound _ coordinate => ⟨(Relations.raw frame occurrence).environment,SourceOperationExecution.Coefficients.expression coordinate.relation⟩
 | .kernelResidual sound _ coordinate => ⟨(Relations.raw frame occurrence).environment,
   SourceOperationExecution.Coefficients.expression (kernelWord frame occurrence sound coordinate).val⟩
 | .coverageResidual _ _ coordinate => ⟨(Relations.raw frame occurrence).environment,.const coordinate.representative⟩
def written (disposition : ResidualDispositionOutcome (face frame occurrence)) :=
 match disposition with
 | .kernelResidual sound _ coordinate => SourceHistoryCommon.seed (Relations.written frame occurrence)
   (.zero (.relation (kernelWord frame occurrence sound coordinate).val))
 | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ => Relations.written frame occurrence
def reader {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 queryRaw frame supplied (selected frame supplied)
def result {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) supplied
def completeWritten {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 SourceHistoryCommon.seed (written frame supplied (selected frame supplied))
  (SourceOperationPaidRelations.exposure (result frame supplied).2.1.2)
def material {sourceCurrent : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=sourceCurrent)) :=
 (Relations.material frame supplied,history frame supplied,evaluator frame supplied,
 selected frame supplied,queryRaw frame supplied (selected frame supplied),result frame supplied,completeWritten frame supplied)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

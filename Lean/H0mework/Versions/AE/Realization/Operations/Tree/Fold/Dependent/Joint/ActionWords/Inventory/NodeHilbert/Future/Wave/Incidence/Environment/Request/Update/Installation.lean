import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Request.Update.Laws
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable (frame : Frame.{u})
def reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (_occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) := raw frame
def result {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) occurrence
def written {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :=
 SourceHistoryCommon.seed (Request.written frame)
  (SourceHistoryCommon.seed (SourceOperationPaidRelations.exposure (fullTrace frame))
   (SourceOperationPaidRelations.exposure (result frame occurrence).2.1.2))
def material {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :=
 (sourceMaterial frame,binding frame,raw frame,fullTrace frame,result frame occurrence,written frame occurrence)
def component : SourceNativeProjectionLaw
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ => type_of% (material frame occurrence)
 project := fun _ {_current} occurrence _ => material frame occurrence
def programme := {Request.programme.{u} with
 datum := fun sourceFrame => {
  component := some (component sourceFrame)
  reader := reader sourceFrame
  nextEnvironmentRead := (Disposition.programme.datum sourceFrame).nextEnvironmentRead
  nextEnvironmentReadAt := (Disposition.programme.datum sourceFrame).nextEnvironmentReadAt }
 nextPairInventory := fun sourceFrame => some (((component (A.epoch sourceFrame)).project PUnit.unit
  (Shared.actualOccurrence sourceFrame) PUnit.unit).2.2.2.2.2) }
def installed := (SourceNativeProjectionLaw.InstallationAt.componentCoface
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base (component (A.epoch frame))).trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (Shared.baseRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch frame) programme)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame programme).source.base
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch frame) programme))
def sourceFace : SourceNativeRootSemanticFaceAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.root frame programme)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme) where
 projection := (installed frame).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable (frame : Frame.{u})
def localEnvironment := nextEnvironmentRead frame ((runtime frame).stateAt 0)
def queryRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=SourceOperationScalarInventoryLift.PairValue Value.{u}) (Var:=Var.{u}) (sort:=Slot.orbit) :=
 ⟨SourceOperationScalarInventoryLift.pairEnvironment frame.rawRead.environment
   (localEnvironment frame-frame.rawRead.environment),
  SourceOperationScalarInventoryLift.liftExpr PaidSourceMacroHistory.programme.{u}⟩
def queryReader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (_occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) := queryRaw frame
abbrev queryResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
 (queryReader frame) (Shared.actualOccurrence frame)
theorem query_value : (queryResult frame).2.2.1=
 (PaidSourceMacroHistory.programme.{u}.eval frame.rawRead.environment,
 PaidSourceMacroHistory.programme.{u}.effect frame.rawRead.environment (localEnvironment frame-frame.rawRead.environment)) := by
 exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
  (queryReader frame) (Shared.actualOccurrence frame)).trans
  (SourceOperationScalarInventoryLift.eval_liftExpr _ _ _)
def component : SourceNativeProjectionLaw
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit.{u+1} ⊕ PUnit.{u+1}
 ActiveAt := fun _ {_current} _ => PUnit.{u+1}
 InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun projection {_current} _ _ => match projection with
  | .inl _ => type_of% ((WriteBack.component frame).project PUnit.unit (Shared.actualOccurrence frame) PUnit.unit) ×
    (Nat → Env Value.{u} Var.{u}) × type_of% (queryRaw frame,queryResult frame)
  | .inr _ => Env Value.{u} Var.{u}
 project := fun projection {_current} _ _ => match projection with
  | .inl _ => (((WriteBack.component frame).project PUnit.unit (Shared.actualOccurrence frame) PUnit.unit),
    (fun depth => localEnvironment (WriteBack.stage frame depth)),(queryRaw frame,queryResult frame))
  | .inr _ => localEnvironment frame
def programme := {WriteBack.programme.{u} with
 datum := fun sourceFrame => {
  component := some (component sourceFrame)
  reader := (WriteBack.programme.datum sourceFrame).reader
  nextEnvironmentRead := (WriteBack.programme.datum sourceFrame).nextEnvironmentRead
  nextEnvironmentReadAt := (WriteBack.programme.datum sourceFrame).nextEnvironmentReadAt }
 nextPairInventory := fun sourceFrame => some (SourceHistoryCommon.seed (WriteBack.installedWritten sourceFrame)
  (SourceOperationPaidRelations.exposure (((component (A.epoch sourceFrame)).project (.inl PUnit.unit)
   (Shared.actualOccurrence sourceFrame) PUnit.unit).2.2.2).2.1.2)) }
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
 projection := (installed frame).embed (.inl PUnit.unit)
 active := PUnit.unit
 classifier_eq := rfl
abbrev environmentAtDepth (depth : Nat) := (sourceFace frame).rootRead.2.1 depth
theorem local_environment : localEnvironment frame=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame WriteBack.programme).rawRead.environment :=
 (next_environment frame ((runtime frame).stateAt 0)).trans
  (Configured.environment_actual frame WriteBack.programme 1)
theorem installed_environment (depth : Nat) : environmentAtDepth frame depth=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next (WriteBack.stage frame depth) WriteBack.programme).rawRead.environment :=
 local_environment (WriteBack.stage frame depth)
abbrev written := SourceHistoryCommon.seed (WriteBack.installedWritten frame)
 (SourceOperationPaidRelations.exposure ((sourceFace frame).rootRead.2.2.2).2.1.2)
theorem born_inventory : (Shared.nextBorn frame programme).pairInventory=some (written frame) := rfl
theorem inherited_inventory (event)
 (present : event ∈ (WriteBack.installedWritten frame).trace) : event ∈ (written frame).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem query_trace_written (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure ((sourceFace frame).rootRead.2.2.2).2.1.2).trace) :
 event ∈ (written frame).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem actual_next_environment :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).rawRead.environment=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame WriteBack.programme).rawRead.environment := by
 rw [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment,
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment]
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 cases frame.action <;> rfl
abbrev installedRuntime (initialFrame : Frame.{u}) := Shared.runtime initialFrame programme
abbrev installedGenerated (initialFrame : Frame.{u}) := (installedRuntime initialFrame,
 Configured.withActualFaces initialFrame programme,
 fun stage => (sourceFace (Shared.frames initialFrame programme stage),(generated (Shared.frames initialFrame programme stage) 0).canonical,
  (generated (Shared.frames initialFrame programme stage) 0).embedding,
  (sourceFace (Shared.frames initialFrame programme stage)).rootRead.2.2),
 WriteBack.generated initialFrame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

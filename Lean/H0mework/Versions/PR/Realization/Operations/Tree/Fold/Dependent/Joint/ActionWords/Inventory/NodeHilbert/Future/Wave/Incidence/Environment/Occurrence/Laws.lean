import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedOccurrenceNextRaw
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {S : Type u} {A X : S → Type u} [∀ slot,AddCommGroup (A slot)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=A) (Var:=X) (sort:=slot))
variable (programme : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=A) (PhysicalVar:=X) (sort:=slot))
theorem actual : SourceOperationInquiry.Context.Installation.nextRawAt frame
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).rawRead := by
 apply (SourceOperationInquiry.Context.Installation.next_raw_source frame).trans
 unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 cases frame.action with
 | inr paid => rfl
 | inl settled => rfl
end SourceGeneratedOccurrenceNextRaw
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable (frame : Frame.{u})
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem epoch_material : physical (A.epoch frame) occurrence=physical frame occurrence := by
 dsimp only [SourceOperationInquiry.Context.Faces.Execution.Activation.epoch]
 rcases occurrence with ⟨support,event⟩
 cases event
 unfold physical SourceOperationInquiry.Context.Installation.materialAt
  SourceOperationInquiry.Context.Installation.nextRawAt SourceOperationInquiry.Context.Installation.rawAt
  SourceOperationInquiry.Context.Installation.residualAt
 cases RootGeneratedDebtActivationJointSource.mathAction current.2 <;> rfl
theorem current_state : HEq (physical frame occurrence).paid.state current.2.state := by
 rcases occurrence with ⟨support,event⟩
 cases event
 exact HEq.rfl
theorem next_raw (programme : A.Programme (PhysicalValue:=Value.{u}) (PhysicalVar:=Var.{u}) (sort:=Slot.orbit)) :
 (physical (A.epoch frame) (Shared.actualOccurrence frame)).nextRaw=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).rawRead := by
 apply (congrArg (fun value => value.nextRaw) (epoch_material frame (Shared.actualOccurrence frame))).trans
 exact SourceGeneratedOccurrenceNextRaw.actual frame programme
theorem source_value : (result frame occurrence).2.2.1=(physical frame occurrence).pair :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) occurrence).trans
 (physical frame occurrence).pairTrace.sound
theorem source_original : HEq (physical frame occurrence).pairTrace
 (SourceOperationInquiry.Context.Installation.materialAt frame occurrence).pairTrace := HEq.rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

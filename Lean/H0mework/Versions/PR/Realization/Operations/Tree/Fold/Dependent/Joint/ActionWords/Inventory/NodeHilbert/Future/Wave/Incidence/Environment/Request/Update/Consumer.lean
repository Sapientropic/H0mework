import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Request.Update.Installation
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable (frame : Frame.{u})
theorem actual_query : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame programme).raw=
 (sourceFace frame).rootRead.2.2.1 := rfl
theorem actual_value : (Shared.resultFace frame programme).rootRead.2.2.1=(completed (A.epoch frame)).1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Shared.baseRoot frame programme).toAuthoritativeRoot (Shared.datum frame programme).reader (Shared.actualOccurrence frame)).trans
  (updated_value (A.epoch frame))
theorem actual_cost : (Shared.resultFace frame programme).rootRead.2.1.2.length=remaining (raw (A.epoch frame)).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem born_inventory : (Shared.nextBorn frame programme).pairInventory=some (sourceFace frame).rootRead.2.2.2.2.2 := rfl
theorem source_trace_written (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (fullTrace (A.epoch frame))).trace) :
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem old_inventory_written (event)
 (present : event ∈ (Request.written (A.epoch frame)).trace) :
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem actual_trace_written : ∀ event ∈ (SourceOperationPaidRelations.exposure
 (Shared.resultFace frame programme).rootRead.2.1.2).trace,
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.trace := by
 have exposure : SourceOperationPaidRelations.exposure (Shared.resultFace frame programme).rootRead.2.1.2=
  SourceOperationPaidRelations.exposure (result (A.epoch frame) (Shared.actualOccurrence frame)).2.1.2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
   (Shared.baseRoot frame programme).toAuthoritativeRoot
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme).current
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme).current
   (reader (A.epoch frame) (Shared.actualOccurrence frame))
 rw [exposure]
 exact fun event present => (SourceHistoryCommon.parallel_right _ _ _).1 event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
abbrev runtime (initialFrame : Frame.{u}) := Shared.runtime initialFrame programme
theorem canonical_next (initialFrame : Frame.{u}) (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initialFrame programme stage
theorem whole_current (initialFrame : Frame.{u}) (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage
theorem same_debt : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme frame
theorem noetherian : type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme frame) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme frame
abbrev generated (initialFrame : Frame.{u}) := (runtime initialFrame,Configured.withActualFaces initialFrame programme,
 fun stage => sourceFace (Shared.frames initialFrame programme stage),Request.generated initialFrame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request.Update
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

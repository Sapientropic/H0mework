import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Installation
import H0mework.Realization.Operations.Execution.Coefficients.Words
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable (frame : Frame.{u})
theorem actual_query : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame programme).raw=
 (sourceFace frame).rootRead.2.2.2.2.1 := rfl
theorem actual_value : (Shared.resultFace frame programme).rootRead.2.2.1=
 (0,(residualEquivRange (evaluation (R:=ℤ) (s:=Slot.orbit)
  ((before (A.epoch frame) (Shared.actualOccurrence frame))+(increment (A.epoch frame) (Shared.actualOccurrence frame))))
  (sourceFace frame).rootRead.2.2.2.1).val) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (Shared.baseRoot frame programme).toAuthoritativeRoot (Shared.datum frame programme).reader (Shared.actualOccurrence frame)).trans
 ((pair_value (A.epoch frame) (Shared.actualOccurrence frame)).trans
  (congrArg (fun effect : Value.{u} Slot.orbit => ((0:Value.{u} Slot.orbit),effect))
   (inverse_effect (A.epoch frame) (Shared.actualOccurrence frame)).symm))
theorem actual_cost : (Shared.resultFace frame programme).rootRead.2.1.2.length=
 SourceOperationExecution.Coefficients.cost (sourceFace frame).rootRead.2.2.1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
  (SourceOperationExecution.Coefficients.lifted_remaining _)
theorem actual_current_state : HEq (sourceFace frame).rootRead.1.2.1.paid.state frame.event.state :=
 current_state (A.epoch frame) (Shared.actualOccurrence frame)
theorem actual_next_raw : (sourceFace frame).rootRead.1.2.1.nextRaw=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame programme).rawRead :=
 next_raw frame programme
theorem born_inventory : (Shared.nextBorn frame programme).pairInventory=some (sourceFace frame).rootRead.2.2.2.2.2.2 := rfl
theorem old_inventory_written (event)
 (present : event ∈ (Occurrence.written (A.epoch frame) (Shared.actualOccurrence frame)).trace) :
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.2.trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem paid_trace_written (event)
 (present : event ∈ (paidInventory (A.epoch frame) (Shared.actualOccurrence frame)).trace) :
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.2.trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem actual_trace_written : ∀ event ∈ (SourceOperationPaidRelations.exposure
 (Shared.resultFace frame programme).rootRead.2.1.2).trace,
 event ∈ (sourceFace frame).rootRead.2.2.2.2.2.2.trace := by
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
abbrev runtime (initialFrame : Frame.{u}) := Shared.runtime initialFrame programme
abbrev generated (initialFrame : Frame.{u}) := (runtime initialFrame,Configured.withActualFaces initialFrame programme,
 fun stage => sourceFace (Shared.frames initialFrame programme stage),Occurrence.generated initialFrame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

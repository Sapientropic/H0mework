import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Disposition.Installation
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
theorem evaluator_source (word : SourceOperationScalarRelations.Formal ℤ (PairValue Value.{u}) Var.{u} Slot.orbit) :
 (face frame occurrence).freeEvaluation word=SourceOperationScalarRelations.evaluation (R:=ℤ)
  (Relations.raw frame occurrence).environment word := by
 classical
 induction word using Finsupp.induction with
 | zero => exact (face frame occurrence).freeEvaluation.map_zero
 | @single_add expression integer rest absent nonzero prior =>
  rw [map_add,map_add,freeEvaluation_single,prior]
  rw [SourceOperationScalarRelations.evaluation,Finsupp.linearCombination_single]
  rfl
theorem kernel_word_read (sound : GeneratedRelationSoundnessAt (face frame occurrence))
 (coordinate : GeneratedKernelResidualCoordinateAt (face frame occurrence) sound) :
 (history frame occurrence).completionProjection (kernelWord frame occurrence sound coordinate)=coordinate.coordinate.val :=
 Classical.choose_spec (Submodule.Quotient.mk_surjective (history frame occurrence).relationInGeneratorClosure coordinate.coordinate.val)
theorem kernel_word_value (sound : GeneratedRelationSoundnessAt (face frame occurrence))
 (coordinate : GeneratedKernelResidualCoordinateAt (face frame occurrence) sound) :
 SourceOperationScalarRelations.evaluation (R:=ℤ) (Relations.raw frame occurrence).environment
  (kernelWord frame occurrence sound coordinate).val=0 := by
 have read := congrArg ((face frame occurrence).completionEvaluation sound) (kernel_word_read frame occurrence sound coordinate)
 change (face frame occurrence).freeEvaluation (kernelWord frame occurrence sound coordinate).val=
  (face frame occurrence).completionEvaluation sound coordinate.coordinate.val at read
 exact (evaluator_source frame occurrence _).symm.trans (read.trans coordinate.maps_to_zero)
theorem unsound_query_value (obstruction : GeneratedUnsoundRelationObstructionAt (face frame occurrence))
 (coordinate : GeneratedRelationResidualCoordinateAt (face frame occurrence)) :
 (queryRaw frame occurrence (.unsound obstruction coordinate)).expression.eval
  (queryRaw frame occurrence (.unsound obstruction coordinate)).environment=coordinate.coordinate :=
 (SourceOperationExecution.Coefficients.expression_eval coordinate.relation (Relations.raw frame occurrence).environment).trans
  ((evaluator_source frame occurrence _).symm.trans coordinate.relation_image_eq.symm)
theorem coverage_query_value (sound : GeneratedRelationSoundnessAt (face frame occurrence))
 (obstruction : GeneratedCoverageResidualObstructionAt (face frame occurrence) sound)
 (coordinate : GeneratedCoverageResidualCoordinateAt (face frame occurrence) sound) :
 (queryRaw frame occurrence (.coverageResidual sound obstruction coordinate)).expression.eval
  (queryRaw frame occurrence (.coverageResidual sound obstruction coordinate)).environment=coordinate.representative := rfl
theorem written_preserves (disposition : ResidualDispositionOutcome (face frame occurrence)) :
 ∀ event ∈ (Relations.written frame occurrence).trace,event ∈ (written frame occurrence disposition).trace := by
 cases disposition with
 | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact fun _ present => present
 | kernelResidual _ _ _ => exact (SourceHistoryCommon.parallel_left _ _ _).1
theorem complete_preserves : ∀ event ∈ (Relations.written frame occurrence).trace,event ∈ (completeWritten frame occurrence).trace :=
 fun event present => (SourceHistoryCommon.parallel_left _ _ _).1 event (written_preserves frame occurrence _ event present)
theorem paid_query_preserves : ∀ event ∈ (SourceOperationPaidRelations.exposure (result frame occurrence).2.1.2).trace,
 event ∈ (completeWritten frame occurrence).trace :=
 fun event present => (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem actual_value : (Shared.resultFace frame programme).rootRead.2.2.1=
 ((sourceFace frame).rootRead.2.2.2.2.1.expression).eval (sourceFace frame).rootRead.2.2.2.2.1.environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem actual_cost : (Shared.resultFace frame programme).rootRead.2.1.2.length=
 remaining (sourceFace frame).rootRead.2.2.2.2.1.expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem actual_query_trace_written : ∀ event ∈ (SourceOperationPaidRelations.exposure
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
 exact paid_query_preserves (A.epoch frame) (Shared.actualOccurrence frame)
abbrev runtime (initialFrame : Frame.{u}) := Shared.runtime initialFrame programme
theorem canonical_query (initialFrame : Frame.{u}) (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initialFrame programme stage
theorem canonical_answer (initialFrame : Frame.{u}) (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initialFrame programme stage
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
 fun stage => sourceFace (Shared.frames initialFrame programme stage),Relations.generated initialFrame)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations.Disposition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

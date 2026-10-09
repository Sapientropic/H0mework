import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Installation
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Faces.Native.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
theorem actual_query : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame (programme configuration)).raw=
 raw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) := rfl
theorem actual_value : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame (programme configuration)).rootRead.2.2.1=
 (physicalResult (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.2.1 :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (programme configuration)).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame (programme configuration)).reader
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trans
 ((binding_value (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trans
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
   (J.queryReader (seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).symm)
theorem original_low_trace (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (lowResult frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.1.2).trace) :
 event ∈ (completeWritten frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_left _ _ _).1 event present)
theorem converted_trace (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (result frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.1.2).trace) :
 event ∈ (completeWritten frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem migrated_trace (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (migratedTrace frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame))).trace) :
 event ∈ (completeWritten frame configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem actual_trace_written : ∀ event ∈ (SourceOperationPaidRelations.exposure
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame (programme configuration)).rootRead.2.1.2).trace,
 event ∈ (completeWritten (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).trace := by
 have exposure : SourceOperationPaidRelations.exposure
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultFace frame (programme configuration)).rootRead.2.1.2=
  SourceOperationPaidRelations.exposure (result (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.1.2 :=
  RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame (programme configuration)).toAuthoritativeRoot
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame (programme configuration)).current
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame (programme configuration)).current
   (reader (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame))
 rw [exposure]
 exact fun event present => (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event present)
theorem born_source_inventory : HEq
 ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
  ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.oldProjection
   ((installed frame configuration).embed PUnit.unit))
  ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetRoot.emitted
   (SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetInitialVisit.current))
 (sourceOutcome frame configuration) :=
 (SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.oldOutcome_heq
  ((installed frame configuration).embed PUnit.unit)
theorem born_complete_inventory : HEq
 ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
  ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.oldProjection
   ((installed frame configuration).embed PUnit.unit))
  ((SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetRoot.emitted
   (SourceGeneratedInquiryReceiptAction.generatedAction frame (programme configuration)).target.targetInitialVisit.current))
 (Sum.inl (β:=PEmpty.{u+1}) (⟨PUnit.unit,completeMaterial (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)⟩ :
  Sigma fun active : (stockLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration).ActiveAt PUnit.unit
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) =>
   (stockLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration).PayloadAt PUnit.unit
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) active)) :=
 (born_source_inventory frame configuration).trans (source_inventory frame configuration)
theorem decoder_preserved (pair : PairValue PhysicalValue slot) :
 (match (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame (programme configuration)).nextEnvironmentReadAt with
  | none => none
  | some read => some (read (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) pair))=
 (match (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).nextEnvironmentReadAt with
  | some read => some (read (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)
   (lowResult (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.2.1)
  | none => (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame configuration).nextEnvironmentRead.map
   (fun read => read (lowResult (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) configuration
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)).2.2.1)) := by
 dsimp only [SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,programme]
 cases (configuration.datum (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)).nextEnvironmentReadAt with
 | some read => rfl
 | none =>
  cases (configuration.datum (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)).nextEnvironmentRead <;> rfl
abbrev generated := (SourceGeneratedInquiryReceiptAction.actualGenerated frame (programme configuration),sourceOutcome frame configuration)
abbrev nativeGenerated (stage : Nat) :=
 (Faces.Native.generated frame configuration stage,
  generated (Faces.Native.nativeFrame frame configuration stage) Faces.Native.R.programme)
end SourceGeneratedInquiryReceiptAction.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

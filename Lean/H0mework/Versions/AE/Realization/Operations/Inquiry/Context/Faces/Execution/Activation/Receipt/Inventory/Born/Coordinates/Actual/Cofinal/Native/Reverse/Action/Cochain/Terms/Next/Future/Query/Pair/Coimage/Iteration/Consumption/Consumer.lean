import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Consumption.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Carried
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Consumption
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage count iterations : Nat)
namespace B
export Inventory.Born (stock_source actual_disposition actual_query actual_update actual_inverse whole_first literal_next no_refill noetherian)
end B
namespace I
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (prior_seed_preserved updatedSeed priorSeed)
end I
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (configuration disposition complete_written_preserves)
end J
abbrev selected := J.disposition (Inventory.Born.seed (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (bornFrame frame configuration sourceStage stage count iterations))
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence (bornFrame frame configuration sourceStage stage count iterations))
theorem paid_steps : (SourceOperationPaidRelations.words (Iteration.result frame configuration sourceStage stage count iterations).2.1.2).length=
 (Iteration.result frame configuration sourceStage stage count iterations).2.1.2.length := SourceOperationPaidRelations.complete_steps _
theorem paid_event (event) (present : event ∈ (queryExposure frame configuration sourceStage stage count iterations).trace) :
 event ∈ (prior frame configuration sourceStage stage count iterations).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem source_event (event) (present : event ∈ (sourceExposure frame configuration sourceStage stage count iterations).trace) :
 event ∈ (prior frame configuration sourceStage stage count iterations).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem source_inventory : (sourceFrame frame configuration sourceStage stage count iterations).inventory=some (prior frame configuration sourceStage stage count iterations) := rfl
theorem carried_born (event) (present : event ∈ (prior frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (inventory frame configuration sourceStage stage count iterations).trace := by
 apply Inventory.Born.physical_event
 rw [Inventory.Born.original_physical_inventory]
 exact Inventory.Carried.input_carried_written _ _ (source_inventory frame configuration sourceStage stage count iterations) event present
theorem source_step_born (event)
 (present : event ∈ (sourceExposure frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (inventory frame configuration sourceStage stage count iterations).trace :=
 carried_born frame configuration sourceStage stage count iterations event (source_event frame configuration sourceStage stage count iterations event present)
theorem prefix_step_born (index : Fin (iterations+1)) (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (O.trace (Future.runtime frame configuration sourceStage stage)
  (Future.source frame configuration sourceStage stage) (Query.state frame configuration sourceStage stage count)
  (Query.expression frame configuration sourceStage stage count) index.val)).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (inventory frame configuration sourceStage stage count iterations).trace :=
 source_step_born frame configuration sourceStage stage count iterations event
  (Iteration.complete_inventory frame configuration sourceStage stage count iterations index event present)
theorem paid_step_born (event) (present : event ∈ (queryExposure frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (inventory frame configuration sourceStage stage count iterations).trace :=
 carried_born frame configuration sourceStage stage count iterations event (paid_event frame configuration sourceStage stage count iterations event present)
theorem carried_cofinal (event) (present : event ∈ (prior frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (Inventory.Born.Coordinates.combined (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace :=
 Inventory.Born.cofinal_input _ _ _ (carried_born frame configuration sourceStage stage count iterations event present)
theorem carried_written (event) (present : event ∈ (prior frame configuration sourceStage stage count iterations).trace) :
 Inventory.Born.migratedEvent (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme (R.liftEvent event) ∈
 (Inventory.Born.Coordinates.written (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.relation_write_preserves
 _ _ _ _ _ (carried_cofinal frame configuration sourceStage stage count iterations event present)
theorem carried_actual_next (event) (present : event ∈ (inventory frame configuration sourceStage stage count iterations).trace) :
 event ∈ (Inventory.Born.Coordinates.Actual.actualInventory (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace := by
 have indexed :=  List.mem_iff_get.mp present
 rcases indexed with ⟨index,same⟩
 have read := Inventory.Born.Coordinates.Actual.actual_event_read
  (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme index
 have belongs := List.get_mem (Inventory.Born.Coordinates.Actual.actualInventory
  (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme).trace
  (Inventory.Born.Coordinates.Actual.intoActual (sourceFrame frame configuration sourceStage stage count iterations)
   SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme index)
 exact (read.trans same) ▸ belongs
theorem born_stock : type_of% (B.stock_source (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.stock_source _ _
theorem actual_disposition : type_of% (B.actual_disposition (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.actual_disposition _ _
theorem actual_query : type_of% (B.actual_query (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.actual_query _ _
theorem actual_update : type_of% (B.actual_update (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.actual_update _ _
theorem actual_inverse : type_of% (B.actual_inverse (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.actual_inverse _ _
theorem whole_first : type_of% (B.whole_first (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.whole_first _ _
theorem literal_next : type_of% (B.literal_next (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.literal_next _ _
theorem no_refill : type_of% (B.no_refill (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.no_refill _ _
theorem noetherian : type_of% (B.noetherian (sourceFrame frame configuration sourceStage stage count iterations)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := B.noetherian _ _
abbrev generatedActual := (generated frame configuration sourceStage stage count iterations,
 Inventory.Born.Coordinates.Actual.generated (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
theorem complete_next_query (index : Inventory.Born.Coordinates.Actual.ActualIndex
 (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :
 type_of% (Inventory.Born.Coordinates.Actual.result_coordinate
  (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme index) :=
 Inventory.Born.Coordinates.Actual.result_coordinate _ _ index
theorem old_next_query (index : Inventory.Born.Vector.Index
 (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :
 type_of% (Inventory.Born.Coordinates.Actual.old_coordinate
  (sourceFrame frame configuration sourceStage stage count iterations)
  SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme index) :=
 Inventory.Born.Coordinates.Actual.old_coordinate _ _ index
theorem next_occurrence_injective : Function.Injective (Inventory.Born.Coordinates.Actual.intoActual
 (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :=
 Inventory.Born.Coordinates.Actual.actual_injective _ _
theorem complete_next_whole : type_of% (Inventory.Born.Coordinates.Actual.mother_whole
 (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :=
 Inventory.Born.Coordinates.Actual.mother_whole _ _
theorem complete_next_next : type_of% (Inventory.Born.Coordinates.Actual.mother_next
 (sourceFrame frame configuration sourceStage stage count iterations) SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) :=
 Inventory.Born.Coordinates.Actual.mother_next _ _
abbrev nativeGenerated (nativeStage : Nat) := (Iteration.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage count iterations => generatedActual (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage count iterations)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future.Query.Pair.Coimage.Iteration.Consumption
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

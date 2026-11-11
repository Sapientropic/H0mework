import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Pair.Transport
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.SegmentRead

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.PairTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement

namespace IP
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme (priorSeed updatedSeed)
end IP
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end P

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (frame : A.M.Frame (Value := V) (Var := X) (sort := s))
variable (carried : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X s)))
variable (registered : frame.inventory = some carried)
local notation "epoch" => A.epoch frame
local notation "occurrence" => Q.actualOccurrence frame

/-- The carried scalar stock enters the actual written Joint at a single exact offset. -/
def installedScalarSegment : SourceInventoryTraceSegment (carried.map P.liftEvent)
    (P.J.completeWrittenInventory seed epoch occurrence) := by
  have initial : SourceInventoryTraceSegment carried (IP.priorSeed seed epoch) := by
    unfold IP.priorSeed
    rw [show (epoch).inventory = some carried from registered]
    exact .right _ _
  let updated : SourceInventoryTraceSegment carried (IP.updatedSeed seed epoch occurrence) :=
    initial.trans (.left _ _)
  let lifted : SourceInventoryTraceSegment (carried.map P.liftEvent) (P.liftedInventory seed epoch occurrence) :=
    updated.map P.liftEvent
  have priorPair : SourceInventoryTraceSegment (P.liftedInventory seed epoch occurrence)
      (P.priorPairInventory seed epoch occurrence) := by
    change SourceInventoryTraceSegment (P.liftedInventory seed epoch occurrence)
      (match frame.pairInventory with
       | none => P.liftedInventory seed epoch occurrence
       | some previous => SourceHistoryCommon.seed previous (P.liftedInventory seed epoch occurrence))
    cases frame.pairInventory with
    | none => exact .refl _
    | some previous => exact .right previous _
  let pair : SourceInventoryTraceSegment (carried.map P.liftEvent) (P.pairInventory seed epoch occurrence) :=
    (lifted.trans priorPair).trans (.left _ _)
  exact pair.trans (dispositionSegment seed frame)

end SourceGeneratedInquiryReceiptAction.Configured.PairTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

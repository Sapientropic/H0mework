import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Receipt
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
local instance inventoryGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
private theorem source_preserve_right {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) :
 event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve old next).trace := by
 cases old with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem source_preserve_left {α : Type} (old next : RootedAccountedUnfolding α)
 (event : α) (present : event∈old.trace) :
 event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve (some old) next).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance inventoryBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance inventoryNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

theorem continuation_source_nodes_in_born (event)
 (present : event∈(SourceOperationPaidRelations.exposure
  (continuationSourceTrace t factory packet (continuationSourceSelected t factory packet))).trace) :
 event∈((continuationSourceBorn t factory packet).inventory.get (by rfl)).trace := by
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve (continuationSourceSelected t factory packet).inventory
  (OriginalKSourceFeedbackSuccessorAction.Stock.preserve
   (some (TraceSource.preserve ((continuationSourceEmitter t factory packet).nextInventory (continuationSourceSelected t factory packet))
    (SourceOperationPaidRelations.exposure (continuationSourceTrace t factory packet (continuationSourceSelected t factory packet)))))
   (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedStock (continuationSourceSelected t factory packet)))).trace
 apply source_preserve_right
 apply source_preserve_left
 exact source_preserve_right _ _ _ present

theorem continuation_source_pair_nodes_in_born (event)
 (present : event∈(SourceOperationPaidRelations.exposure
  (continuationSourcePairTrace t factory packet (continuationSourceSelected t factory packet))).trace) :
 event∈((continuationSourceBorn t factory packet).pairInventory.get (by rfl)).trace := by
 change event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve (continuationSourceSelected t factory packet).pairInventory
  (OriginalKSourceFeedbackSuccessorAction.Stock.preserve
   (some (TraceSource.preserve ((continuationSourceEmitter t factory packet).nextPairInventory (continuationSourceSelected t factory packet))
    (SourceOperationPaidRelations.exposure (continuationSourcePairTrace t factory packet (continuationSourceSelected t factory packet)))))
   (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.generatedPairStock (continuationSourceSelected t factory packet)))).trace
 apply source_preserve_right
 apply source_preserve_left
 exact source_preserve_right _ _ _ present
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

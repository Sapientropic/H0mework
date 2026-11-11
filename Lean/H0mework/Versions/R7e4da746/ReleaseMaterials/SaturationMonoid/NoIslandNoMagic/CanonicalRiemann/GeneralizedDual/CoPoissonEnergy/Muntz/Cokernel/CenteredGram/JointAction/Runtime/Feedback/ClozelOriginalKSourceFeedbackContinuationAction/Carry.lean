import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Inventory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryStock
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock (scalar_legacy_preserved legacyStock)
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
local instance carryGroups (grade : Nat) (target : Unit) : AddCommGroup
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

namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (scalar pair)
end AS
namespace LowerStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock
 (scalar pair carried_scalar)
end LowerStock
namespace SourceStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (liftEvent physicalPrior pairPrior mapped_trace)
end SourceStock
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Frames
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end Frames

private theorem receipt_scalar_preserved
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 (Complete.atReceipt cfg initial 0).inventory=initial.inventory := by
 apply Prefix.receipt_read cfg initial (fun stage => (Frames.frames initial cfg stage).inventory)
 intro stage paid actual
 have next : Frames.frames initial cfg (stage+1)=(Frames.frames initial cfg stage).mathNext := by
  change Frames.next _ _=_
  unfold Frames.next
  rw [actual]
 exact (congrArg (fun candidate : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Value) (Var:=Var) (sort:=()) => candidate.inventory) next).trans rfl

private theorem receipt_pair_preserved
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 (Complete.atReceipt cfg initial 0).pairInventory=initial.pairInventory := by
 apply Prefix.receipt_read cfg initial (fun stage => (Frames.frames initial cfg stage).pairInventory)
 intro stage paid actual
 have next : Frames.frames initial cfg (stage+1)=(Frames.frames initial cfg stage).mathNext := by
  change Frames.next _ _=_
  unfold Frames.next
  rw [actual]
 exact (congrArg (fun candidate : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Value) (Var:=Var) (sort:=()) => candidate.pairInventory) next).trans rfl

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance carryBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance carryNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

/-- Every existing current scalar node is lifted by the original source carrier, preserved through its actual paid receipt, then retained by this born stock. -/
theorem continuation_old_scalar_nodes_in_born
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) C.Var ())))
 (actual : (Parent.actualNextSourceFrame t factory packet).inventory=some prior)
 (event) (present : event∈prior.trace) :
 SourceStock.liftEvent event∈((continuationSourceBorn t factory packet).inventory.get (by rfl)).trace := by
 have original := LowerStock.carried_scalar (Parent.actualNextSourceFrame t factory packet)
  (actualCurrentSourceBase t factory packet) rfl prior actual event present
 have atReceiver : SourceStock.liftEvent event∈(AS.scalar (actualCurrentSourceFactory t factory packet) 0
  (actualCurrentSourceData t factory packet) (actualCurrentSourceBase t factory packet) rfl).trace :=
  scalar_legacy_preserved (actualCurrentSourceFactory t factory packet) 0
   (actualCurrentSourceData t factory packet) (actualCurrentSourceBase t factory packet) rfl
   (SourceStock.liftEvent event) (source_preserve_right _ _ _ original)
 have preserved := receipt_scalar_preserved (AS.stockCfg (continuationSourceStockEmitter t factory packet))
  (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
   (actualCurrentSourceBase t factory packet) rfl)
 have hasSelected : (continuationSourceSelected t factory packet).inventory=
  some (AS.scalar (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
   (actualCurrentSourceBase t factory packet) rfl) := preserved
 apply SourceInventoryExecutionFeed.original_preserved
 change SourceStock.liftEvent event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve
  (continuationSourceSelected t factory packet).inventory _).trace
 rw [hasSelected]
 exact source_preserve_left _ _ _ atReceiver

/-- Paired source nodes retain their typed second lift, not an untyped inventory count. -/
theorem continuation_old_pair_nodes_in_born
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (PairValue (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1)) C.Var ())))
 (actual : (Parent.actualNextSourceFrame t factory packet).pairInventory=some prior)
 (event) (present : event∈prior.trace) :
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent event∈
  ((continuationSourceBorn t factory packet).pairInventory.get (by rfl)).trace := by
 let lift := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.liftEvent
  (PhysicalValue:=PairValue (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1))
  (PhysicalVar:=C.Var) (sort:=())
 have mapped : lift event∈(prior.map lift).trace := by
  rw [SourceStock.mapped_trace]
  exact List.mem_map_of_mem present
 have original : lift event∈(LowerStock.pair (Parent.actualNextSourceFrame t factory packet)
  (actualCurrentSourceBase t factory packet) rfl).trace := by
  unfold LowerStock.pair SourceStock.pairPrior
  rw [actual]
  exact source_preserve_left _ _ _ mapped
 have atReceiver : lift event∈(AS.pair (actualCurrentSourceFactory t factory packet) 0
  (actualCurrentSourceData t factory packet) (actualCurrentSourceBase t factory packet) rfl).trace :=
  source_preserve_right _ _ _ original
 have preserved := receipt_pair_preserved (AS.stockCfg (continuationSourceStockEmitter t factory packet))
  (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
   (actualCurrentSourceBase t factory packet) rfl)
 have hasSelected : (continuationSourceSelected t factory packet).pairInventory=
  some (AS.pair (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
   (actualCurrentSourceBase t factory packet) rfl) := preserved
 change lift event∈(OriginalKSourceFeedbackSuccessorAction.Stock.preserve
  (continuationSourceSelected t factory packet).pairInventory _).trace
 rw [hasSelected]
 exact source_preserve_left _ _ _ atReceiver
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock.Return
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Frame.Stock.Coordinates
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open RootInquiryCompletion CofinalHistorySettlement
namespace R
export SourceOperationInquiry.Context.Native.Frame.Stock.Return (written new_event_born)
end R
namespace B
export SourceGeneratedInquiryReceiptAction.Inventory.Born (inventory)
end B
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory
 (reader lowResult result written migratedTrace completeWritten)
end I
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot visit actualOccurrence)
end Shared
namespace H
export SourceHistoryCommon.Coordinates (left right left_read right_read left_injective right_injective)
end H
-- Keep the whole tree equality in the index transport; unfolding a dependent
-- List/Fin transport can expand the complete source root during kernel checking.
private theorem cast_get {α : Type u} {first second : RootedAccountedUnfolding α}
 (same : first=second) (index : Fin first.trace.length) :
 second.trace.get (Fin.cast (congrArg (fun tree => tree.trace.length) same) index)=
 first.trace.get index := by
 cases same
 rfl

private theorem cast_value {α : Type u} {first second : RootedAccountedUnfolding α}
 (same : first=second) (index : Fin first.trace.length) :
 (Fin.cast (congrArg (fun tree => tree.trace.length) same) index).val=index.val := rfl

private theorem seeded_value {α : Type u}
 (old newer migrated physical : RootedAccountedUnfolding α) (index : Fin newer.trace.length) :
 (H.right physical (SourceHistoryCommon.seed (SourceHistoryCommon.seed old newer) migrated)
  (H.left (SourceHistoryCommon.seed old newer) migrated (H.right old newer index))).val=
 index.val+old.trace.length+1+1+physical.trace.length+1 := rfl

private theorem ordered_value {n m : Nat} (f : Fin n → Fin m) (a b : Nat)
 (value : ∀ index, (f index).val=index.val+a+1+1+b+1) : StrictMono f := by
 intro i j less
 change (f i).val<(f j).val
 rw [value,value]
 omega

variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=W) (Var:=X) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))

abbrev origin := SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame
abbrev sourceOccurrence := Shared.actualOccurrence frame
abbrev oldWritten := SourceOperationPaidRelations.exposure
 (I.lowResult (origin frame) cfg (sourceOccurrence frame)).2.1.2
abbrev sourceWritten := SourceOperationPaidRelations.exposure
 (I.result (origin frame) cfg (sourceOccurrence frame)).2.1.2
abbrev migratedWritten := SourceOperationPaidRelations.exposure
 (I.migratedTrace (origin frame) cfg (sourceOccurrence frame))
abbrev physicalWritten :=
 (SourceGeneratedInquiryReceiptAction.Inventory.Born.physicalInventory frame cfg).map
  (SourceGeneratedInquiryReceiptAction.Inventory.Born.migratedEvent frame cfg)

-- The same supplied occurrence, read through the installed cofaces, has one whole exposure.
theorem source_exposure : R.written frame cfg=sourceWritten frame cfg :=
 RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
  (Shared.baseRoot frame (SourceGeneratedInquiryReceiptAction.Inventory.programme cfg)).toAuthoritativeRoot
  (Shared.visit frame (SourceGeneratedInquiryReceiptAction.Inventory.programme cfg)).current
  (Shared.base frame).root.toAuthoritativeRoot
  (Shared.visit frame (SourceGeneratedInquiryReceiptAction.Inventory.programme cfg)).current
  (I.reader (origin frame) cfg (sourceOccurrence frame))

def sourceIndex (index : Fin (R.written frame cfg).trace.length) :
 Fin (sourceWritten frame cfg).trace.length :=
 Fin.cast (congrArg (fun tree => tree.trace.length) (source_exposure frame cfg)) index

def completeIndex (index : Fin (R.written frame cfg).trace.length) :
 Fin (I.completeWritten (origin frame) cfg (sourceOccurrence frame)).trace.length :=
 H.left (I.written (origin frame) cfg (sourceOccurrence frame)) (migratedWritten frame cfg)
  (H.right (oldWritten frame cfg) (sourceWritten frame cfg) (sourceIndex frame cfg index))

theorem inventory_source : B.inventory frame cfg=
 SourceHistoryCommon.seed (physicalWritten frame cfg)
  (I.completeWritten (origin frame) cfg (sourceOccurrence frame)) :=
 congrArg (SourceHistoryCommon.seed (physicalWritten frame cfg))
  (SourceGeneratedInquiryReceiptAction.Inventory.Born.original_low_inventory frame cfg)

abbrev canonicalInventory := SourceHistoryCommon.seed (physicalWritten frame cfg)
 (I.completeWritten (origin frame) cfg (sourceOccurrence frame))

def canonicalIndex (index : Fin (R.written frame cfg).trace.length) :
 Fin (canonicalInventory frame cfg).trace.length :=
 H.right (physicalWritten frame cfg)
  (I.completeWritten (origin frame) cfg (sourceOccurrence frame)) (completeIndex frame cfg index)

def intoBorn (index : Fin (R.written frame cfg).trace.length) : Fin (B.inventory frame cfg).trace.length :=
 Fin.cast (congrArg (fun tree => tree.trace.length) (inventory_source frame cfg).symm)
  (canonicalIndex frame cfg index)

theorem intoBorn_injective : Function.Injective (intoBorn frame cfg) := by
 intro i j same
 have canonical : canonicalIndex frame cfg i=canonicalIndex frame cfg j :=
  Fin.cast_injective _ same
 have complete : completeIndex frame cfg i=completeIndex frame cfg j :=
  H.right_injective (physicalWritten frame cfg)
   (I.completeWritten (origin frame) cfg (sourceOccurrence frame)) canonical
 have combined :
  H.right (oldWritten frame cfg) (sourceWritten frame cfg) (sourceIndex frame cfg i)=
  H.right (oldWritten frame cfg) (sourceWritten frame cfg) (sourceIndex frame cfg j) :=
  H.left_injective (I.written (origin frame) cfg (sourceOccurrence frame))
   (migratedWritten frame cfg) complete
 have source : sourceIndex frame cfg i=sourceIndex frame cfg j :=
  H.right_injective (oldWritten frame cfg) (sourceWritten frame cfg) combined
 exact Fin.cast_injective _ source

theorem sourceIndex_read (index : Fin (R.written frame cfg).trace.length) :
 (sourceWritten frame cfg).trace.get (sourceIndex frame cfg index)=
 (R.written frame cfg).trace.get index :=
 cast_get (source_exposure frame cfg) index

theorem completeIndex_read (index : Fin (R.written frame cfg).trace.length) :
 (I.completeWritten (origin frame) cfg (sourceOccurrence frame)).trace.get (completeIndex frame cfg index)=
 (R.written frame cfg).trace.get index :=
 (H.left_read (I.written (origin frame) cfg (sourceOccurrence frame)) (migratedWritten frame cfg)
  (H.right (oldWritten frame cfg) (sourceWritten frame cfg) (sourceIndex frame cfg index))).trans
 ((H.right_read (oldWritten frame cfg) (sourceWritten frame cfg) (sourceIndex frame cfg index)).trans
  (sourceIndex_read frame cfg index))

theorem canonical_read (index : Fin (R.written frame cfg).trace.length) :
 (canonicalInventory frame cfg).trace.get (canonicalIndex frame cfg index)=
 (R.written frame cfg).trace.get index :=
 (H.right_read (physicalWritten frame cfg)
  (I.completeWritten (origin frame) cfg (sourceOccurrence frame)) (completeIndex frame cfg index)).trans
 (completeIndex_read frame cfg index)

theorem intoBorn_read (index : Fin (R.written frame cfg).trace.length) :
 (B.inventory frame cfg).trace.get (intoBorn frame cfg index)=(R.written frame cfg).trace.get index :=
 (cast_get (inventory_source frame cfg).symm (canonicalIndex frame cfg index)).trans
 (canonical_read frame cfg index)

theorem intoBorn_value (index : Fin (R.written frame cfg).trace.length) :
 (intoBorn frame cfg index).val=
  index.val+(oldWritten frame cfg).trace.length+1+1+(physicalWritten frame cfg).trace.length+1 :=
 (cast_value (inventory_source frame cfg).symm (canonicalIndex frame cfg index)).trans
 ((seeded_value (oldWritten frame cfg) (sourceWritten frame cfg) (migratedWritten frame cfg)
   (physicalWritten frame cfg) (sourceIndex frame cfg index)).trans
  (congrArg (fun position => position+(oldWritten frame cfg).trace.length+1+1+
    (physicalWritten frame cfg).trace.length+1)
   (cast_value (source_exposure frame cfg) index)))

theorem intoBorn_strictMono : StrictMono (intoBorn frame cfg) :=
 ordered_value (intoBorn frame cfg) (oldWritten frame cfg).trace.length (physicalWritten frame cfg).trace.length
  (intoBorn_value frame cfg)

end SourceOperationInquiry.Context.Native.Frame.Stock.Coordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

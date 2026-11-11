import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Occurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SourceInventoryBlock

private def full {A : Type u} (tree : RootedAccountedUnfolding A) : OccurrenceBlock tree.trace tree.trace :=
 ⟨[],[],by simp only [List.nil_append,List.append_nil]⟩

private def seedLeft {A : Type u} (first second : RootedAccountedUnfolding A)
 (chunk : List A) (block : OccurrenceBlock chunk first.trace) :
 OccurrenceBlock chunk (SourceHistoryCommon.seed first second).trace := by
 rcases block with ⟨front,back,equal⟩
 refine ⟨first.root::front,back++second.trace,?_⟩
 change first.root::(first.trace++(second.trace++[]))=_
 rw [equal]
 simp only [List.append_nil,List.cons_append,List.append_assoc]

private def seedRight {A : Type u} (first second : RootedAccountedUnfolding A)
 (chunk : List A) (block : OccurrenceBlock chunk second.trace) :
 OccurrenceBlock chunk (SourceHistoryCommon.seed first second).trace := by
 rcases block with ⟨front,back,equal⟩
 refine ⟨first.root::(first.trace++front),back,?_⟩
 change first.root::(first.trace++(second.trace++[]))=_
 rw [equal]
 simp only [List.append_nil,List.cons_append,List.append_assoc]

private def preserveRight {A : Type u} (prior : Option (RootedAccountedUnfolding A))
 (generated : RootedAccountedUnfolding A) (chunk : List A)
 (block : OccurrenceBlock chunk generated.trace) :
 OccurrenceBlock chunk (T.preserve prior generated).trace := by
 cases prior with
 | none => exact block
 | some carried => exact seedRight carried generated chunk block

namespace SA
export ActualCofinalSourceAction (sourceLiftEvent nativePacket selected receipt paid_prefix_stocks)
end SA
namespace Lower
export ActualCofinalSourceAction.L (Value groups)
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock (scalar)
end Stock
end Lower
namespace SourceAS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (scalar)
end SourceAS

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target,AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) : AddCommGroup (Lower.Value W grade target) := Lower.groups W grade target

private def lowCarried
 (frame : A.M.Frame (Value:=W) (Var:=X) (sort:=s))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
 (same : cfg.LowVar=X)
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
 (present : frame.inventory=some prior) :
 OccurrenceBlock
  (prior.trace.map (fun event => same.symm ▸ ActualCofinalSourceAction.T.liftEvent event))
  (Lower.Stock.scalar frame cfg same).trace := by
 cases cfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at same
  cases same
  unfold Lower.Stock.scalar
  unfold SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.physicalPrior
  rw [present]
  change OccurrenceBlock _ (SourceHistoryCommon.seed
   (prior.map ActualCofinalSourceAction.T.liftEvent)
   (SourceGeneratedInquiryReceiptAction.Configured.lowWritten frame ⟨X,datum,inventory,pairInventory⟩)).trace
  have mapped := seedLeft (prior.map ActualCofinalSourceAction.T.liftEvent)
   (SourceGeneratedInquiryReceiptAction.Configured.lowWritten frame ⟨X,datum,inventory,pairInventory⟩)
   (prior.map ActualCofinalSourceAction.T.liftEvent).trace (full _)
  simpa only [ActualCofinalSourceAction.T.mapped_trace] using mapped

/-- The original packet's ordered inventory remains a constructor-selected contiguous block of its actual receiver. -/
def receiver
 (factory : ActualCofinalSourceAction.SF.Factory W X s)
 (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W:=W) (X:=X) (s:=s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W packet.1) X s)))
 (present : packet.2.1.1.inventory=some prior) :
 OccurrenceBlock (prior.trace.map (SA.sourceLiftEvent packet))
  (SourceAS.scalar factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).trace :=
 preserveRight _ _ _ (preserveRight _ _ _ (preserveRight _ _ _
  (lowCarried packet.2.1.1 packet.2.2.1 packet.2.2.2.down prior present)))

/-- Source construction and the unchanged paid prefix retain each old occurrence's exact ordered location before Feed execution. -/
def source
 (factory : ActualCofinalSourceAction.SF.Factory W X s)
 (packet : ActualCofinalSourceAction.AS.AdmissionPacket (W:=W) (X:=X) (s:=s))
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (Lower.Value W packet.1) X s)))
 (present : packet.2.1.1.inventory=some prior) :
 OccurrenceBlock (prior.trace.map (SA.sourceLiftEvent packet))
  (AS.stockScalar (SA.selected factory packet) (SA.nativePacket factory packet).2.2.1).trace := by
 have carried := (SA.paid_prefix_stocks factory packet (SA.receipt factory packet).1 (Nat.le_refl _)).1
 unfold AS.stockScalar
 rw [carried]
 exact seedLeft _ _ _ (receiver factory packet prior present)

end SourceInventoryBlock
end ActualNativeRelationTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

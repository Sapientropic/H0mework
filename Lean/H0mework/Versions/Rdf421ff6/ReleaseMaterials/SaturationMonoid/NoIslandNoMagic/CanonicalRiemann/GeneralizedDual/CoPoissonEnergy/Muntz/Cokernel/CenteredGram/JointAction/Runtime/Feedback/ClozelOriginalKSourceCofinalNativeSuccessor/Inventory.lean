import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Correction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryStock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock (scalar_legacy_preserved legacyStock)
namespace Native
export ActualCofinalSourceAction (bornStock bornPairStock sourceLiftEvent sourceLiftPairEvent
 old_event_in_born old_pair_event_in_born whole_paid_in_born generated_joint_in_born
 paid_prefix_stocks source_word_action_in_born)
end Native
namespace LowerStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock (scalar)
end LowerStock
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end T
namespace AS
export ActualCofinalSourceAction.AS (scalar)
end AS
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance inventoryFamilyGroups (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
variable (fixedFactory : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

private theorem preserve_new {α : Type} (old : Option (RootedAccountedUnfolding α))
 (generated : RootedAccountedUnfolding α) (event : α) (present : event∈generated.trace) :
 event∈(T.preserve old generated).trace := by
 cases old with
 | none=>exact present
 | some prior=>exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

/-- Literal source and syntax-correction events enter the actual born stock of this original packet. -/
theorem source_actual_written_nodes_in_born (event)
 (present : event∈(SourceGeneratedInquiryReceiptAction.Configured.lowWritten packet.2.1.1 packet.2.2.1).trace) :
 (packet.2.2.2.down.symm ▸ event : PresentedRelationEventAt
  (Expr (PairValue (L.Value W packet.1)) packet.2.2.1.LowVar ()))∈
 (Native.bornStock fixedFactory packet).trace := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory=>
  change lowVar=X at sameVar
  cases sameVar
  have lower : event∈(LowerStock.scalar data.1 ⟨X,datum,inventory,pairInventory⟩ rfl).trace :=
   preserve_new _ _ _ present
  have receiver : event∈(AS.scalar fixedFactory grade data ⟨X,datum,inventory,pairInventory⟩ rfl).trace :=
   scalar_legacy_preserved fixedFactory grade data ⟨X,datum,inventory,pairInventory⟩ rfl event
    (preserve_new _ _ _ lower)
  apply SourceInventoryExecutionFeed.original_preserved
  change event∈(T.preserve (Native.selected fixedFactory ⟨grade,data,⟨X,datum,inventory,pairInventory⟩,⟨rfl⟩⟩).inventory _).trace
  rw [(Native.paid_prefix_stocks fixedFactory ⟨grade,data,⟨X,datum,inventory,pairInventory⟩,⟨rfl⟩⟩ _ (Nat.le_refl _)).1]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event receiver

/-- The generated deltaWord is retained in the same actual born inventory, rather than erased by a scalar price. -/
theorem source_actual_correction_in_born (event)
 (present : event∈(Out.scalarStock packet.2.1.1 packet.2.2.1).trace) :
 (packet.2.2.2.down.symm ▸ event : PresentedRelationEventAt
  (Expr (PairValue (L.Value W packet.1)) packet.2.2.1.LowVar ()))∈
 (Native.bornStock fixedFactory packet).trace :=
 source_actual_written_nodes_in_born fixedFactory packet event
 (SourceGeneratedInquiryReceiptAction.Configured.outgoing_event_preserved _ _ _ present)

/-- Both prior inventories are carried by their actual native lifts. -/
theorem source_actual_prior_scalar
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value W packet.1) X ())))
 (actual : packet.2.1.1.inventory=some prior) (event) (present : event∈prior.trace) :
 Native.sourceLiftEvent packet event∈(Native.bornStock fixedFactory packet).trace :=
 Native.old_event_in_born _ _ _ actual _ present

theorem source_actual_prior_pair
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X ())))
 (actual : packet.2.1.1.pairInventory=some prior) (event) (present : event∈prior.trace) :
 Native.sourceLiftPairEvent packet event∈(Native.bornPairStock fixedFactory packet).trace :=
 Native.old_pair_event_in_born _ _ _ actual _ present

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

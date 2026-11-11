import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.TraceFactory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Native
export ActualCofinalSourceAction (bornStock bornPairStock selected paid_prefix_stocks)
end Native
namespace AS
export ActualCofinalSourceAction.AS (scalar pair)
end AS
private def hasSourceNode {α : Type} (stock : Option (RootedAccountedUnfolding α)) (event : α) : Prop :=
 ∃ stored,stock=some stored ∧ event∈stored.trace
private theorem source_preserve_old {α : Type} (prior : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : hasSourceNode prior event) :
 hasSourceNode (some (Stock.preserve prior next)) event := by
 rcases present with ⟨stored,same,belongs⟩
 rw [same]
 exact ⟨_,rfl,(SourceHistoryCommon.parallel_left _ _ _).1 event belongs⟩
private theorem source_preserve_new {α : Type} (prior : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) :
 hasSourceNode (some (Stock.preserve prior next)) event := by
 refine ⟨_,rfl,?_⟩
 cases prior with
 | none=>exact present
 | some stored=>exact (SourceHistoryCommon.parallel_right _ _ _).1 event present
private theorem source_fold_keeps {α β : Type} (trace : β→RootedAccountedUnfolding α) (codes : List β)
 (prior : Option (RootedAccountedUnfolding α)) (event : α) (present : hasSourceNode prior event) :
 hasSourceNode (codes.foldl (fun old code=>some (Stock.preserve old (trace code))) prior) event := by
 induction codes generalizing prior with
 | nil=>exact present
 | cons code rest ih=>exact ih _ (source_preserve_old _ _ _ present)
private theorem source_fold_adds {α β : Type} (trace : β→RootedAccountedUnfolding α) (codes : List β)
 (prior : Option (RootedAccountedUnfolding α)) (code : β) (installed : code∈codes)
 (event : α) (present : event∈(trace code).trace) :
 hasSourceNode (codes.foldl (fun old sourceCode=>some (Stock.preserve old (trace sourceCode))) prior) event := by
 induction codes generalizing prior with
 | nil=>cases installed
 | cons first rest ih=>
  rcases List.mem_cons.mp installed with same | later
  · subst first
    exact source_fold_keeps trace rest _ event (source_preserve_new _ _ _ present)
  · exact ih _ later
private theorem source_preserved_node {α : Type} (prior : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : hasSourceNode prior event) :
 event∈(Stock.preserve prior next).trace := by
 rcases present with ⟨stored,same,belongs⟩
 rw [same]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event belongs

variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance installedGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (mother : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

def sourceCompleteDifferentialFactory := sourceDifferentialFactory (sourceDifferentialTraceFactory mother)

def sourceCompleteDifferentialPacket := sourceDifferentialPacket (sourceDifferentialTraceFactory mother) packet

/-- Every actual same-source differential child is retained in its born scalar inventory. -/
theorem source_complete_scalar_nodes
 (code : Expr (PairValue (L.Value W packet.1)) X ()) (installed : code∈sourceMaterialAuxCodes packet.1 packet.2.1.1)
 (event : PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X ()))
 (present : event∈(SourceOperationPaidRelations.exposure (sourceMaterialAuxTrace packet.1 packet.2.1.1 code)).trace) :
 event∈(Native.bornStock (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet)).trace := by
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(Stock.preserve (Native.selected (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet)).inventory _).trace
 rw [(Native.paid_prefix_stocks (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet) _ (Nat.le_refl _)).1]
 have generated:=source_fold_adds
  (fun sourceCode=>SourceOperationPaidRelations.exposure (sourceMaterialAuxTrace packet.1 packet.2.1.1 sourceCode))
  (sourceMaterialAuxCodes packet.1 packet.2.1.1) (mother.extraScalar packet.1 packet.2.1.2 packet.2.1.1) code installed event present
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 apply SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock.scalar_legacy_preserved
 exact source_preserved_node _ _ _ generated

/-- The original query-zero lift records both feet honestly and keeps all typed source words in paired born stock. -/
theorem source_complete_pair_nodes
 (code : Expr (PairValue (L.Value W packet.1)) X ()) (installed : code∈sourceMaterialAuxCodes packet.1 packet.2.1.1)
 (event : PresentedRelationEventAt (Expr (PairValue (PairValue (L.Value W packet.1))) X ()))
 (present : event∈(SourceOperationPaidRelations.exposure (sourceMaterialAuxPairTrace packet.1 packet.2.1.1 code)).trace) :
 event∈(Native.bornPairStock (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet)).trace := by
 change event∈(Stock.preserve (Native.selected (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet)).pairInventory _).trace
 rw [(Native.paid_prefix_stocks (sourceCompleteDifferentialFactory mother) (sourceCompleteDifferentialPacket mother packet) _ (Nat.le_refl _)).2]
 have generated:=source_fold_adds
  (fun sourceCode=>SourceOperationPaidRelations.exposure (sourceMaterialAuxPairTrace packet.1 packet.2.1.1 sourceCode))
  (sourceMaterialAuxCodes packet.1 packet.2.1.1) (mother.extraPair packet.1 packet.2.1.2 packet.2.1.1) code installed event present
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 exact source_preserved_node _ _ _ generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

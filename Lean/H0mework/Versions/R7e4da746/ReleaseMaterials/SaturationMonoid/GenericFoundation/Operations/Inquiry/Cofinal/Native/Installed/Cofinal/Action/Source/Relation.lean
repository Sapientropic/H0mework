import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport.SourceRelationOccurrence
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace SA
export ActualCofinalSourceAction
  (SF.Factory AS.AdmissionPacket L.Value L.groups selected nativePacket bornStock
   sourceLiftEvent sourceWordAction source_word_action_relation)
end SA
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance levelGroups (grade : Nat) (target : Sorts) :
    AddCommGroup (SA.L.Value W grade target) := SA.L.groups W grade target
variable (factory : SA.SF.Factory W X s)
variable (packet : SA.AS.AdmissionPacket (W := W) (X := X) (s := s))
variable (prior : SourceInventoryExecutionFeed.Inventory (V := SA.L.Value W packet.1) (X := X) (s := s))
variable (present : packet.2.1.1.inventory = some prior)
variable (occurrence : WR.RelationOccurrence prior)

/-- The existing source action retains the original slot, rather than selecting an equal word. -/
def source :
    WR.RelationOccurrence (AS.stockScalar (SA.selected factory packet)
      (SA.nativePacket factory packet).2.2.1) := by
  let block := SourceInventoryBlock.source factory packet prior present
  refine ⟨block.before ++ occurrence.before.map (SA.sourceLiftEvent packet),
    SA.sourceWordAction packet occurrence.word,
    occurrence.after.map (SA.sourceLiftEvent packet) ++ block.after, ?_⟩
  have mapped : prior.trace.map (SA.sourceLiftEvent packet) =
      occurrence.before.map (SA.sourceLiftEvent packet) ++
        PresentedRelationEventAt.relation (SA.sourceWordAction packet occurrence.word) ::
          occurrence.after.map (SA.sourceLiftEvent packet) := by
    rw [occurrence.trace_eq, List.map_append, List.map_cons, SA.source_word_action_relation]
  exact block.trace_eq.trans
    ((congrArg (fun middle => block.before ++ middle ++ block.after) mapped).trans
      (by simp only [List.cons_append, List.append_assoc]))

theorem source_word :
    (source factory packet prior present occurrence).word =
      SA.sourceWordAction packet occurrence.word := rfl

theorem source_before_length :
    (source factory packet prior present occurrence).before.length =
      (SourceInventoryBlock.source factory packet prior present).before.length +
        occurrence.before.length := by
  change (_ ++ occurrence.before.map (SA.sourceLiftEvent packet)).length = _
  simp only [List.length_append, List.length_map]

/-- Appended Feed executions leave this exact pre-existing relation location intact. -/
def born : WR.RelationOccurrence (SA.bornStock factory packet) := by
  let point := source factory packet prior present occurrence
  let frame := SA.selected factory packet
  let base := (SA.nativePacket factory packet).2.2.1
  let tail := RootedAccountedUnfolding.traceBranches
    (SourceInventoryExecutionFeed.executionBranches (AS.stockDecodedEnvironment frame base)
      (SourceInventoryExecutionFeed.requests (AS.stockScalar frame base)))
  refine ⟨point.before, point.word, point.after ++ tail, ?_⟩
  change (SourceInventoryExecutionFeed.written (AS.stockDecodedEnvironment frame base)
    (AS.stockScalar frame base)).trace = _
  rw [SourceInventoryExecutionFeed.written_trace, point.trace_eq]
  simp only [tail, List.cons_append, List.append_assoc]

theorem born_word :
    (born factory packet prior present occurrence).word =
      SA.sourceWordAction packet occurrence.word := rfl

theorem born_before_length :
    (born factory packet prior present occurrence).before.length =
      (SourceInventoryBlock.source factory packet prior present).before.length +
        occurrence.before.length :=
  source_before_length factory packet prior present occurrence

end ActualNativeRelationTransport.SourceRelationOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

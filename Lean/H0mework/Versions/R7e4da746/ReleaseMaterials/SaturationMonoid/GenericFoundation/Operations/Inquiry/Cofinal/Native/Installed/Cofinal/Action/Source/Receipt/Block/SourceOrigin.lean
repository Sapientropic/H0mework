import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block.Position

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
namespace F
export SourceInventoryExecutionFeed (Event Request eventItems requestsFrom readRequestOrigin)
export SourceInventoryExecutionFeed.WordReceipt (sourceRequest)
export SourceInventoryExecutionFeed.ReceiptOccurrence (relationPrefix executionSegmentAt executionSegmentAt_before)
end F
namespace C
export ActualCofinalSourceAction (sourceWordAction sourceLiftEvent source_word_action_relation)
end C
namespace P
export SourceOperationPaidRelations (words stepOccurrence stepOccurrence_word paidCut)
end P

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance originGroups (grade : Nat) : ∀ t, AddCommGroup (S.Value W grade t) := S.groups W grade
variable (factory : S.Factory W X s) (packet : S.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : ExecutionAt packet)

set_option quotPrecheck false in
local notation "events" => ((actedWords packet execution).map PresentedRelationEventAt.relation)
set_option quotPrecheck false in
local notation "sourcePrefix" => (sourceBlock factory packet execution).before
local notation "input" => ActualNativeRelationTransport.SourceInventoryBlock.source factory packet execution.stock execution.installed
local notation "liftEvent" => C.sourceLiftEvent packet
local notation "paidWords" => P.words execution.paid

/-- Exact original Step and support address of an existing request ordinal. -/
structure SourceRequestAt (ordinal : Fin (requests factory packet execution).length) where
  sourceIndex : Fin (paidWords).length
  supportIndex : SupportIndex factory packet execution.stock execution.installed (execution.step sourceIndex)
  request_eq : (requests factory packet execution).get ordinal =
    (atBirth factory packet execution.stock execution.installed (execution.step sourceIndex) supportIndex).request
  prefix_eq : F.relationPrefix (acted factory packet execution.stock execution.installed
      (execution.step sourceIndex)) supportIndex =
    F.requestsFrom 0 (sourcePrefix) ++ (requests factory packet execution).take ordinal.val

open private requestsFrom_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

private theorem sourcePrefix_step (index : Fin (paidWords).length) :
    (acted factory packet execution.stock execution.installed (execution.step index)).before =
      (sourcePrefix) ++ (events).take index.val := by
  change (input).before ++ ((execution.segment.before ++
      (PresentedRelationEventAt.generator execution.request.expression ::
        ((paidWords).take index.val).map PresentedRelationEventAt.relation)).map liftEvent) =
    ((input).before ++ execution.segment.before.map liftEvent ++ [liftEvent (.generator execution.request.expression)]) ++
      ((actedWords packet execution).map PresentedRelationEventAt.relation).take index.val
  simp only [List.map_append, List.map_cons, List.append_assoc, List.singleton_append,
    List.map_take, List.map_map, Function.comp_def, C.source_word_action_relation, actedWords]

/-- Locate the exact pre-write Step, using its generated ordinal even for repeated equal words. -/
def sourceRequestAt (ordinal : Fin (requests factory packet execution).length) :
    SourceRequestAt factory packet execution ordinal := by
  let located := F.readRequestOrigin (sourcePrefix).length (events) ordinal
  let index : Fin (paidWords).length :=
    Fin.cast (by simp only [List.length_map, actedWords]) located.eventIndex
  let sourcePoint := acted factory packet execution.stock execution.installed (execution.step index)
  have sourceWord : sourcePoint.word = C.sourceWordAction packet ((paidWords).get index) := by
    change C.sourceWordAction packet ((execution.step index).word) = _
    exact congrArg (C.sourceWordAction packet)
      (((P.stepOccurrence execution.paid index).transport_word execution.segment).trans
        (P.stepOccurrence_word execution.paid index))
  have actualEvent : (events).get located.eventIndex = .relation sourcePoint.word := by
    rw [sourceWord]
    simp only [List.get_eq_getElem, List.getElem_map, actedWords]
    rfl
  have items : F.eventItems ((events).get located.eventIndex) = Coefficients.sourceItems sourcePoint.word :=
    congrArg F.eventItems actualEvent
  let support : SupportIndex factory packet execution.stock execution.installed (execution.step index) :=
    Fin.cast (congrArg List.length items) located.itemIndex
  have itemEq : (F.eventItems ((events).get located.eventIndex)).get located.itemIndex =
      (Coefficients.sourceItems sourcePoint.word).get support := by
    apply Option.some.inj
    exact (List.getElem?_eq_getElem located.itemIndex.isLt).symm.trans
      ((congrArg (fun list : List (Expr (S.Value W (packet.1+1)) packet.2.2.1.LowVar s × ℤ) =>
        list[support.val]?) items).trans (List.getElem?_eq_getElem support.isLt))
  have preceding_eq : sourcePoint.before = (sourcePrefix) ++ (events).take located.eventIndex.val :=
    sourcePrefix_step factory packet execution index
  have taken : ((events).take located.eventIndex.val).length = located.eventIndex.val :=
    List.length_take.trans (Nat.min_eq_left located.eventIndex.isLt.le)
  have position : sourcePoint.before.length = (sourcePrefix).length + located.eventIndex.val :=
    (congrArg List.length preceding_eq).trans
      (List.length_append.trans (congrArg ((sourcePrefix).length + ·) taken))
  let make := fun (n : Nat) (event : F.Event (V := S.Value W (packet.1+1)) (X := packet.2.2.1.LowVar) (s := s))
      (item : Expr (S.Value W (packet.1+1)) packet.2.2.1.LowVar s × ℤ) =>
    (⟨n,event,item.1,item.2⟩ : F.Request)
  have form : F.sourceRequest sourcePoint =
      make ((sourcePrefix).length + located.eventIndex.val) ((events).get located.eventIndex) := by
    exact congrArg₂ make position actualEvent.symm
  refine ⟨index, support, located.request_eq.trans ?_, ?_⟩
  · change make _ _ _ = F.sourceRequest sourcePoint _
    exact (congrArg (make _ _) itemEq).trans
      (congrFun form ((Coefficients.sourceItems sourcePoint.word).get support)).symm
  · let selectedItems := (Coefficients.sourceItems sourcePoint.word).take support.val
    let listedItems := (F.eventItems ((events).get located.eventIndex)).take located.itemIndex.val
    have sameItems : selectedItems = listedItems := (congrArg (List.take support.val) items).symm
    have mapped := congrArg₂ List.map form sameItems
    change F.requestsFrom 0 sourcePoint.before ++ selectedItems.map (F.sourceRequest sourcePoint) =
      F.requestsFrom 0 (sourcePrefix) ++ (F.requestsFrom (sourcePrefix).length (events)).take ordinal.val
    calc
      _ = F.requestsFrom 0 ((sourcePrefix) ++ (events).take located.eventIndex.val) ++
          listedItems.map (make ((sourcePrefix).length + located.eventIndex.val) ((events).get located.eventIndex)) :=
        congrArg₂ List.append (congrArg (F.requestsFrom 0) preceding_eq) mapped
      _ = _ := by
        rw [requestsFrom_append, Nat.zero_add, located.prefix_eq, List.append_assoc]

end ActualCofinalSourceAction.SourceReceiptOccurrence.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

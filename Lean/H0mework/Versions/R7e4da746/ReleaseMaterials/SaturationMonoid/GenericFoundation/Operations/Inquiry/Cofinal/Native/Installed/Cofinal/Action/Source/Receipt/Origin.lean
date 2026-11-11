import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Partition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed
open SourceOperationEffects SourceOperationExecution
open OrderedTracePartition (locatePart)
open private requestsFrom_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable (start : Nat) (events : List (Event (V := V) (X := X) (s := s)))

/-- The generated request retains both the source event address and its item address. -/
structure RequestOriginAt (ordinal : Fin (requestsFrom start events).length) where
  eventIndex : Fin events.length
  itemIndex : Fin (eventItems (events.get eventIndex)).length
  ordinal_eq : ordinal.val =
    (requestsFrom start (events.take eventIndex.val)).length + itemIndex.val
  request_eq : (requestsFrom start events).get ordinal =
    ⟨start + eventIndex.val, events.get eventIndex,
      ((eventItems (events.get eventIndex)).get itemIndex).1,
      ((eventItems (events.get eventIndex)).get itemIndex).2⟩
  prefix_eq : (requestsFrom start events).take ordinal.val =
    requestsFrom start (events.take eventIndex.val) ++
      ((eventItems (events.get eventIndex)).take itemIndex.val).map
        (fun item => ⟨start + eventIndex.val, events.get eventIndex, item.1, item.2⟩)

def readRequestOrigin (ordinal : Fin (requestsFrom start events).length) :
    RequestOriginAt start events ordinal := by
  let preceding := fun n => requestsFrom start (events.take n)
  let parts := fun (n : Nat) => requestsFrom (start+n) (events[n]?).toList
  have advance (n : Nat) : preceding (n+1) = preceding n ++ parts n := by
    change requestsFrom start (events.take (n+1)) =
      requestsFrom start (events.take n) ++ requestsFrom (start+n) (events[n]?).toList
    by_cases inside : n < events.length
    · have before : (events.take n).length = n :=
        (List.length_take).trans (Nat.min_eq_left inside.le)
      rw [List.take_add_one, requestsFrom_append, before]
    · have outside : events[n]? = none :=
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside)
      rw [List.take_add_one, outside]
      simp only [Option.toList_none, List.append_nil, requestsFrom]
  have complete : preceding events.length = requestsFrom start events :=
    congrArg (requestsFrom start) List.take_length
  let found := locatePart parts preceding rfl advance events.length ordinal.val
    (complete.symm ▸ ordinal.isLt)
  let event := events.get found.block
  let form := fun item : Expr V X s × ℤ => (⟨start + found.block.val,event,item.1,item.2⟩ : Request)
  have selected : parts found.block.val = (eventItems event).map form := by
    change requestsFrom (start+found.block.val) (events[found.block.val]?).toList = _
    rw [List.getElem?_eq_getElem found.block.isLt]
    simp only [Option.toList_some, requestsFrom, List.append_nil, event, form, List.get_eq_getElem]
  let index : Fin (eventItems event).length :=
    Fin.cast ((congrArg List.length selected).trans (List.length_map _)) found.localIndex
  have sourceRead : (preceding events.length)[ordinal.val]? = some ((requestsFrom start events).get ordinal) :=
    (congrArg (fun items : List (Request (V := V) (X := X) (s := s)) =>
      items[ordinal.val]?) complete).trans (List.getElem?_eq_getElem ordinal.isLt)
  have itemRead : (parts found.block.val)[found.localIndex.val]? = some (form ((eventItems event).get index)) := by
    calc
      _ = ((eventItems event).map form)[index.val]? :=
        congrArg (fun items : List (Request (V := V) (X := X) (s := s)) =>
          items[found.localIndex.val]?) selected
      _ = _ := by rw [List.getElem?_map, List.getElem?_eq_getElem index.isLt]; rfl
  refine ⟨found.block, index, found.offset_eq,
    Option.some.inj (sourceRead.symm.trans (found.read.trans itemRead)), ?_⟩
  let trailing := requestsFrom (start+found.block.val+1) (events.drop (found.block.val+1))
  have eventSplit : events = events.take found.block.val ++ event :: events.drop (found.block.val+1) :=
    (List.take_append_drop found.block.val events).symm.trans
      (congrArg (events.take found.block.val ++ ·) (List.drop_eq_getElem_cons found.block.isLt))
  have requestSplit : requestsFrom start events =
      preceding found.block.val ++ ((eventItems event).map form ++ trailing) := by
    refine (congrArg (requestsFrom start) eventSplit).trans ?_
    rw [requestsFrom_append, List.length_take, Nat.min_eq_left found.block.isLt.le]
    rfl
  have selectedBound : index.val ≤ ((eventItems event).map form).length :=
    (List.length_map form).symm ▸ index.isLt.le
  calc
    _ = (preceding found.block.val ++ ((eventItems event).map form ++ trailing)).take ordinal.val :=
      congrArg (fun requests : List (Request (V := V) (X := X) (s := s)) => requests.take ordinal.val) requestSplit
    _ = preceding found.block.val ++ (((eventItems event).map form ++ trailing).take index.val) :=
      (congrArg (fun n => (preceding found.block.val ++ ((eventItems event).map form ++ trailing)).take n)
        found.offset_eq).trans (List.take_length_add_append index.val)
    _ = _ := by
      rw [List.take_append_of_le_length selectedBound, ← List.map_take]

end SourceInventoryExecutionFeed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Origin

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed

open SourceOperationEffects
open private requestsFrom_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Execution

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable (start : Nat) (events : List (Event (V := V) (X := X) (s := s)))
variable (eventIndex : Fin events.length)

private theorem requests_at_split :
    requestsFrom start events =
      requestsFrom start (events.take eventIndex.val) ++
        (eventItems (events.get eventIndex)).map
          (fun item => ⟨start+eventIndex.val, events.get eventIndex, item.1, item.2⟩) ++
        requestsFrom (start+eventIndex.val+1) (events.drop (eventIndex.val+1)) := by
  let before := events.take eventIndex.val
  let after := events.drop (eventIndex.val+1)
  have split : events = before ++ events.get eventIndex :: after :=
    (List.take_append_drop eventIndex.val events).symm.trans
      (congrArg (before ++ ·) (List.drop_eq_getElem_cons eventIndex.isLt))
  have length : before.length = eventIndex.val :=
    List.length_take.trans (Nat.min_eq_left eventIndex.isLt.le)
  calc
    _ = requestsFrom start (before ++ events.get eventIndex :: after) :=
      congrArg (requestsFrom start) split
    _ = _ := by rw [requestsFrom_append, length, requestsFrom, List.append_assoc]

/-- A literal event and its local item determine the original global request ordinal. -/
def requestIndexAt (itemIndex : Fin (eventItems (events.get eventIndex)).length) :
    Fin (requestsFrom start events).length where
  val := (requestsFrom start (events.take eventIndex.val)).length + itemIndex.val
  isLt := by
    have bound := itemIndex.isLt
    rw [requests_at_split start events eventIndex, List.length_append, List.length_append, List.length_map]
    omega

theorem request_index_at_read (itemIndex : Fin (eventItems (events.get eventIndex)).length) :
    (requestsFrom start events).get (requestIndexAt start events eventIndex itemIndex) =
      ⟨start+eventIndex.val, events.get eventIndex,
        ((eventItems (events.get eventIndex)).get itemIndex).1,
        ((eventItems (events.get eventIndex)).get itemIndex).2⟩ := by
  apply Option.some.inj
  refine (List.getElem?_eq_getElem (requestIndexAt start events eventIndex itemIndex).isLt).symm.trans ?_
  let before := requestsFrom start (events.take eventIndex.val)
  change (requestsFrom start events)[before.length+itemIndex.val]? = _
  rw [requests_at_split start events eventIndex, List.append_assoc,
    List.getElem?_append_right (Nat.le_add_right before.length itemIndex.val), Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by rw [List.length_map]; exact itemIndex.isLt),
    List.getElem?_map, List.getElem?_eq_getElem itemIndex.isLt]
  rfl

/-- The existing source origin read returns an address of that exact request. -/
theorem request_index_at_origin (ordinal : Fin (requestsFrom start events).length) :
    let origin := readRequestOrigin start events ordinal
    requestIndexAt start events origin.eventIndex origin.itemIndex = ordinal := by
  exact Fin.ext (readRequestOrigin start events ordinal).ordinal_eq.symm

end SourceInventoryExecutionFeed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

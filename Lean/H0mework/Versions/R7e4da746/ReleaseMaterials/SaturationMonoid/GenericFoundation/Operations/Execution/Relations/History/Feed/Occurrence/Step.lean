import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Transport
import H0mework.Realization.Operations.Execution.Relations.History.Events

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
variable {S : Type u} {V X : S → Type u} [∀ target, AddCommGroup (V target)] {s : S}
variable {environment : Env V X} {raw last : Expr V X s}

/-- The trace's own ordered Step selects its occurrence, including repeated equal words. -/
def stepOccurrence (trace : Trace environment raw last)
    (index : Fin (words trace).length) : WR.RelationOccurrence (exposure trace) := by
  let items := words trace
  refine ⟨PresentedRelationEventAt.generator raw ::
    (items.take index.val).map PresentedRelationEventAt.relation,
    items.get index, (items.drop (index.val + 1)).map PresentedRelationEventAt.relation, ?_⟩
  change PresentedRelationEventAt.generator raw ::
    RootedAccountedUnfolding.traceBranches (events trace) = _
  rw [events_trace]
  have split : items = items.take index.val ++ items.get index :: items.drop (index.val + 1) := by
    change items = items.take index.val ++ items[index.val] :: items.drop (index.val + 1)
    rw [List.getElem_cons_drop index.isLt, List.take_append_drop]
  have mapped := congrArg (List.map PresentedRelationEventAt.relation) split
  simp only [List.map_append, List.map_cons] at mapped
  simpa only [List.cons_append] using congrArg (List.cons (PresentedRelationEventAt.generator raw)) mapped

theorem stepOccurrence_word (trace : Trace environment raw last)
    (index : Fin (words trace).length) :
    (stepOccurrence trace index).word = (words trace).get index := rfl

theorem stepOccurrence_before_length (trace : Trace environment raw last)
    (index : Fin (words trace).length) :
    (stepOccurrence trace index).before.length = 1 + index.val := by
  change ((PresentedRelationEventAt.generator raw ::
    ((words trace).take index.val).map PresentedRelationEventAt.relation).length) = _
  rw [List.length_cons, List.length_map, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt index.isLt)]
  omega

theorem stepOccurrence_positions (trace : Trace environment raw last) :
    StrictMono (fun index : Fin (words trace).length =>
      (stepOccurrence trace index).before.length) := by
  intro first second ordered
  change (stepOccurrence trace first).before.length < (stepOccurrence trace second).before.length
  rw [stepOccurrence_before_length, stepOccurrence_before_length]
  exact Nat.add_lt_add_left (show first.val < second.val from ordered) _

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

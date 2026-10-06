import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Consumer
import H0mework.Realization.Operations.Execution.Relations.History.Append
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem paid_words_next : ∀ word ∈ SourceOperationPaidRelations.words frame.event.state.2,
    word ∈ SourceOperationPaidRelations.words frame.mathNext.event.state.2 := by
  intro word belongs
  change word ∈ SourceOperationPaidRelations.words (RootGeneratedDebtActivationJointSource.mathTarget frame.event).2
  unfold RootGeneratedDebtActivationJointSource.mathTarget
  cases selected : RootGeneratedDebtActivationJointSource.mathAction frame.event with
  | inl settled => exact belongs
  | inr paid =>
      rcases paid with ⟨target, advance⟩
      cases advance with
      | paid step =>
          dsimp only [SourceOperationExecutionDebt.advance]
          rw [SourceOperationPaidRelations.words_append]
          exact List.mem_append_left _ belongs

theorem paid_exposure_next : ∀ atom ∈ (SourceOperationPaidRelations.exposure frame.event.state.2).trace,
    atom ∈ (SourceOperationPaidRelations.exposure frame.mathNext.event.state.2).trace := by
  intro atom belongs
  change atom ∈ PresentedRelationEventAt.generator frame.registered.input.expression ::
    RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events frame.event.state.2) at belongs
  change atom ∈ PresentedRelationEventAt.generator frame.registered.input.expression ::
    RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events frame.mathNext.event.state.2)
  rcases List.mem_cons.mp belongs with same | rest
  · exact List.mem_cons.mpr (.inl same)
  · apply List.mem_cons_of_mem
    rw [SourceOperationPaidRelations.events_trace] at rest ⊢
    obtain ⟨word, present, equal⟩ := List.mem_map.mp rest
    exact List.mem_map.mpr ⟨word,paid_words_next frame word present,equal⟩

theorem inventory_math_next : ∀ atom ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
    atom ∈ (updatedSeed seed (epoch frame.mathNext) (Shared.actualOccurrence frame.mathNext)).trace := by
  intro atom belongs
  change atom ∈ (priorSeed seed frame).root ::
    ((priorSeed seed frame).trace ++ ((SourceOperationPaidRelations.exposure frame.event.state.2).trace ++ [])) at belongs
  change atom ∈ (priorSeed seed frame).root ::
    ((priorSeed seed frame).trace ++ ((SourceOperationPaidRelations.exposure frame.mathNext.event.state.2).trace ++ []))
  rcases List.mem_cons.mp belongs with same | rest
  · exact List.mem_cons.mpr (.inl same)
  · apply List.mem_cons_of_mem
    rcases List.mem_append.mp rest with prior | paid
    · exact List.mem_append_left _ prior
    · apply List.mem_append_right
      rcases List.mem_append.mp paid with previous | impossible
      · exact List.mem_append_left _ (paid_exposure_next frame atom previous)
      · cases impossible


theorem inventory_next : ∀ atom ∈ (materialFace seed frame).rootRead.2.1.trace,
    atom ∈ (materialFace seed (Shared.next frame (programme seed))).rootRead.2.1.trace := by
  unfold Shared.next
  cases frame.action with
  | inl settled => exact birth_inventory_preserved seed frame
  | inr paid => exact inventory_math_next seed frame

def transition : CofinalHistoryTransition.GeneratedTransition
    (history seed (epoch frame) (Shared.actualOccurrence frame))
    (history seed (epoch (Shared.next frame (programme seed)))
      (Shared.actualOccurrence (Shared.next frame (programme seed)))) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame)) (by
      intro word belongs
      change (history seed (epoch (Shared.next frame (programme seed)))
        (Shared.actualOccurrence (Shared.next frame (programme seed)))).completionProjection
          ⟨word.val,SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame) word.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (inventory_next seed frame) belongs)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Exposure
set_option autoImplicit false
noncomputable section
universe u v w r
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon
open CofinalHistorySettlement
variable {A : Type v} {B : Type w} {G : Type u} {Root : Type r}
variable {rootA : RootedAccountedUnfolding A} {rootB : RootedAccountedUnfolding B}
variable {seedA seedB : RootedAccountedUnfolding (PresentedRelationEventAt G)}
variable {nextA nextB : RootedAccountedUnfolding (PresentedRelationEventAt G → RootedAccountedUnfolding (PresentedRelationEventAt G))}
variable (left : RootGeneratedCofinalHistoryAt rootA seedA nextA)
variable (right : RootGeneratedCofinalHistoryAt rootB seedB nextB)
theorem events_left (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    ∀ event, event ∈ left.observedEvents stage → event ∈ (history left right actual).observedEvents stage := by
  intro event present
  simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap, List.mem_range] at present ⊢
  rcases present with ⟨index, bounded, found⟩
  exact ⟨index, bounded, (observations_left left right actual index).1 event found⟩

theorem events_right (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    ∀ event, event ∈ right.observedEvents stage → event ∈ (history left right actual).observedEvents stage := by
  intro event present
  simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap, List.mem_range] at present ⊢
  rcases present with ⟨index, bounded, found⟩
  exact ⟨index, bounded, (observations_right left right actual index).1 event found⟩

theorem support_left (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    (left.generatorSupport stage : Set G) ⊆ (history left right actual).generatorSupport stage := by
  classical
  intro atom present
  change atom ∈ left.generatorSupport stage at present
  change atom ∈ (history left right actual).generatorSupport stage
  rw [RootGeneratedCofinalHistoryAt.generatorSupport, List.mem_toFinset, List.mem_flatMap] at present ⊢
  rcases present with ⟨event, found, supported⟩
  exact ⟨event, events_left left right actual stage event found, supported⟩

theorem support_right (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    (right.generatorSupport stage : Set G) ⊆ (history left right actual).generatorSupport stage := by
  classical
  intro atom present
  change atom ∈ right.generatorSupport stage at present
  change atom ∈ (history left right actual).generatorSupport stage
  rw [RootGeneratedCofinalHistoryAt.generatorSupport, List.mem_toFinset, List.mem_flatMap] at present ⊢
  rcases present with ⟨event, found, supported⟩
  exact ⟨event, events_right left right actual stage event found, supported⟩

theorem generators_left (actual : RootedAccountedUnfolding Root) :
    left.generatorClosure ≤ (history left right actual).generatorClosure := by
  apply iSup_le
  intro stage
  exact (Finsupp.supported_mono (support_left left right actual stage)).trans
    ((history left right actual).generatorStage_le_closure stage)

theorem generators_right (actual : RootedAccountedUnfolding Root) :
    right.generatorClosure ≤ (history left right actual).generatorClosure := by
  apply iSup_le
  intro stage
  exact (Finsupp.supported_mono (support_right left right actual stage)).trans
    ((history left right actual).generatorStage_le_closure stage)

theorem relations_left (actual : RootedAccountedUnfolding Root) :
    left.relationClosure ≤ (history left right actual).relationClosure := by
  apply iSup_le
  intro stage
  apply le_trans (Submodule.span_mono (fun word present => events_left left right actual stage _ present))
  exact (history left right actual).relationStage_le_closure stage

theorem relations_right (actual : RootedAccountedUnfolding Root) :
    right.relationClosure ≤ (history left right actual).relationClosure := by
  apply iSup_le
  intro stage
  apply le_trans (Submodule.span_mono (fun word present => events_right left right actual stage _ present))
  exact (history left right actual).relationStage_le_closure stage
namespace T
export CofinalHistoryTransition (GeneratedTransition RelationCompatible freeTransition)
end T
def leftTransition (actual : RootedAccountedUnfolding Root) :
    T.GeneratedTransition left (history left right actual) :=
  CofinalHistoryTransition.GeneratedTransition.create left (history left right actual) (generators_left left right actual) (by
    intro direction relation
    change (history left right actual).completionProjection
      (⟨direction.val, generators_left left right actual direction.property⟩) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact relations_left left right actual relation)
def rightTransition (actual : RootedAccountedUnfolding Root) :
    T.GeneratedTransition right (history left right actual) :=
  CofinalHistoryTransition.GeneratedTransition.create right (history left right actual) (generators_right left right actual) (by
    intro direction relation
    change (history left right actual).completionProjection
      (⟨direction.val, generators_right left right actual direction.property⟩) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact relations_right left right actual relation)
theorem left_fibre_zero (actual : RootedAccountedUnfolding Root) (word : left.generatorClosure) :
    CofinalHistoryTransition.GeneratedTransition.completionMap left (history left right actual)
      (leftTransition left right actual) (left.completionProjection word) = 0 ↔
        word.val ∈ (history left right actual).relationClosure := by
  have generated := CofinalHistoryTransition.GeneratedTransition.completionMap_projection left (history left right actual)
    (leftTransition left right actual) word
  have read : CofinalHistoryTransition.GeneratedTransition.completionMap left (history left right actual)
      (leftTransition left right actual) (left.completionProjection word) =
        (history left right actual).completionProjection ⟨word.val, generators_left left right actual word.property⟩ := generated
  exact (iff_of_eq (congrArg (fun value : (history left right actual).CompletionCarrier => value = 0) read)).trans
    (Submodule.Quotient.mk_eq_zero (history left right actual).relationInGeneratorClosure)

theorem right_fibre_zero (actual : RootedAccountedUnfolding Root) (word : right.generatorClosure) :
    CofinalHistoryTransition.GeneratedTransition.completionMap right (history left right actual)
      (rightTransition left right actual) (right.completionProjection word) = 0 ↔
        word.val ∈ (history left right actual).relationClosure := by
  have generated := CofinalHistoryTransition.GeneratedTransition.completionMap_projection right (history left right actual)
    (rightTransition left right actual) word
  have read : CofinalHistoryTransition.GeneratedTransition.completionMap right (history left right actual)
      (rightTransition left right actual) (right.completionProjection word) =
        (history left right actual).completionProjection ⟨word.val, generators_right left right actual word.property⟩ := generated
  exact (iff_of_eq (congrArg (fun value : (history left right actual).CompletionCarrier => value = 0) read)).trans
    (Submodule.Quotient.mk_eq_zero (history left right actual).relationInGeneratorClosure)
theorem transition_fibre_zero (generated : CofinalHistoryTransition.GeneratedTransition left right)
    (word : left.generatorClosure) :
    CofinalHistoryTransition.GeneratedTransition.completionMap left right generated (left.completionProjection word) = 0 ↔
      word.val ∈ right.relationClosure := by
  have point := CofinalHistoryTransition.GeneratedTransition.completionMap_projection left right generated word
  have read : CofinalHistoryTransition.GeneratedTransition.completionMap left right generated (left.completionProjection word) =
      right.completionProjection ⟨word.val, generated.generatorCompatible word.property⟩ := point
  exact (iff_of_eq (congrArg (fun value : right.CompletionCarrier => value = 0) read)).trans
    (Submodule.Quotient.mk_eq_zero right.relationInGeneratorClosure)
end SourceHistoryCommon
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

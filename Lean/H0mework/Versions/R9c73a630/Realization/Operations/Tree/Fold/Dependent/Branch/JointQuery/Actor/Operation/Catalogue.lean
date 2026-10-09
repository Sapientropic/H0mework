import H0mework.Versions.R9c73a630.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Source

set_option autoImplicit false
noncomputable section
universe u w
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open RootLawDependentJointStateController RootLawDependentJointTransition
namespace Catalogue
variable {G : Type u} {Root : Type w}
variable {origin : RootedAccountedUnfolding Root}
variable {seed : RootedAccountedUnfolding (PresentedRelationEventAt G)}
variable {continuation : RootedAccountedUnfolding (PresentedRelationEventAt G → RootedAccountedUnfolding (PresentedRelationEventAt G))}
def word : PresentedRelationEventAt G → G →₀ ℤ
  | .generator g => Finsupp.single g 1
  | .relation value => value
private theorem word_supported (event : PresentedRelationEventAt G) : (word event).support ⊆ event.support := by
  classical
  cases event <;> simp [word,PresentedRelationEventAt.support]
theorem seed_member (history : RootGeneratedCofinalHistoryAt origin seed continuation)
    (event : PresentedRelationEventAt G) (present : event ∈ history.seed.trace) : word event ∈ history.generatorClosure := by
  classical
  apply history.generatorStage_le_closure 0
  change word event ∈ Finsupp.supported ℤ ℤ (history.generatorSupport 0 : Set G)
  rw [Finsupp.mem_supported]
  intro generator belongs
  change generator ∈ history.generatorSupport 0
  rw [RootGeneratedCofinalHistoryAt.generatorSupport,List.mem_toFinset,List.mem_flatMap]
  refine ⟨event,?_,?_⟩
  · simpa [RootGeneratedCofinalHistoryAt.observedEvents] using present
  · exact Finset.mem_toList.mpr (word_supported event belongs)
def value (history : RootGeneratedCofinalHistoryAt origin seed continuation)
    (event : {event : PresentedRelationEventAt G // event ∈ history.seed.trace}) : history.CompletionCarrier :=
  history.completionProjection ⟨word event.val,seed_member history event.val event.property⟩
def points (history : RootGeneratedCofinalHistoryAt origin seed continuation) :=
  history.seed.trace.attach.map (value history)
theorem relation_member (history : RootGeneratedCofinalHistoryAt origin seed continuation)
    (relation : G →₀ ℤ) (present : PresentedRelationEventAt.relation relation ∈ history.seed.trace) :
    relation ∈ history.relationClosure := by
  apply history.relationStage_le_closure 0
  apply Submodule.subset_span
  simpa [RootGeneratedCofinalHistoryAt.observedEvents] using present
theorem relation_value (history : RootGeneratedCofinalHistoryAt origin seed continuation)
    (relation : G →₀ ℤ) (present : PresentedRelationEventAt.relation relation ∈ history.seed.trace) :
    value history ⟨.relation relation,present⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact relation_member history relation present
end Catalogue
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

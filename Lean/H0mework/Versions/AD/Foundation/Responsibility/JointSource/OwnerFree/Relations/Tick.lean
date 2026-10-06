import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Consumer
import H0mework.Realization.Operations.Execution.Relations.History.Append
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Relations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (runtime : Runtime old origin reader)
theorem tick_words : ∀ word ∈ SourceOperationPaidRelations.words (runtimeCurrent old origin reader runtime).2,
    word ∈ SourceOperationPaidRelations.words (runtimeCurrent old origin reader runtime.tick.next).2 := by
  intro word belongs
  rw [tick_math]
  unfold nextState targetOf
  cases selected : action old origin reader (runtimeCurrent old origin reader runtime) with
  | inl settled => exact belongs
  | inr paid =>
      rcases paid with ⟨target, advance⟩
      cases advance with
      | paid step =>
          dsimp only [SourceOperationExecutionDebt.advance]
          rw [SourceOperationPaidRelations.words_append]
          exact List.mem_append_left _ belongs
theorem tick_paid_exposure : ∀ event ∈ (exposure old origin reader runtime).trace,
    event ∈ (exposure old origin reader runtime.tick.next).trace := by
  intro event belongs
  change event ∈ CofinalHistorySettlement.PresentedRelationEventAt.generator
    (raw old origin reader).expression :: RootedAccountedUnfolding.traceBranches
      (SourceOperationPaidRelations.events (runtimeCurrent old origin reader runtime).2) at belongs
  change event ∈ CofinalHistorySettlement.PresentedRelationEventAt.generator
    (raw old origin reader).expression :: RootedAccountedUnfolding.traceBranches
      (SourceOperationPaidRelations.events (runtimeCurrent old origin reader runtime.tick.next).2)
  rcases List.mem_cons.mp belongs with same | rest
  · exact List.mem_cons.mpr (.inl same)
  · apply List.mem_cons_of_mem
    have prevRead := SourceOperationPaidRelations.events_trace (runtimeCurrent old origin reader runtime).2
    have nextRead := SourceOperationPaidRelations.events_trace (runtimeCurrent old origin reader runtime.tick.next).2
    rw [prevRead] at rest
    rw [nextRead]
    obtain ⟨word,member,equal⟩ := List.mem_map.mp rest
    exact List.mem_map.mpr ⟨word,tick_words old origin reader runtime word member,equal⟩
end RootGeneratedDebtActivationJointSource.OwnerFree.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

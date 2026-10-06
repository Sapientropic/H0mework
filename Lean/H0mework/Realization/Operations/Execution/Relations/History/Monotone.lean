import H0mework.Realization.Operations.Execution.Relations.History.Laws
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before middle after : Expr Value Var sort}
open CofinalHistorySettlement
variable {Root : Type u}
variable (rootOccurrence : RootedAccountedUnfolding Root)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr Value Var sort)))
abbrev prefixHistory := RootGeneratedCofinalHistoryAt.generate (rootOccurrence:=rootOccurrence)
  (seedOccurrence:=seed) (continuationOccurrence:=continuation (Value:=Value) (Var:=Var) (sort:=sort))
theorem observation_seed (stage : Nat) :
    ∀ event ∈ (prefixHistory rootOccurrence seed).observation stage |>.trace, event ∈ seed.trace := by
  induction stage with
  | zero => exact fun _ belongs => belongs
  | succ stage previous => exact advance_preserves (fun event => event ∈ seed.trace) _ previous

theorem events_seed (stage : Nat) : ∀ event ∈ (prefixHistory rootOccurrence seed).observedEvents stage,
    event ∈ seed.trace := by
  intro event belongs
  rw [RootGeneratedCofinalHistoryAt.observedEvents,List.mem_flatMap] at belongs
  obtain ⟨index,_,member⟩ := belongs
  exact observation_seed rootOccurrence seed index event member

variable {RootNext : Type u}
variable (nextRoot : RootedAccountedUnfolding RootNext)
variable (nextSeed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr Value Var sort)))
theorem events_next (preservation : ∀ event ∈ seed.trace, event ∈ nextSeed.trace) (stage : Nat) : ∀ event ∈ (prefixHistory rootOccurrence seed).observedEvents stage,
    event ∈ (prefixHistory nextRoot nextSeed).observedEvents 0 := by
  intro event belongs
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
    List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
  exact preservation event (events_seed rootOccurrence seed stage event belongs)

theorem relations_next (preservation : ∀ event ∈ seed.trace, event ∈ nextSeed.trace) : (prefixHistory rootOccurrence seed).relationClosure ≤
    (prefixHistory nextRoot nextSeed).relationClosure := by
  apply iSup_le
  intro stage
  apply le_trans (Submodule.span_mono (fun word belongs =>
    events_next rootOccurrence seed nextRoot nextSeed preservation stage _ belongs))
  exact (prefixHistory nextRoot nextSeed).relationStage_le_closure 0

theorem generators_next (preservation : ∀ event ∈ seed.trace, event ∈ nextSeed.trace) : (prefixHistory rootOccurrence seed).generatorClosure ≤
    (prefixHistory nextRoot nextSeed).generatorClosure := by
  classical
  apply iSup_le
  intro stage
  apply le_trans (Finsupp.supported_mono ?_)
    ((prefixHistory nextRoot nextSeed).generatorStage_le_closure 0)
  intro atom belongs
  change atom ∈ (prefixHistory rootOccurrence seed).generatorSupport stage at belongs
  change atom ∈ (prefixHistory nextRoot nextSeed).generatorSupport 0
  rw [RootGeneratedCofinalHistoryAt.generatorSupport,List.mem_toFinset,List.mem_flatMap] at belongs ⊢
  obtain ⟨event,eventMem,atomMem⟩ := belongs
  exact ⟨event,events_next rootOccurrence seed nextRoot nextSeed preservation stage _ eventMem,atomMem⟩
end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

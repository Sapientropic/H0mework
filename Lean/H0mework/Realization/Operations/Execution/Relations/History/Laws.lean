import H0mework.Realization.Operations.Execution.Relations.History.Source
/-! The actual Step relations generate closure soundness and the complete paid boundary. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationPaidRelations
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalHistorySettlement
variable {Sorts : Type u} {Value Var : Sorts → Type u}
variable [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {environment : Env Value Var} {before after : Expr Value Var sort}
variable {Root : Type u}
variable (rootOccurrence : RootedAccountedUnfolding Root)
theorem word_read (trace : Trace environment before after) (word : Expr Value Var sort →₀ ℤ) :
    (face rootOccurrence trace).freeEvaluation word = evaluation (R:=ℤ) environment word := by
  classical
  induction word using Finsupp.induction with
  | zero => exact (face rootOccurrence trace).freeEvaluation.map_zero
  | @single_add expression integer rest absent nonzero previous =>
      calc
        (face rootOccurrence trace).freeEvaluation (Finsupp.single expression integer + rest) =
            (face rootOccurrence trace).freeEvaluation (Finsupp.single expression integer) +
              (face rootOccurrence trace).freeEvaluation rest :=
          (face rootOccurrence trace).freeEvaluation.map_add _ _
        _ = integer • expression.eval environment + evaluation (R:=ℤ) environment rest :=
          congrArg₂ (· + ·)
            (CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.freeEvaluation_single
              (face rootOccurrence trace) expression integer) previous
        _ = evaluation (R:=ℤ) environment (Finsupp.single expression integer + rest) := by
          rw [map_add, Finsupp.linearCombination_single]
theorem advance_preserves {A : Type u} (property : A → Prop)
    (occurrence : RootedAccountedUnfolding A)
    (holds : ∀ atom ∈ occurrence.trace, property atom) :
    ∀ atom ∈ (occurrence.advance RootedAccountedUnfolding.zero).trace, property atom := by
  induction occurrence using RootedAccountedUnfolding.rec
    (motive_2 := fun branches =>
      (∀ atom ∈ RootedAccountedUnfolding.traceBranches branches, property atom) →
        ∀ atom ∈ RootedAccountedUnfolding.traceBranches
          (RootedAccountedUnfolding.advanceBranches RootedAccountedUnfolding.zero branches), property atom) with
  | occur origin branches branchPrevious =>
      cases branches with
      | nil =>
          intro atom belongs
          change atom ∈ [origin,origin] at belongs
          have same := holds origin (by change origin ∈ [origin]; exact List.mem_cons_self)
          rcases List.mem_cons.mp belongs with equal | rest
          · exact equal ▸ same
          · rcases List.mem_cons.mp rest with equal | impossible
            · exact equal ▸ same
            · cases impossible
      | cons head tail =>
          intro atom belongs
          change atom ∈ origin :: RootedAccountedUnfolding.traceBranches
            (RootedAccountedUnfolding.advanceBranches RootedAccountedUnfolding.zero (.cons head tail)) at belongs
          rcases List.mem_cons.mp belongs with equal | rest
          · exact equal ▸ holds origin List.mem_cons_self
          · exact branchPrevious (fun item member => holds item (List.mem_cons_of_mem origin member)) atom rest
  | nil =>
      rename_i branchHolds atom impossible
      cases impossible
  | cons head tail headPrevious tailPrevious =>
      rename_i branchHolds atom belongs
      change atom ∈ (head.advance RootedAccountedUnfolding.zero).trace ++
        RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.advanceBranches RootedAccountedUnfolding.zero tail) at belongs
      rcases List.mem_append.mp belongs with left | right
      · exact headPrevious (fun item member => branchHolds item (List.mem_append_left _ member)) atom left
      · exact tailPrevious (fun item member => branchHolds item (List.mem_append_right _ member)) atom right

def soundEvent (environment : Env Value Var) : PresentedRelationEventAt (Expr Value Var sort) → Prop
  | .generator _ => True
  | .relation word => evaluation (R:=ℤ) environment word = 0

theorem observation_sound (trace : Trace environment before after) (stage : Nat) :
    ∀ event ∈ (history rootOccurrence trace).observation stage |>.trace, soundEvent environment event := by
  induction stage with
  | zero =>
      intro event belongs
      cases event with
      | generator _ => exact True.intro
      | relation word => exact exposure_sound trace word belongs
  | succ stage previous =>
      exact advance_preserves (soundEvent environment) _ previous

theorem relations_sound (trace : Trace environment before after) :
    (face rootOccurrence trace).RelationsSound := by
  apply iSup_le
  intro stage
  apply Submodule.span_le.mpr
  intro word belongs
  change (face rootOccurrence trace).freeEvaluation word = 0
  apply (word_read rootOccurrence trace word).trans
  change PresentedRelationEventAt.relation word ∈ (history rootOccurrence trace).observedEvents stage at belongs
  rw [RootGeneratedCofinalHistoryAt.observedEvents, List.mem_flatMap] at belongs
  obtain ⟨index,_,eventMem⟩ := belongs
  exact observation_sound rootOccurrence trace index _ eventMem

theorem step_in_inventory (trace : Trace environment before after) (word : Expr Value Var sort →₀ ℤ)
    (belongs : word ∈ words trace) : word ∈ (history rootOccurrence trace).relationClosure := by
  apply (history rootOccurrence trace).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation word ∈ (history rootOccurrence trace).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ, List.range_zero, List.nil_append, List.flatMap_singleton, RootGeneratedCofinalHistoryAt.observation_zero]
  change PresentedRelationEventAt.relation word ∈ (exposure trace).trace
  apply List.mem_cons_of_mem
  exact Eq.mpr (congrArg (fun events => PresentedRelationEventAt.relation word ∈ events) (events_trace trace))
    (List.mem_map.mpr ⟨word,belongs,rfl⟩)

theorem boundary_in_inventory (trace : Trace environment before after) :
    relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ)) ∈
      (history rootOccurrence trace).relationClosure := by
  rw [← paid_boundary]
  have sum_mem : ∀ items : List (Expr Value Var sort →₀ ℤ),
      (∀ word ∈ items, word ∈ (history rootOccurrence trace).relationClosure) →
      items.sum ∈ (history rootOccurrence trace).relationClosure := by
    intro items
    induction items with
    | nil => intro _; exact Submodule.zero_mem _
    | cons head tail previous =>
        intro all
        exact Submodule.add_mem _ (all head List.mem_cons_self)
          (previous (fun word belongs => all word (List.mem_cons_of_mem head belongs)))
  exact sum_mem (words trace) (fun word belongs => step_in_inventory rootOccurrence trace word belongs)

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

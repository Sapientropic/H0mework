import H0mework.Realization.Operations.Execution.Relations
import H0mework.Realization.Completion.HistorySettlement
/-! Every actual paid Step contributes its endpoint relation in original trace order. -/

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
def events : {before after : Expr Value Var sort} → Trace environment before after →
    AccountedBranches (PresentedRelationEventAt (Expr Value Var sort))
  | _, _, .nil _ => .nil
  | before, _, .cons (middle:=next) step tail =>
      .cons (.zero (.relation (relation (R:=ℤ) environment (.inl ⟨before,next,step.toDerivation⟩)))) (events tail)
def exposure (trace : Trace environment before after) : RootedAccountedUnfolding
    (PresentedRelationEventAt (Expr Value Var sort)) := .occur (.generator before) (events trace)
theorem events_sound (trace : Trace environment before after) :
    ∀ word, PresentedRelationEventAt.relation word ∈ RootedAccountedUnfolding.traceBranches (events trace) →
      evaluation (R:=ℤ) environment word = 0 := by
  induction trace with
  | nil expression => intro word absent; cases absent
  | @cons before middle after step tail previous =>
      intro word belongs
      change PresentedRelationEventAt.relation word ∈
        PresentedRelationEventAt.relation (relation (R:=ℤ) environment (.inl ⟨before,middle,step.toDerivation⟩)) ::
          RootedAccountedUnfolding.traceBranches (events tail) at belongs
      rcases List.mem_cons.mp belongs with same | rest
      · have sameWord := PresentedRelationEventAt.relation.inj same
        exact sameWord ▸ relation_sound environment (.inl ⟨before,middle,step.toDerivation⟩)
      · exact previous word rest

theorem exposure_sound (trace : Trace environment before after) (word : Expr Value Var sort →₀ ℤ)
    (belongs : PresentedRelationEventAt.relation word ∈ (exposure trace).trace) :
    evaluation (R:=ℤ) environment word = 0 := by
  change PresentedRelationEventAt.relation word ∈ PresentedRelationEventAt.generator before ::
    RootedAccountedUnfolding.traceBranches (events trace) at belongs
  rcases List.mem_cons.mp belongs with impossible | rest
  · cases impossible
  · exact events_sound trace word rest
def words : {before after : Expr Value Var sort} → Trace environment before after →
    List (Expr Value Var sort →₀ ℤ)
  | _, _, .nil _ => []
  | before, _, .cons (middle:=next) step tail =>
      relation (R:=ℤ) environment (.inl ⟨before,next,step.toDerivation⟩) :: words tail

theorem events_trace (trace : Trace environment before after) :
    RootedAccountedUnfolding.traceBranches (events trace) =
      (words trace).map PresentedRelationEventAt.relation := by
  induction trace with
  | nil => rfl
  | cons step tail previous => exact congrArg (List.cons _) previous

theorem complete_steps (trace : Trace environment before after) : (words trace).length = trace.length := by
  induction trace with
  | nil => rfl
  | cons step tail previous =>
      change (words tail).length + 1 = 1 + tail.length
      exact (congrArg (fun count => count+1) previous).trans (Nat.add_comm _ _)

theorem paid_boundary (trace : Trace environment before after) :
    (words trace).sum = relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ)) := by
  induction trace with
  | nil => exact (map_zero _).symm
  | cons step tail previous =>
      simp only [words, List.sum_cons, Trace.relationWords, map_add, Step.relation_boundary]
      exact congrArg₂ (· + ·) rfl previous

end SourceOperationPaidRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

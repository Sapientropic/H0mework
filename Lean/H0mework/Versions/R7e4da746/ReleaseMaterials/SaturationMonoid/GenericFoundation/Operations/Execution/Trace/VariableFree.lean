import H0mework.Realization.Operations.Execution.Relations.History.Events
import H0mework.Realization.Operations.InventoryLift

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.PaidSyntax
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace P
export SourceOperationPaidRelations (words)
end P

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

def NoVariable {target : S} (term : Expr V X target) : Prop := by
  induction term with
  | var => exact False
  | const => exact True
  | add _ _ first second => exact first ∧ second
  | linear _ _ previous => exact previous
  | bilinear _ _ _ first second => exact first ∧ second

theorem eval_eq (term : Expr V X s) (closed : NoVariable term) (left right : Env V X) :
    term.eval left = term.eval right := by
  induction term with
  | var => exact False.elim closed
  | const => rfl
  | add _ _ first second => exact congrArg₂ (· + ·) (first closed.1) (second closed.2)
  | linear operation _ previous => exact congrArg operation (previous closed)
  | bilinear operation _ _ first second =>
    exact congrArg₂ (fun x y => operation x y) (first closed.1) (second closed.2)

theorem lift_noVariable (term : Expr V X s) (closed : NoVariable term) :
    NoVariable (liftExpr term) := by
  induction term with
  | var => exact closed
  | const => exact closed
  | add _ _ first second => exact ⟨first closed.1, second closed.2⟩
  | linear _ _ previous => exact previous closed
  | bilinear _ _ _ first second => exact ⟨first closed.1, second closed.2⟩

theorem step_noVariable {environment : Env V X} {before after : Expr V X s}
    (step : Step environment before after) (closed : NoVariable before) : NoVariable after := by
  induction step with
  | bind => exact False.elim closed
  | addConst => exact True.intro
  | linearConst => exact True.intro
  | bilinearConst => exact True.intro
  | addLeft _ previous => exact ⟨previous closed.1, closed.2⟩
  | addRight _ previous => exact ⟨closed.1, previous closed.2⟩
  | linear _ _ previous => exact previous closed
  | bilinearLeft _ _ previous => exact ⟨previous closed.1, closed.2⟩
  | bilinearRight _ _ previous => exact ⟨closed.1, previous closed.2⟩

def WordNoVariable (word : Formal ℤ V X s) : Prop :=
  ∀ term ∈ word.support, NoVariable term

private theorem difference_noVariable {left right : Expr V X s}
    (leftClosed : NoVariable left) (rightClosed : NoVariable right) :
    WordNoVariable (Finsupp.single left 1 - Finsupp.single right 1) := by
  classical
  intro term member
  by_cases leftHit : term = left
  · subst term
    exact leftClosed
  by_cases rightHit : term = right
  · subst term
    exact rightClosed
  have nonzero := Finsupp.mem_support_iff.mp member
  exact (nonzero (by
    simp only [Finsupp.sub_apply, Finsupp.single_eq_of_ne leftHit, Finsupp.single_eq_of_ne rightHit, sub_zero])).elim

/-- Each original contextual Step contributes exactly its own two endpoints. -/
theorem trace_words_noVariable {environment : Env V X} {before after : Expr V X s}
    (trace : Trace environment before after) :
    NoVariable before → ∀ word ∈ P.words trace, WordNoVariable word := by
  induction trace with
  | nil => intro _ _ member; cases member
  | @cons before middle after paid tail previous =>
    intro closed word member
    have middleClosed := step_noVariable paid closed
    change word ∈ (Finsupp.single before 1 - Finsupp.single middle 1) :: P.words tail at member
    rcases List.mem_cons.mp member with selected | rest
    · subst word
      exact difference_noVariable closed middleClosed
    · exact previous middleClosed word rest

theorem lift_word_noVariable (word : Formal ℤ V X s) (closed : WordNoVariable word) :
    WordNoVariable (liftMap (R := ℤ) word) := by
  classical
  intro term member
  change term ∈ (Finsupp.mapDomain liftExpr word).support at member
  obtain ⟨source, fromSource, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support member)
  exact lift_noVariable source (closed source fromSource)

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.PaidSyntax
end

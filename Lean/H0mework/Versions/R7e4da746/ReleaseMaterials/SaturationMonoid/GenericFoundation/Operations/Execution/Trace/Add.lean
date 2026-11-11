import H0mework.Realization.Operations.Execution.Trace

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace SaturationMonoid.SourceOperationExecution.Trace

open SourceOperationEffects

universe u v w
variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ sort, AddCommGroup (Value sort)]
variable {environment : Env Value Var} {sort : Sorts}

/-- The indices retain every original step, including the chosen left/right order. -/
inductive AddInterleaving (environment : Env Value Var) {sort : Sorts} :
    {left right : Expr Value Var sort} → {total leftValue rightValue : Value sort} →
    Trace environment (.add left right) (.const total) →
    Trace environment left (.const leftValue) →
    Trace environment right (.const rightValue) → Type (max u v w)
  | last (leftValue rightValue : Value sort) :
      AddInterleaving environment (.single (.addConst leftValue rightValue))
        (.nil (.const leftValue)) (.nil (.const rightValue))
  | left {left middle right : Expr Value Var sort} {total leftValue rightValue : Value sort}
      (step : Step environment left middle)
      {actual : Trace environment (.add middle right) (.const total)}
      {leftTrace : Trace environment middle (.const leftValue)}
      {rightTrace : Trace environment right (.const rightValue)}
      (tail : AddInterleaving environment actual leftTrace rightTrace) :
      AddInterleaving environment (.cons (.addLeft step) actual) (.cons step leftTrace) rightTrace
  | right {left right middle : Expr Value Var sort} {total leftValue rightValue : Value sort}
      (step : Step environment right middle)
      {actual : Trace environment (.add left middle) (.const total)}
      {leftTrace : Trace environment left (.const leftValue)}
      {rightTrace : Trace environment middle (.const rightValue)}
      (tail : AddInterleaving environment actual leftTrace rightTrace) :
      AddInterleaving environment (.cons (.addRight step) actual) leftTrace (.cons step rightTrace)

namespace AddInterleaving
variable {left right : Expr Value Var sort} {total leftValue rightValue : Value sort}
variable {actual : Trace environment (.add left right) (.const total)}
variable {leftTrace : Trace environment left (.const leftValue)}
variable {rightTrace : Trace environment right (.const rightValue)}

theorem total_eq (interleaving : AddInterleaving environment actual leftTrace rightTrace) :
    total = leftValue + rightValue := by
  induction interleaving with
  | last => rfl
  | left _ _ prior => exact prior
  | right _ _ prior => exact prior

theorem length_eq (interleaving : AddInterleaving environment actual leftTrace rightTrace) :
    actual.length = leftTrace.length + rightTrace.length + 1 := by
  induction interleaving with
  | last => rfl
  | left _ _ prior => simp only [Trace.length] at *; omega
  | right _ _ prior => simp only [Trace.length] at *; omega

def leftPositions
    {left right : Expr Value Var sort} {total leftValue rightValue : Value sort}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace) : List Nat :=
  match interleaving with
  | .last _ _ => []
  | .left _ tail => 0 :: (leftPositions tail).map Nat.succ
  | .right _ tail => (leftPositions tail).map Nat.succ

def rightPositions
    {left right : Expr Value Var sort} {total leftValue rightValue : Value sort}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace) : List Nat :=
  match interleaving with
  | .last _ _ => []
  | .left _ tail => (rightPositions tail).map Nat.succ
  | .right _ tail => 0 :: (rightPositions tail).map Nat.succ

theorem leftPositions_length (interleaving : AddInterleaving environment actual leftTrace rightTrace) :
    interleaving.leftPositions.length = leftTrace.length := by
  induction interleaving with
  | last => rfl
  | left _ _ prior =>
      simp only [leftPositions, List.length_cons, List.length_map, Trace.length]
      omega
  | right _ _ prior => simpa only [leftPositions, List.length_map] using prior

theorem rightPositions_length (interleaving : AddInterleaving environment actual leftTrace rightTrace) :
    interleaving.rightPositions.length = rightTrace.length := by
  induction interleaving with
  | last => rfl
  | left _ _ prior => simpa only [rightPositions, List.length_map] using prior
  | right _ _ prior =>
      simp only [rightPositions, List.length_cons, List.length_map, Trace.length]
      omega
end AddInterleaving

structure AddSplit {left right : Expr Value Var sort} {total : Value sort}
    (actual : Trace environment (.add left right) (.const total)) : Type (max u v w) where
  leftValue : Value sort
  rightValue : Value sort
  leftTrace : Trace environment left (.const leftValue)
  rightTrace : Trace environment right (.const rightValue)
  interleaving : AddInterleaving environment actual leftTrace rightTrace

/-- Split the given paid history itself; no new execution is selected. -/
def splitAdd {left right : Expr Value Var sort} {total : Value sort}
    (actual : Trace environment (.add left right) (.const total)) : AddSplit actual :=
  match actual with
  | .cons (.addConst leftValue rightValue) (.nil _) =>
      ⟨leftValue, rightValue, .nil _, .nil _, .last _ _⟩
  | .cons (.addConst _ _) (.cons impossible _) => nomatch impossible
  | .cons (.addLeft step) tail =>
      let result := splitAdd tail
      ⟨result.leftValue, result.rightValue, .cons step result.leftTrace,
        result.rightTrace, .left step result.interleaving⟩
  | .cons (.addRight step) tail =>
      let result := splitAdd tail
      ⟨result.leftValue, result.rightValue, result.leftTrace,
        .cons step result.rightTrace, .right step result.interleaving⟩

namespace AddSplit
variable {left right : Expr Value Var sort} {total : Value sort}
variable {actual : Trace environment (.add left right) (.const total)}

theorem total_eq (result : AddSplit actual) : total = result.leftValue + result.rightValue :=
  result.interleaving.total_eq

theorem length_eq (result : AddSplit actual) :
    actual.length = result.leftTrace.length + result.rightTrace.length + 1 :=
  result.interleaving.length_eq
end AddSplit

end SaturationMonoid.SourceOperationExecution.Trace

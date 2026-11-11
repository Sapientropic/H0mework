import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace SaturationMonoid.SourceOperationExecution.Trace
open SourceOperationEffects
universe u v w
variable {S : Type u} {V : S → Type v} {X : S → Type w}
  [∀ s, AddCommGroup (V s)] {environment : Env V X} {s t r : S}

/-- The given order of the two child histories and the final payment are retained. -/
inductive BilinearInterleaving (operation : V s →+ V t →+ V r) :
    {left : Expr V X s} → {right : Expr V X t} →
    {total : V r} → {leftValue : V s} → {rightValue : V t} →
    Trace environment (.bilinear operation left right) (.const total) →
    Trace environment left (.const leftValue) →
    Trace environment right (.const rightValue) → Type (max u v w)
  | last (leftValue : V s) (rightValue : V t) :
      BilinearInterleaving operation (.single (.bilinearConst operation leftValue rightValue))
        (.nil (.const leftValue)) (.nil (.const rightValue))
  | left {left middle : Expr V X s} {right : Expr V X t}
      {total : V r} {leftValue : V s} {rightValue : V t}
      (step : Step environment left middle)
      {actual : Trace environment (.bilinear operation middle right) (.const total)}
      {leftTrace : Trace environment middle (.const leftValue)}
      {rightTrace : Trace environment right (.const rightValue)}
      (tail : BilinearInterleaving operation actual leftTrace rightTrace) :
      BilinearInterleaving operation (.cons (.bilinearLeft operation step) actual)
        (.cons step leftTrace) rightTrace
  | right {left : Expr V X s} {right middle : Expr V X t}
      {total : V r} {leftValue : V s} {rightValue : V t}
      (step : Step environment right middle)
      {actual : Trace environment (.bilinear operation left middle) (.const total)}
      {leftTrace : Trace environment left (.const leftValue)}
      {rightTrace : Trace environment middle (.const rightValue)}
      (tail : BilinearInterleaving operation actual leftTrace rightTrace) :
      BilinearInterleaving operation (.cons (.bilinearRight operation step) actual)
        leftTrace (.cons step rightTrace)

namespace BilinearInterleaving
variable {operation : V s →+ V t →+ V r}
variable {left : Expr V X s} {right : Expr V X t}
variable {total : V r} {leftValue : V s} {rightValue : V t}
variable {actual : Trace environment (.bilinear operation left right) (.const total)}
variable {leftTrace : Trace environment left (.const leftValue)}
variable {rightTrace : Trace environment right (.const rightValue)}

theorem total_eq (cut : BilinearInterleaving operation actual leftTrace rightTrace) :
    total = operation leftValue rightValue := by
  induction cut with
  | last => rfl
  | left _ _ prior => exact prior
  | right _ _ prior => exact prior

theorem length_eq (cut : BilinearInterleaving operation actual leftTrace rightTrace) :
    actual.length = leftTrace.length + rightTrace.length + 1 := by
  induction cut with
  | last => rfl
  | left _ _ prior => simp only [Trace.length] at *; omega
  | right _ _ prior => simp only [Trace.length] at *; omega

def leftPositions {left : Expr V X s} {right : Expr V X t}
    {total : V r} {leftValue : V s} {rightValue : V t}
    {actual : Trace environment (.bilinear operation left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (cut : BilinearInterleaving operation actual leftTrace rightTrace) : List Nat :=
  match cut with
  | .last _ _ => []
  | .left _ tail => 0 :: tail.leftPositions.map Nat.succ
  | .right _ tail => tail.leftPositions.map Nat.succ

def rightPositions {left : Expr V X s} {right : Expr V X t}
    {total : V r} {leftValue : V s} {rightValue : V t}
    {actual : Trace environment (.bilinear operation left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (cut : BilinearInterleaving operation actual leftTrace rightTrace) : List Nat :=
  match cut with
  | .last _ _ => []
  | .left _ tail => tail.rightPositions.map Nat.succ
  | .right _ tail => 0 :: tail.rightPositions.map Nat.succ

theorem leftPositions_length (cut : BilinearInterleaving operation actual leftTrace rightTrace) :
    cut.leftPositions.length = leftTrace.length := by
  induction cut with
  | last => rfl
  | left _ _ prior => simp only [leftPositions, List.length_cons, List.length_map, Trace.length]; omega
  | right _ _ prior => simpa only [leftPositions, List.length_map] using prior

theorem rightPositions_length (cut : BilinearInterleaving operation actual leftTrace rightTrace) :
    cut.rightPositions.length = rightTrace.length := by
  induction cut with
  | last => rfl
  | left _ _ prior => simpa only [rightPositions, List.length_map] using prior
  | right _ _ prior => simp only [rightPositions, List.length_cons, List.length_map, Trace.length]; omega
end BilinearInterleaving

structure BilinearSplit {operation : V s →+ V t →+ V r}
    {left : Expr V X s} {right : Expr V X t} {total : V r}
    (actual : Trace environment (.bilinear operation left right) (.const total)) where
  leftValue : V s
  rightValue : V t
  leftTrace : Trace environment left (.const leftValue)
  rightTrace : Trace environment right (.const rightValue)
  interleaving : BilinearInterleaving operation actual leftTrace rightTrace

/-- Eliminate the actual paid trace; never evaluate either child again. -/
def splitBilinear {operation : V s →+ V t →+ V r}
    {left : Expr V X s} {right : Expr V X t} {total : V r}
    (actual : Trace environment (.bilinear operation left right) (.const total)) : BilinearSplit actual :=
  match actual with
  | .cons (.bilinearConst _ leftValue rightValue) (.nil _) =>
      ⟨leftValue, rightValue, .nil _, .nil _, .last _ _⟩
  | .cons (.bilinearConst _ _ _) (.cons impossible _) => nomatch impossible
  | .cons (.bilinearLeft _ step) tail =>
      let cut := splitBilinear tail
      ⟨cut.leftValue, cut.rightValue, .cons step cut.leftTrace, cut.rightTrace, .left step cut.interleaving⟩
  | .cons (.bilinearRight _ step) tail =>
      let cut := splitBilinear tail
      ⟨cut.leftValue, cut.rightValue, cut.leftTrace, .cons step cut.rightTrace, .right step cut.interleaving⟩

namespace BilinearControls
private abbrev Value (_ : Unit) := ℤ
private abbrev Var (_ : Unit) := Unit
private def env : Env Value Var := fun _ _ => 1
private def op : ℤ →+ ℤ →+ ℤ := 0
private def bound : Step env (.var (s := ()) ()) (.const (env () ())) :=
  @Step.bind Unit Value Var (fun _ => Int.instAddCommGroup) env () ()
private def finalStep (a b : ℤ) : Step env
    (.bilinear (s := ()) (t := ()) (r := ()) op (.const a) (.const b)) (.const (op a b)) :=
  @Step.bilinearConst Unit Value Var (fun _ => Int.instAddCommGroup) env () () () op a b
private def leftFirst : Trace env
    (.bilinear (s := ()) (t := ()) (r := ()) op (.var ()) (.var ())) (.const (op (env () ()) (env () ()))) :=
  .cons (@Step.bilinearLeft Unit Value Var (fun _ => Int.instAddCommGroup) env () () () op _ _ (.var ()) bound)
    (.cons (@Step.bilinearRight Unit Value Var (fun _ => Int.instAddCommGroup) env () () () op (.const (env () ())) _ _ bound)
      (.single (finalStep (env () ()) (env () ()))))
private def rightFirst : Trace env
    (.bilinear (s := ()) (t := ()) (r := ()) op (.var ()) (.var ())) (.const (op (env () ()) (env () ()))) :=
  .cons (@Step.bilinearRight Unit Value Var (fun _ => Int.instAddCommGroup) env () () () op (.var ()) _ _ bound)
    (.cons (@Step.bilinearLeft Unit Value Var (fun _ => Int.instAddCommGroup) env () () () op _ _ (.const (env () ())) bound)
      (.single (finalStep (env () ()) (env () ()))))
private def leftCut : BilinearInterleaving op leftFirst (.single bound) (.single bound) :=
  .left bound (.right bound (.last (env () ()) (env () ())))
private def rightCut : BilinearInterleaving op rightFirst (.single bound) (.single bound) :=
  .right bound (.left bound (.last (env () ()) (env () ())))
theorem equal_output_distinct_order :
    leftCut.leftPositions = [0] ∧ rightCut.leftPositions = [1] ∧
    leftCut.rightPositions = [1] ∧ rightCut.rightPositions = [0] := ⟨rfl,rfl,rfl,rfl⟩
private def constants : Trace env
    (.bilinear (s := ()) (t := ()) (r := ()) op (.const 2) (.const 3)) (.const (op 2 3)) :=
  .single (finalStep 2 3)
private def constantCut : BilinearInterleaving (environment := env) (s := ()) (t := ()) (r := ()) op constants (.nil (.const 2)) (.nil (.const 3)) := .last 2 3
theorem constant_children_keep_parent_payment :
    constants.length = 1 ∧ constantCut.leftPositions=[] ∧ constantCut.rightPositions=[] :=
  ⟨rfl,rfl,rfl⟩
end BilinearControls
end SaturationMonoid.SourceOperationExecution.Trace

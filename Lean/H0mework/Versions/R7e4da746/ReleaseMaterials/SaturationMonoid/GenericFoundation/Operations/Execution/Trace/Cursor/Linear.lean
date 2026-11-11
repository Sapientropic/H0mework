import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Cursor

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.SourceOperationExecution.Trace
open SourceOperationEffects
universe u v w
variable {S : Type u} {V : S → Type v} {X : S → Type w}
  [∀ s, AddCommGroup (V s)] {environment : Env V X} {s : S}

/-- The given child's paid position is realized inside its original linear parent. -/
def LinearInterleaving.liftCursor {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) (cursor : Cursor inside) : Cursor actual :=
  match interleaving, cursor with
  | .last _, impossible => nomatch impossible
  | .step paid tail, .here _ _ => .here (.linear operation paid) _
  | .step paid tail, .there _ _ inner => .there (.linear operation paid) _ (tail.liftCursor inner)

theorem LinearInterleaving.liftCursor_position {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) (cursor : Cursor inside) :
    (interleaving.liftCursor cursor).position = cursor.position := by
  induction interleaving with
  | last => cases cursor
  | step paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inner => exact congrArg (fun n => n+1) (previous inner)

theorem LinearInterleaving.liftCursor_before {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) (cursor : Cursor inside) :
    (interleaving.liftCursor cursor).beforeExpr = .linear operation cursor.beforeExpr := by
  induction interleaving with
  | last => cases cursor
  | step paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inner => exact previous inner

theorem LinearInterleaving.liftCursor_after {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) (cursor : Cursor inside) :
    (interleaving.liftCursor cursor).afterExpr = .linear operation cursor.afterExpr := by
  induction interleaving with
  | last => cases cursor
  | step paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inner => exact previous inner

theorem LinearInterleaving.liftCursor_step {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) (cursor : Cursor inside) :
    HEq (interleaving.liftCursor cursor).paidStep (Step.linear operation cursor.paidStep) := by
  induction interleaving with
  | last => cases cursor
  | step paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inner => exact previous inner

end SaturationMonoid.SourceOperationExecution.Trace

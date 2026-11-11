import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.SourceOperationExecution.Trace
open SourceOperationEffects
universe u v w
variable {S : Type u} {V : S → Type v} {X : S → Type w}
  [∀ s, AddCommGroup (V s)] {environment : Env V X} {s : S}

/-- A paid position in the given trace, including repeated equal steps. -/
inductive Cursor : {before after : Expr V X s} → Trace environment before after → Type (max u v w)
  | here {before middle after : Expr V X s}
      (paid : Step environment before middle) (tail : Trace environment middle after) :
      Cursor (.cons paid tail)
  | there {before middle after : Expr V X s}
      (paid : Step environment before middle) (tail : Trace environment middle after)
      (inside : Cursor tail) : Cursor (.cons paid tail)

namespace Cursor
variable {before after : Expr V X s} {actual : Trace environment before after}

def position {before after : Expr V X s} {actual : Trace environment before after} : Cursor actual → Nat
  | .here _ _ => 0
  | .there _ _ inside => inside.position + 1

def beforeExpr {before after : Expr V X s} {actual : Trace environment before after} : Cursor actual → Expr V X s
  | .here (before := point) _ _ => point
  | .there _ _ inside => inside.beforeExpr

def afterExpr {before after : Expr V X s} {actual : Trace environment before after} : Cursor actual → Expr V X s
  | .here (middle := point) _ _ => point
  | .there _ _ inside => inside.afterExpr

def past {before after : Expr V X s} {actual : Trace environment before after} (cursor : Cursor actual) : Trace environment before cursor.beforeExpr :=
  match cursor with
  | .here _ _ => .nil _
  | .there paid _ inside => .cons paid inside.past

def paidStep {before after : Expr V X s} {actual : Trace environment before after} (cursor : Cursor actual) : Step environment cursor.beforeExpr cursor.afterExpr :=
  match cursor with
  | .here paid _ => paid
  | .there _ _ inside => inside.paidStep

def suffix {before after : Expr V X s} {actual : Trace environment before after} (cursor : Cursor actual) : Trace environment cursor.afterExpr after :=
  match cursor with
  | .here _ tail => tail
  | .there _ _ inside => inside.suffix

theorem reconstruct (cursor : Cursor actual) :
    actual = cursor.past.append (.cons cursor.paidStep cursor.suffix) := by
  induction cursor with
  | here => rfl
  | there paid tail inside previous =>
      exact congrArg (Trace.cons paid) previous

theorem past_length (cursor : Cursor actual) : cursor.past.length = cursor.position := by
  induction cursor with
  | here => rfl
  | there paid tail inside previous =>
      change 1 + inside.past.length = inside.position + 1
      omega

theorem position_lt (cursor : Cursor actual) : cursor.position < actual.length := by
  induction cursor with
  | here => simp only [position, length]; omega
  | there paid tail inside previous => simp only [position, length]; omega

theorem eq_of_position (first second : Cursor actual) (same : first.position = second.position) :
    first = second := by
  induction first with
  | here paid tail =>
      cases second with
      | here => rfl
      | there => simp only [position] at same; omega
  | there paid tail inside previous =>
      cases second with
      | here => simp only [position] at same; omega
      | there _ _ other =>
          exact congrArg (Cursor.there paid tail) (previous other (Nat.add_right_cancel same))

def extend {before after : Expr V X s} {actual : Trace environment before after} {terminal : Expr V X s} (cursor : Cursor actual)
    (rest : Trace environment after terminal) : Cursor (actual.append rest) :=
  match cursor with
  | .here paid tail => .here paid (tail.append rest)
  | .there paid tail inside => .there paid (tail.append rest) (inside.extend rest)

theorem extend_position {terminal : Expr V X s} (cursor : Cursor actual)
    (rest : Trace environment after terminal) : (cursor.extend rest).position = cursor.position := by
  induction cursor with
  | here => rfl
  | there paid tail inside previous => exact congrArg (fun n => n + 1) (previous rest)

def last {before after : Expr V X s} {terminal : Expr V X s} (actual : Trace environment before after)
    (paid : Step environment after terminal) : Cursor (actual.append (.single paid)) :=
  match actual, paid with
  | .nil _, step => .here step (.nil _)
  | .cons head tail, step => .there head _ (last tail step)

theorem last_position {terminal : Expr V X s} (paid : Step environment after terminal) :
    (last actual paid).position = actual.length := by
  induction actual with
  | nil => rfl
  | cons head tail previous =>
      change (last tail paid).position + 1 = 1 + tail.length
      have prior := previous paid
      omega

theorem last_step {terminal : Expr V X s} (paid : Step environment after terminal) :
    HEq (last actual paid).paidStep paid := by
  induction actual with
  | nil => rfl
  | cons head tail previous => exact previous paid

theorem extend_step {terminal : Expr V X s} (cursor : Cursor actual)
    (rest : Trace environment after terminal) :
    HEq (cursor.extend rest).paidStep cursor.paidStep := by
  induction cursor with
  | here => rfl
  | there paid tail inside previous => exact previous rest

def transfer {before : Expr V X s}
    {first second : Σ terminal : Expr V X s, Trace environment before terminal}
    (same : first = second) (cursor : Cursor first.2) : Cursor second.2 := by
  cases same
  exact cursor

theorem transfer_position {first second : Σ terminal : Expr V X s, Trace environment before terminal}
    (same : first = second) (cursor : Cursor first.2) :
    (transfer same cursor).position = cursor.position := by cases same; rfl

theorem transfer_step {first second : Σ terminal : Expr V X s, Trace environment before terminal}
    (same : first = second) (cursor : Cursor first.2) :
    HEq (transfer same cursor).paidStep cursor.paidStep := by cases same; rfl

theorem endpoint_state {terminal : Expr V X s} (actual : Trace environment before after)
    (same : after = terminal) :
    (⟨terminal, Eq.mp (congrArg (fun endpoint => Trace environment before endpoint) same) actual⟩ :
      Σ endpoint : Expr V X s, Trace environment before endpoint) = ⟨after, actual⟩ := by
  cases same
  rfl

end Cursor

theorem append_nil {before after : Expr V X s} (actual : Trace environment before after) :
    actual.append (.nil after) = actual := by
  induction actual with
  | nil => rfl
  | cons paid tail previous => exact congrArg (Trace.cons paid) previous

theorem append_assoc {first middle next last : Expr V X s}
    (left : Trace environment first middle) (center : Trace environment middle next)
    (right : Trace environment next last) :
    (left.append center).append right = left.append (center.append right) := by
  induction left with
  | nil => rfl
  | cons paid tail previous => exact congrArg (Trace.cons paid) (previous center)

def LinearInterleaving.lastCursor {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) : Cursor actual :=
  match interleaving with
  | .last value => .here (.linearConst operation value) (.nil _)
  | .step paid tail => .there (.linear operation paid) _ tail.lastCursor

theorem LinearInterleaving.lastCursor_position {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) :
    interleaving.lastCursor.position = inside.length := by
  induction interleaving with
  | last => rfl
  | step paid tail previous =>
      simp only [lastCursor, Cursor.position, length]
      omega

theorem LinearInterleaving.lastCursor_step {operation : V s →+ V s} {body : Expr V X s} {total input : V s}
    {actual : Trace environment (.linear operation body) (.const total)}
    {inside : Trace environment body (.const input)}
    (interleaving : LinearInterleaving operation actual inside) :
    HEq interleaving.lastCursor.paidStep (Step.linearConst (environment := environment) operation input) := by
  induction interleaving with
  | last => rfl
  | step paid tail previous => exact previous

def AddInterleaving.leftCursor {left right : Expr V X s} {total leftValue rightValue : V s}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace)
    (cursor : Cursor leftTrace) : Cursor actual :=
  match interleaving, cursor with
  | .last _ _, impossible => nomatch impossible
  | .left paid tail, .here _ _ => .here (.addLeft paid) _
  | .left paid tail, .there _ _ inside => .there (.addLeft paid) _ (tail.leftCursor inside)
  | .right paid tail, inside => .there (.addRight paid) _ (tail.leftCursor inside)

def AddInterleaving.rightAtLeft {left right : Expr V X s} {total leftValue rightValue : V s}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace)
    (cursor : Cursor leftTrace) : Expr V X s :=
  match interleaving, cursor with
  | .last _ _, impossible => nomatch impossible
  | .left (right := right) _ _, .here _ _ => right
  | .left _ tail, .there _ _ inside => tail.rightAtLeft inside
  | .right _ tail, inside => tail.rightAtLeft inside

theorem AddInterleaving.leftCursor_step {left right : Expr V X s} {total leftValue rightValue : V s}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace)
    (cursor : Cursor leftTrace) :
    HEq (interleaving.leftCursor cursor).paidStep
      (Step.addLeft (right := interleaving.rightAtLeft cursor) cursor.paidStep) := by
  induction interleaving with
  | last => cases cursor
  | left paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inside => exact previous inside
  | right paid tail previous => exact previous cursor

theorem AddInterleaving.leftCursor_position {left right : Expr V X s} {total leftValue rightValue : V s}
    {actual : Trace environment (.add left right) (.const total)}
    {leftTrace : Trace environment left (.const leftValue)}
    {rightTrace : Trace environment right (.const rightValue)}
    (interleaving : AddInterleaving environment actual leftTrace rightTrace)
    (cursor : Cursor leftTrace) :
    (interleaving.leftCursor cursor).position = interleaving.leftPositions[cursor.position]'(by rw [interleaving.leftPositions_length]; exact cursor.position_lt) := by
  induction interleaving with
  | last => cases cursor
  | left paid tail previous =>
      cases cursor with
      | here => rfl
      | there _ _ inside =>
          simp only [leftCursor, Cursor.position, leftPositions, List.getElem_cons_succ,
            List.getElem_map]
          exact congrArg Nat.succ (previous inside)
  | right paid tail previous =>
      simp only [leftCursor, Cursor.position, leftPositions, List.getElem_map]
      exact congrArg Nat.succ (previous cursor)

end SaturationMonoid.SourceOperationExecution.Trace

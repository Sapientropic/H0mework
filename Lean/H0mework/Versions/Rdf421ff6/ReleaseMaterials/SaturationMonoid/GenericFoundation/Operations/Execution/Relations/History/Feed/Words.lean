import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.WordReceipt
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation
open CofinalHistorySettlement

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

def naturalUsing (environment : Env V X) (expression : Expr V X s) (value : V s)
    (paid : Trace environment expression (.const value)) (count : Nat) :
    Trace environment (Coefficients.naturalExpansion count expression) (.const (count • value)) := by
  induction count with
  | zero =>
      simpa only [Coefficients.naturalExpansion, zero_nsmul] using
        (Trace.nil (environment := environment) (.const (0 : V s)))
  | succ count previous =>
      have assembled := (paid.addLeft (Coefficients.naturalExpansion count expression)).append
        ((Trace.addRight (.const value) previous).append
          (Trace.single (environment := environment) (.addConst value (count • value))))
      simpa only [Coefficients.naturalExpansion, succ_nsmul, add_comm] using assembled

def integerUsing (environment : Env V X) (expression : Expr V X s) (value : V s)
    (paid : Trace environment expression (.const value)) (coefficient : ℤ) :
    Trace environment (Coefficients.integerExpansion coefficient expression) (.const (coefficient • value)) := by
  cases coefficient with
  | ofNat count =>
      change Trace environment (Coefficients.naturalExpansion count expression) (.const ((count : ℤ) • value))
      rw [natCast_zsmul]
      exact naturalUsing environment expression value paid count
  | negSucc count =>
      have assembled := (Trace.linear (-AddMonoidHom.id (V s))
        (naturalUsing environment expression value paid (count + 1))).append
          (Trace.single (environment := environment) (.linearConst (-AddMonoidHom.id (V s)) ((count + 1) • value)))
      simpa only [Coefficients.integerExpansion, AddMonoidHom.neg_apply,
        AddMonoidHom.id_apply, negSucc_zsmul] using assembled

def termsUsing (environment : Env V X) :
    (items : List (Expr V X s × ℤ)) →
    (∀ item ∈ items, Trace environment item.1 (.const (item.1.eval environment))) →
    Trace environment (Coefficients.terms items)
      (.const ((items.map fun item => item.2 • item.1.eval environment).sum))
  | [], _ => .nil _
  | item :: rest, receipts =>
      ((integerUsing environment item.1 (item.1.eval environment)
        (receipts item List.mem_cons_self) item.2).addLeft (Coefficients.terms rest)).append
      ((Trace.addRight (.const (item.2 • item.1.eval environment))
        (termsUsing environment rest fun entry member =>
          receipts entry (List.mem_cons_of_mem item member))).append
        (Trace.single (.addConst _ _)))

theorem request_at_from (position : Nat)
    (before after : List (Event (V := V) (X := X) (s := s)))
    (event : Event (V := V) (X := X) (s := s))
    (item : Expr V X s × ℤ) (present : item ∈ eventItems event) :
    (⟨position + before.length, event, item.1, item.2⟩ : Request (V := V) (X := X) (s := s)) ∈
      requestsFrom position (before ++ event :: after) := by
  induction before generalizing position with
  | nil =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨item, present, rfl⟩)
  | cons head tail previous =>
      have next := List.mem_append_right
        ((eventItems head).map fun pair => (⟨position, head, pair.1, pair.2⟩ : Request (V := V) (X := X) (s := s)))
        (previous (position + 1))
      have index : position + (head :: tail).length = (position + 1) + tail.length := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact next

/-- The slot is part of the source, so duplicate equal words remain distinct occurrences. -/
structure RelationOccurrence (source : Inventory (V := V) (X := X) (s := s)) where
  before : List (Event (V := V) (X := X) (s := s))
  word : Formal ℤ V X s
  after : List (Event (V := V) (X := X) (s := s))
  trace_eq : source.trace = before ++ PresentedRelationEventAt.relation word :: after

def sourceRequest {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : RelationOccurrence source) (item : Expr V X s × ℤ) :
    Request (V := V) (X := X) (s := s) :=
  ⟨occurrence.before.length, .relation occurrence.word, item.1, item.2⟩

theorem source_request_member {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : RelationOccurrence source) (item : Expr V X s × ℤ)
    (present : item ∈ Coefficients.sourceItems occurrence.word) :
    sourceRequest occurrence item ∈ requests source := by
  unfold requests
  rw [occurrence.trace_eq]
  simpa only [Nat.zero_add, sourceRequest] using
    request_at_from 0 occurrence.before occurrence.after (.relation occurrence.word) item present

def supportReceipt (environment : Env V X)
    {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : RelationOccurrence source) (item : Expr V X s × ℤ)
    (_present : item ∈ Coefficients.sourceItems occurrence.word) :
    Trace environment item.1 (.const (item.1.eval environment)) :=
  receipt environment (sourceRequest occurrence item)

/-- This execution assembles the stored per-term receipts with the original integer syntax. -/
def relationTrace (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s))
    (occurrence : RelationOccurrence source) :
    Trace environment (Coefficients.expression occurrence.word)
      (.const (evaluation (R := ℤ) environment occurrence.word)) := by
  have assembled := termsUsing environment (Coefficients.sourceItems occurrence.word) (by
    intro item member
    exact supportReceipt environment occurrence item member)
  have endpoint := (Coefficients.terms_eval (Coefficients.sourceItems occurrence.word) environment).symm.trans
    (Coefficients.expression_eval occurrence.word environment)
  exact endpoint ▸ assembled

def orderedExpression : List (Formal ℤ V X s) → Expr V X s
  | [] => .const 0
  | word :: rest => .add (Coefficients.expression word) (orderedExpression rest)

theorem ordered_eval (words : List (Formal ℤ V X s)) (environment : Env V X) :
    (orderedExpression words).eval environment = evaluation (R := ℤ) environment words.sum := by
  induction words with
  | nil => exact (map_zero _).symm
  | cons word rest previous =>
      simp only [orderedExpression, Expr.eval, Coefficients.expression_eval, previous,
        List.sum_cons, map_add]

/-- Order and repeated paid source words survive in the actual request syntax. -/
def orderedTrace (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s)) :
    (words : List (RelationOccurrence source)) →
    Trace environment (orderedExpression (words.map RelationOccurrence.word))
      (.const (evaluation (R := ℤ) environment (words.map RelationOccurrence.word).sum))
  | [] => by simpa only [List.map_nil, List.sum_nil, map_zero, orderedExpression] using (Trace.nil (.const (0 : V s)))
  | word :: rest => by
      have assembled := ((relationTrace environment source word).addLeft
        (orderedExpression (rest.map RelationOccurrence.word))).append
        ((Trace.addRight (.const (evaluation (R := ℤ) environment word.word))
          (orderedTrace environment source rest)).append (Trace.single (.addConst _ _)))
      simpa only [List.map_cons, List.sum_cons, map_add, orderedExpression] using assembled

/-- The complete free scalar certificate remains available beside its evaluated trace endpoint. -/
def scalarCertificate (environment : Env V X) (words : List (Formal ℤ V X s)) :=
  valueMap (R := ℤ) environment words.sum

theorem scalar_certificate_sum (environment : Env V X) (words : List (Formal ℤ V X s)) :
    scalarCertificate environment words = (words.map (valueMap (R := ℤ) environment)).sum :=
  map_list_sum _ _

def liftStepZero {environment : Env V X} {before after : Expr V X s}
    (paid : Step environment before after) :
    Step (pairEnvironment environment 0) (liftExpr before) (liftExpr after) := by
  induction paid with
  | bind name => exact .bind name
  | addConst left right =>
      simpa only [liftExpr, Prod.mk_add_mk, zero_add] using
        (Step.addConst (environment := pairEnvironment environment 0) (left, (0 : V _)) (right, (0 : V _)))
  | linearConst operation value =>
      simpa only [liftExpr, pairLinear, AddMonoidHom.coe_prodMap, Prod.map_apply, map_zero] using
        (Step.linearConst (environment := pairEnvironment environment 0) (pairLinear operation) (value, (0 : V _)))
  | bilinearConst operation left right =>
      simpa only [liftExpr, pairBilinear_apply, map_zero, AddMonoidHom.zero_apply, zero_add] using
        (Step.bilinearConst (environment := pairEnvironment environment 0) (pairBilinear operation)
          (left, (0 : V _)) (right, (0 : V _)))
  | addLeft _ previous => exact .addLeft previous
  | addRight _ previous => exact .addRight previous
  | linear operation _ previous => exact .linear (pairLinear operation) previous
  | bilinearLeft operation _ previous => exact .bilinearLeft (pairBilinear operation) previous
  | bilinearRight operation _ previous => exact .bilinearRight (pairBilinear operation) previous

def liftTraceZero {environment : Env V X} {before after : Expr V X s}
    (paid : Trace environment before after) :
    Trace (pairEnvironment environment 0) (liftExpr before) (liftExpr after) :=
  match paid with
  | .nil expression => .nil _
  | .cons step tail => .cons (liftStepZero step) (liftTraceZero tail)

end SourceInventoryExecutionFeed.WordReceipt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

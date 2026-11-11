import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.AdmissionReceipt
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation CofinalHistorySettlement
namespace WR
export WordReceipt (RelationOccurrence request_at_from sourceRequest source_request_member
  supportReceipt orderedExpression orderedTrace scalarCertificate integerUsing liftTraceZero)
end WR

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

def naturalCongr {environment : Env V X} {before after : Expr V X s}
    (paid : Trace environment before after) (count : Nat) :
    Trace environment (Coefficients.naturalExpansion count before) (Coefficients.naturalExpansion count after) :=
  match count with
  | 0 => .nil _
  | count + 1 => (paid.addLeft (Coefficients.naturalExpansion count before)).append
      (Trace.addRight after (naturalCongr paid count))

def integerCongr {environment : Env V X} {before after : Expr V X s}
    (paid : Trace environment before after) (coefficient : ℤ) :
    Trace environment (Coefficients.integerExpansion coefficient before) (Coefficients.integerExpansion coefficient after) :=
  match coefficient with
  | .ofNat count => naturalCongr paid count
  | .negSucc count => Trace.linear (-AddMonoidHom.id _) (naturalCongr paid (count + 1))

def termsCongr (environment : Env V X) (replace : Expr V X s → Expr V X s) :
    (items : List (Expr V X s × ℤ)) →
    (∀ item ∈ items, Trace environment item.1 (replace item.1)) →
    Trace environment (Coefficients.terms items)
      (Coefficients.terms (items.map fun item => (replace item.1, item.2)))
  | [], _ => .nil _
  | item :: rest, paid =>
      ((integerCongr (paid item List.mem_cons_self) item.2).addLeft (Coefficients.terms rest)).append
        (Trace.addRight (Coefficients.integerExpansion item.2 (replace item.1))
          (termsCongr environment replace rest fun entry member => paid entry (List.mem_cons_of_mem item member)))

def normalizedItems (environment : Env V X) (word : Formal ℤ V X s) : List (Expr V X s × ℤ) :=
  (Coefficients.sourceItems word).map fun item => (.const (item.1.eval environment), item.2)

def relationPartialTrace (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s)) (occurrence : WR.RelationOccurrence source) :
    Trace environment (Coefficients.expression occurrence.word)
      (Coefficients.terms (normalizedItems environment occurrence.word)) :=
  termsCongr environment (fun expression => .const (expression.eval environment))
    (Coefficients.sourceItems occurrence.word) fun item present => WR.supportReceipt environment occurrence item present

def orderedTerminal (environment : Env V X) : List (Formal ℤ V X s) → Expr V X s
  | [] => .const 0
  | word :: rest => .add (Coefficients.terms (normalizedItems environment word)) (orderedTerminal environment rest)

def orderedPartialTrace (environment : Env V X)
    (source : Inventory (V := V) (X := X) (s := s)) :
    (occurrences : List (WR.RelationOccurrence source)) →
    Trace environment (WR.orderedExpression (occurrences.map WordReceipt.RelationOccurrence.word))
      (orderedTerminal environment (occurrences.map WordReceipt.RelationOccurrence.word))
  | [] => .nil _
  | occurrence :: rest =>
      ((relationPartialTrace environment source occurrence).addLeft
        (WR.orderedExpression (rest.map WordReceipt.RelationOccurrence.word))).append
        (Trace.addRight (Coefficients.terms (normalizedItems environment occurrence.word))
          (orderedPartialTrace environment source rest))

def formalItems (items : List (Expr V X s × ℤ)) : Formal ℤ V X s :=
  (items.map fun item => Finsupp.single item.1 item.2).sum

theorem formal_source_items (word : Formal ℤ V X s) : formalItems (Coefficients.sourceItems word) = word := by
  classical
  change ((word.support.toList.map fun expression => (expression, word expression)).map
    fun item => Finsupp.single item.1 item.2).sum = word
  rw [List.map_map]
  exact (Finset.sum_map_toList _ _).trans (Finsupp.sum_single word)

theorem formal_normalized_items (environment : Env V X) (word : Formal ℤ V X s) :
    formalItems (normalizedItems environment word) = constantMap (R := ℤ) (valueMap (R := ℤ) environment word) := by
  have mapped : ∀ items : List (Expr V X s × ℤ),
      formalItems (items.map fun item => (Expr.const (Var := X) (item.1.eval environment), item.2)) =
      constantMap (R := ℤ) (Var := X) (valueMap (R := ℤ) environment (formalItems items)) := by
    intro items
    induction items with
    | nil => simp only [formalItems, List.map_nil, List.sum_nil, map_zero]
    | cons item rest previous =>
        simpa only [formalItems, List.map_cons, List.sum_cons, map_add, constantMap, valueMap,
          Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
          congrArg (Finsupp.single (.const (item.1.eval environment)) item.2 + ·) previous
  simpa only [normalizedItems, formal_source_items] using mapped (Coefficients.sourceItems word)

theorem terminal_read (old environment : Env V X) (words : List (Formal ℤ V X s)) :
    (orderedTerminal old words).eval environment = evaluation (R := ℤ) old words.sum := by
  induction words with
  | nil => exact (map_zero _).symm
  | cons word rest previous =>
      have head : (Coefficients.terms (normalizedItems old word)).eval environment = evaluation (R := ℤ) old word := by
        rw [Coefficients.terms_eval, normalizedItems, List.map_map]
        exact (Coefficients.terms_eval (Coefficients.sourceItems word) old).symm.trans
          (Coefficients.expression_eval word old)
      simp only [orderedTerminal, Expr.eval, head, previous, List.sum_cons, map_add]

theorem terminal_effect (old environment increment : Env V X) (words : List (Formal ℤ V X s)) :
    (orderedTerminal old words).effect environment increment = 0 := by
  apply add_left_cancel (a := evaluation (R := ℤ) old words.sum)
  rw [← terminal_read old environment words, ← Expr.eval_update, terminal_read, terminal_read, add_zero]

/-- This slot is the literal admission of a previous Feed exposure generator. -/
structure GeneratorOccurrence (source : Inventory (V := V) (X := X) (s := s)) where
  before : List (Event (V := V) (X := X) (s := s))
  expression : Expr V X s
  after : List (Event (V := V) (X := X) (s := s))
  trace_eq : source.trace = before ++ PresentedRelationEventAt.generator expression :: after

def generatorRequest {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : GeneratorOccurrence source) : Request (V := V) (X := X) (s := s) :=
  ⟨occurrence.before.length, .generator occurrence.expression, occurrence.expression, 1⟩

theorem generator_request_member {source : Inventory (V := V) (X := X) (s := s)}
    (occurrence : GeneratorOccurrence source) : generatorRequest occurrence ∈ requests source := by
  unfold requests
  rw [occurrence.trace_eq]
  simpa only [Nat.zero_add, generatorRequest] using
    WR.request_at_from 0 occurrence.before occurrence.after (.generator occurrence.expression)
      (occurrence.expression, 1) List.mem_cons_self

def generatorReceipt (environment : Env V X)
    {source : Inventory (V := V) (X := X) (s := s)} (occurrence : GeneratorOccurrence source) :
    Trace environment occurrence.expression (.const (occurrence.expression.eval environment)) :=
  receipt environment (generatorRequest occurrence)

/-- The two slots are distinct actual events connected by literal source syntax. -/
abbrev Admission (before : Inventory (V := V) (X := X) (s := s))
    (after : Inventory (V := PairValue V) (X := X) (s := s)) :=
  Σ original : WR.RelationOccurrence before,
    (item : { entry : Expr V X s × ℤ // entry ∈ Coefficients.sourceItems original.word }) →
      { admitted : GeneratorOccurrence after // admitted.expression = liftExpr item.val.1 }

def admittedTermTrace (environment : Env (PairValue V) X)
    (before : Inventory (V := V) (X := X) (s := s))
    (after : Inventory (V := PairValue V) (X := X) (s := s)) (admission : Admission before after)
    (item : Expr V X s × ℤ) (present : item ∈ Coefficients.sourceItems admission.1.word) :
    Trace environment (liftExpr item.1) (.const ((liftExpr item.1).eval environment)) := by
  let actual := admission.2 ⟨item, present⟩
  have paid := generatorReceipt environment actual.val
  exact actual.property ▸ paid

theorem natural_lift (expression : Expr V X s) (count : Nat) :
    liftExpr (Coefficients.naturalExpansion count expression) =
      Coefficients.naturalExpansion count (liftExpr expression) := by
  induction count with
  | zero => rfl
  | succ count previous => exact congrArg (Expr.add (liftExpr expression)) previous

theorem integer_lift (expression : Expr V X s) (coefficient : ℤ) :
    liftExpr (Coefficients.integerExpansion coefficient expression) =
      Coefficients.integerExpansion coefficient (liftExpr expression) := by
  have negative : pairLinear (-AddMonoidHom.id (V s)) = -AddMonoidHom.id (PairValue V s) := by ext value <;> rfl
  cases coefficient with
  | ofNat count => exact natural_lift expression count
  | negSucc count => simp only [Coefficients.integerExpansion, liftExpr, natural_lift, negative]

def mappedTermsUsing (environment : Env (PairValue V) X) :
    (items : List (Expr V X s × ℤ)) →
    (∀ item ∈ items, Trace environment (liftExpr item.1) (.const ((liftExpr item.1).eval environment))) →
    Trace environment (liftExpr (Coefficients.terms items))
      (.const ((items.map fun item => item.2 • (liftExpr item.1).eval environment).sum))
  | [], _ => .nil _
  | item :: rest, paid => by
      have integer := WR.integerUsing environment (liftExpr item.1) ((liftExpr item.1).eval environment)
        (paid item List.mem_cons_self) item.2
      rw [Coefficients.terms, liftExpr, integer_lift]
      exact (integer.addLeft (liftExpr (Coefficients.terms rest))).append
        ((Trace.addRight (.const (item.2 • (liftExpr item.1).eval environment))
          (mappedTermsUsing environment rest fun entry member =>
            paid entry (List.mem_cons_of_mem item member))).append (Trace.single (.addConst _ _)))

theorem literal_read (word : Formal ℤ V X s) (environment : Env (PairValue V) X) :
    (liftExpr (Coefficients.expression word)).eval environment =
      evaluation (R := ℤ) environment (liftMap (R := ℤ) word) := by
  let old : Env V X := fun target name => (environment target name).1
  let increment : Env V X := fun target name => (environment target name).2
  have decomposed : environment = pairEnvironment old increment := rfl
  rw [decomposed, eval_liftExpr, Coefficients.expression_eval, Coefficients.expression_effect]
  exact (LinearMap.congr_fun (evaluation_liftMap (R := ℤ) old increment) word).symm

def admittedTrace (environment : Env (PairValue V) X)
    (before : Inventory (V := V) (X := X) (s := s))
    (after : Inventory (V := PairValue V) (X := X) (s := s)) (admission : Admission before after) :
    Trace environment (liftExpr (Coefficients.expression admission.1.word))
      (.const (evaluation (R := ℤ) environment (liftMap (R := ℤ) admission.1.word))) := by
  have assembled := mappedTermsUsing environment (Coefficients.sourceItems admission.1.word)
    (admittedTermTrace environment before after admission)
  exact (assembled.sound.symm.trans (literal_read admission.1.word environment)) ▸ assembled

theorem ordered_literal_read (words : List (Formal ℤ V X s)) (environment : Env (PairValue V) X) :
    (liftExpr (WR.orderedExpression words)).eval environment =
      evaluation (R := ℤ) environment (liftMap (R := ℤ) words.sum) := by
  induction words with
  | nil =>
      simp only [WR.orderedExpression, liftExpr, Expr.eval, List.sum_nil, map_zero]
      rfl
  | cons word rest previous =>
      simp only [WR.orderedExpression, liftExpr, Expr.eval, literal_read, previous, List.sum_cons, map_add]

def orderedAdmittedTrace (environment : Env (PairValue V) X)
    (before : Inventory (V := V) (X := X) (s := s))
    (after : Inventory (V := PairValue V) (X := X) (s := s)) :
    (admissions : List (Admission before after)) →
    Trace environment (liftExpr (WR.orderedExpression (admissions.map fun admission => admission.1.word)))
      (.const (evaluation (R := ℤ) environment (liftMap (R := ℤ) (admissions.map fun admission => admission.1.word).sum)))
  | [] => by
      have zero : ((0 : V s), (0 : V s)) = (0 : PairValue V s) := rfl
      simpa only [List.map_nil, List.sum_nil, map_zero, WR.orderedExpression, liftExpr, zero] using
        (Trace.nil (environment := environment) (.const (0 : PairValue V s)))
  | admission :: rest => by
      have assembled := ((admittedTrace environment before after admission).addLeft
        (liftExpr (WR.orderedExpression (rest.map fun admission => admission.1.word)))).append
        ((Trace.addRight (.const (evaluation (R := ℤ) environment (liftMap (R := ℤ) admission.1.word)))
          (orderedAdmittedTrace environment before after rest)).append (Trace.single (.addConst _ _)))
      simpa only [List.map_cons, List.sum_cons, map_add, WR.orderedExpression, liftExpr] using assembled

def orderedOldPartialTrace (old : Env V X)
    (before : Inventory (V := V) (X := X) (s := s))
    (after : Inventory (V := PairValue V) (X := X) (s := s)) (admissions : List (Admission before after)) :
    Trace (pairEnvironment old 0)
      (liftExpr (WR.orderedExpression (admissions.map fun admission => admission.1.word)))
      (liftExpr (orderedTerminal old (admissions.map fun admission => admission.1.word))) := by
  have paid := orderedPartialTrace old before (admissions.map Sigma.fst)
  simpa only [List.map_map, Function.comp_def] using WR.liftTraceZero paid

theorem terminal_lift_read (old : Env V X) (environment : Env (PairValue V) X)
    (words : List (Formal ℤ V X s)) :
    (liftExpr (orderedTerminal old words)).eval environment =
      (evaluation (R := ℤ) old words.sum, 0) := by
  let before : Env V X := fun target name => (environment target name).1
  let increment : Env V X := fun target name => (environment target name).2
  have decomposed : environment = pairEnvironment before increment := rfl
  rw [decomposed, eval_liftExpr, terminal_read, terminal_effect]

theorem full_scalar_certificate (environment : Env (PairValue V) X)
    (words : List (Formal ℤ V X s)) :
    valueMap (R := ℤ) environment (liftMap (R := ℤ) words.sum) =
      (words.map fun word => valueMap (R := ℤ) environment (liftMap (R := ℤ) word)).sum := by
  simp only [map_list_sum, List.map_map, Function.comp_def]

end SourceInventoryExecutionFeed.AdmissionReceipt
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

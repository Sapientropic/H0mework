/-
  Proposition 25: safe atom-field relational algebra / calculus completeness.

  Proposition 20 closed only the Boolean safety-query fragment.  This module
  adds the next algebraic layer needed by an agent-native database:

    * relations are predicates over a fixed row/state type;
    * algebra supports base relations, Boolean set operations, selection, and
      field-image generation (`image R q`, i.e. follow a relation `R` from any
      row produced by `q`);
    * calculus supports the same primitive relations plus a safe existential
      image binder.

  For this typed safe fragment, algebra and calculus are mutually expressive
  and denotation-preserving.  This is still not unrestricted first-order
  relational completeness: arbitrary joins, schemas/arity changes, recursion,
  aggregation, and source-table quantification remain outside this file.
-/

import H0mework.Realization.Descent.P24

/-! ## Safe atom-field relational algebra -/

/-- Relational algebra over a fixed row type, with field-image generation. -/
inductive FieldRelAlg (Row Base : Type*) where
  | empty
  | top
  | base : Base → FieldRelAlg Row Base
  | union : FieldRelAlg Row Base → FieldRelAlg Row Base → FieldRelAlg Row Base
  | inter : FieldRelAlg Row Base → FieldRelAlg Row Base → FieldRelAlg Row Base
  | diff : FieldRelAlg Row Base → FieldRelAlg Row Base → FieldRelAlg Row Base
  | select : (Row → Prop) → FieldRelAlg Row Base → FieldRelAlg Row Base
  | image : (Row → Row → Prop) → FieldRelAlg Row Base → FieldRelAlg Row Base

namespace FieldRelAlg

/-- Denotation of the safe atom-field algebra. -/
def eval {Row Base : Type*} (env : Base → Row → Prop) :
    FieldRelAlg Row Base → Row → Prop
  | empty, _row => False
  | top, _row => True
  | base b, row => env b row
  | union p q, row => eval env p row ∨ eval env q row
  | inter p q, row => eval env p row ∧ eval env q row
  | diff p q, row => eval env p row ∧ ¬ eval env q row
  | select predicate q, row => predicate row ∧ eval env q row
  | image relation q, row => ∃ source, eval env q source ∧ relation source row

end FieldRelAlg

/-! ## Safe atom-field relational calculus -/

/-- Calculus over the same primitive relations, with a range-restricted
    existential field-image binder. -/
inductive FieldRelCalc (Row Base : Type*) where
  | falsity
  | truth
  | base : Base → FieldRelCalc Row Base
  | pred : (Row → Prop) → FieldRelCalc Row Base
  | not : FieldRelCalc Row Base → FieldRelCalc Row Base
  | and : FieldRelCalc Row Base → FieldRelCalc Row Base → FieldRelCalc Row Base
  | or : FieldRelCalc Row Base → FieldRelCalc Row Base → FieldRelCalc Row Base
  | imageExists :
      (Row → Row → Prop) →
      FieldRelCalc Row Base →
      FieldRelCalc Row Base

namespace FieldRelCalc

/-- Denotation of the safe atom-field calculus. -/
def eval {Row Base : Type*} (env : Base → Row → Prop) :
    FieldRelCalc Row Base → Row → Prop
  | falsity, _row => False
  | truth, _row => True
  | base b, row => env b row
  | pred predicate, row => predicate row
  | not f, row => ¬ eval env f row
  | and p q, row => eval env p row ∧ eval env q row
  | or p q, row => eval env p row ∨ eval env q row
  | imageExists relation f, row => ∃ source, eval env f source ∧ relation source row

end FieldRelCalc

/-! ## Syntax translations -/

/-- Compile algebraic atom-field queries to safe calculus formulas. -/
def fieldAlgToCalc {Row Base : Type*} :
    FieldRelAlg Row Base → FieldRelCalc Row Base
  | FieldRelAlg.empty => FieldRelCalc.falsity
  | FieldRelAlg.top => FieldRelCalc.truth
  | FieldRelAlg.base b => FieldRelCalc.base b
  | FieldRelAlg.union p q => FieldRelCalc.or (fieldAlgToCalc p) (fieldAlgToCalc q)
  | FieldRelAlg.inter p q => FieldRelCalc.and (fieldAlgToCalc p) (fieldAlgToCalc q)
  | FieldRelAlg.diff p q => FieldRelCalc.and (fieldAlgToCalc p)
      (FieldRelCalc.not (fieldAlgToCalc q))
  | FieldRelAlg.select predicate q => FieldRelCalc.and
      (FieldRelCalc.pred predicate) (fieldAlgToCalc q)
  | FieldRelAlg.image relation q => FieldRelCalc.imageExists relation
      (fieldAlgToCalc q)

/-- Compile safe calculus formulas back to atom-field algebra. -/
def fieldCalcToAlg {Row Base : Type*} :
    FieldRelCalc Row Base → FieldRelAlg Row Base
  | FieldRelCalc.falsity => FieldRelAlg.empty
  | FieldRelCalc.truth => FieldRelAlg.top
  | FieldRelCalc.base b => FieldRelAlg.base b
  | FieldRelCalc.pred predicate => FieldRelAlg.select predicate FieldRelAlg.top
  | FieldRelCalc.not f => FieldRelAlg.diff FieldRelAlg.top (fieldCalcToAlg f)
  | FieldRelCalc.and p q => FieldRelAlg.inter (fieldCalcToAlg p) (fieldCalcToAlg q)
  | FieldRelCalc.or p q => FieldRelAlg.union (fieldCalcToAlg p) (fieldCalcToAlg q)
  | FieldRelCalc.imageExists relation f => FieldRelAlg.image relation
      (fieldCalcToAlg f)

/-- THEOREM 1: algebra-to-calculus compilation preserves denotation. -/
theorem fieldAlgToCalc_sound {Row Base : Type*}
    (env : Base → Row → Prop) :
    ∀ q row, FieldRelCalc.eval env (fieldAlgToCalc q) row ↔
      FieldRelAlg.eval env q row := by
  intro q
  induction q with
  | empty =>
      intro row
      rfl
  | top =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | union p q ihp ihq =>
      intro row
      simp [fieldAlgToCalc, FieldRelAlg.eval, FieldRelCalc.eval, ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [fieldAlgToCalc, FieldRelAlg.eval, FieldRelCalc.eval, ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [fieldAlgToCalc, FieldRelAlg.eval, FieldRelCalc.eval, ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [fieldAlgToCalc, FieldRelAlg.eval, FieldRelCalc.eval, ih row]
  | image relation q ih =>
      intro row
      simp [fieldAlgToCalc, FieldRelAlg.eval, FieldRelCalc.eval, ih]

/-- THEOREM 2: calculus-to-algebra compilation preserves denotation. -/
theorem fieldCalcToAlg_sound {Row Base : Type*}
    (env : Base → Row → Prop) :
    ∀ f row, FieldRelAlg.eval env (fieldCalcToAlg f) row ↔
      FieldRelCalc.eval env f row := by
  intro f
  induction f with
  | falsity =>
      intro row
      rfl
  | truth =>
      intro row
      rfl
  | base b =>
      intro row
      rfl
  | pred predicate =>
      intro row
      simp [fieldCalcToAlg, FieldRelAlg.eval, FieldRelCalc.eval]
  | not f ih =>
      intro row
      simp [fieldCalcToAlg, FieldRelAlg.eval, FieldRelCalc.eval, ih row]
  | and p q ihp ihq =>
      intro row
      simp [fieldCalcToAlg, FieldRelAlg.eval, FieldRelCalc.eval, ihp row, ihq row]
  | or p q ihp ihq =>
      intro row
      simp [fieldCalcToAlg, FieldRelAlg.eval, FieldRelCalc.eval, ihp row, ihq row]
  | imageExists relation f ih =>
      intro row
      simp [fieldCalcToAlg, FieldRelAlg.eval, FieldRelCalc.eval, ih]

/-- THEOREM 3: every safe atom-field algebra query has an equivalent calculus
    formula. -/
theorem fieldAlg_expressible_by_calc {Row Base : Type*}
    (env : Base → Row → Prop) (q : FieldRelAlg Row Base) :
    ∃ f, ∀ row, FieldRelCalc.eval env f row ↔ FieldRelAlg.eval env q row := by
  exact ⟨fieldAlgToCalc q, fieldAlgToCalc_sound env q⟩

/-- THEOREM 4: every safe atom-field calculus formula has an equivalent
    algebraic query. -/
theorem fieldCalc_expressible_by_alg {Row Base : Type*}
    (env : Base → Row → Prop) (f : FieldRelCalc Row Base) :
    ∃ q, ∀ row, FieldRelAlg.eval env q row ↔ FieldRelCalc.eval env f row := by
  exact ⟨fieldCalcToAlg f, fieldCalcToAlg_sound env f⟩

/-! ## AIppocampus safety bridge -/

/-- `C_safe` as a safe atom-field relational algebra query. -/
def cSafeFieldRelAlg {State : Type*} : FieldRelAlg State SemanticAtom :=
  FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.sourceReachability)
    (FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.authorityMonotonicity)
      (FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.graphConfluence)
        (FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.gaugeInvariance)
          (FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.contractionCertification)
            (FieldRelAlg.inter (FieldRelAlg.base SemanticAtom.omegaGluing)
              (FieldRelAlg.base SemanticAtom.freshnessValidity))))))

/-- THEOREM 5: `C_safe` is a relation query in the safe atom-field algebra. -/
theorem cSafeFieldRelAlg_eval_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    FieldRelAlg.eval (semanticHolds P) cSafeFieldRelAlg x ↔ CSafe P x := by
  simp [cSafeFieldRelAlg, FieldRelAlg.eval, semanticHolds, CSafe]

/-- A one-step field image over an AIppocampus semantic relation. -/
def semanticFieldImageQuery {State : Type*}
    (relation : State → State → Prop)
    (q : FieldRelAlg State SemanticAtom) :
    FieldRelAlg State SemanticAtom :=
  FieldRelAlg.image relation q

/-- THEOREM 6: field-image query semantics is exactly existential traversal
    along the supplied relation. -/
theorem semanticFieldImageQuery_eval {State : Type*}
    (P : CSafePredicates State)
    (relation : State → State → Prop)
    (q : FieldRelAlg State SemanticAtom)
    (target : State) :
    FieldRelAlg.eval (semanticHolds P) (semanticFieldImageQuery relation q) target ↔
      ∃ source, FieldRelAlg.eval (semanticHolds P) q source ∧
        relation source target := by
  rfl

/-!
  Summary:
  - Safe atom-field algebra and safe atom-field calculus are mutually
    expressive.
  - The field/generative step is represented as a range-restricted existential
    image along an explicit relation.  This is the algebraic heart of
    "query-as-generation" for a materialized or certified field relation.

  Boundary:
  - The theorem is complete for the syntax in this file, not for unrestricted
    first-order logic or arbitrary AI-generated candidate creation.
  - The supplied relation may itself be expensive or model-generated; this file
    proves denotational equivalence, not candidate-generation cost or
    mechanism-faithfulness.
-/

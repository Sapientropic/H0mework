import H0mework.Computation.SelfReduction.P692

/-!
# Proposition 693: concrete pure-literal exact layer elimination

P692 states the layered-obstruction SAT preprocessor as a certificate.  This
file supplies the first concrete layer producer: pure-literal elimination.

A variable is pure when every occurrence of that variable has the same polarity.
That is the CNF-level version of "no local polarity conflict": the eliminated
variable is exact/path-additive, clauses satisfied by that literal can be
deleted, and the residual formula is satisfiable iff the original is.

Boundary: this proves the pure-literal layer.  It does not yet implement unit
propagation, automatic repeated layer discovery, or polynomial bounds on the
number of layers before the terminal P691 multi-path merge.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

universe u

/-! ## Pure literals and residual formulas -/

/-- A literal matches a chosen variable and polarity. -/
def literalMatches {n : Nat} (v : Fin n) (polarity : Bool)
    (lit : CNFLiteral n) : Bool :=
  decide (lit.var = v ∧ lit.positive = polarity)

/-- A clause contains the chosen pure literal. -/
def clauseContainsLiteral {n : Nat} (clause : CNFClause n)
    (v : Fin n) (polarity : Bool) : Bool :=
  clause.any (literalMatches v polarity)

/-- Remove every clause already satisfied by the chosen pure literal. -/
def pureLiteralResidual {n : Nat} (formula : CNFFormula n)
    (v : Fin n) (polarity : Bool) : CNFFormula n :=
  formula.filter (fun clause => !(clauseContainsLiteral clause v polarity))

/-- Force one variable to the pure polarity, leaving all other variables as
the residual assignment says. -/
def forceAssignment {n : Nat} (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool) : Nat -> Bool :=
  fun i => if i = v.val then polarity else assignment i

/-- The chosen variable is pure in the formula: every occurrence has the chosen
polarity. -/
def PureLiteralInFormula {n : Nat} (formula : CNFFormula n)
    (v : Fin n) (polarity : Bool) : Prop :=
  ∀ clause : CNFClause n, clause ∈ formula ->
    ∀ lit : CNFLiteral n, lit ∈ clause ->
      lit.var = v -> lit.positive = polarity

/-- The pure literal actually occurs, so the layer removes at least one clause.
-/
def PureLiteralOccurs {n : Nat} (formula : CNFFormula n)
    (v : Fin n) (polarity : Bool) : Prop :=
  ∃ clause : CNFClause n, clause ∈ formula ∧
    clauseContainsLiteral clause v polarity = true

/-! ## Clause-level facts -/

/-- THEOREM 1: a matching literal evaluates to true under the forced
assignment. -/
theorem literal_eval_true_of_matches {n : Nat}
    (v : Fin n) (polarity : Bool) (assignment : Nat -> Bool)
    (lit : CNFLiteral n)
    (hmatch : literalMatches v polarity lit = true) :
    CNFLiteral.eval lit (forceAssignment v polarity assignment) = true := by
  have hprop : lit.var = v ∧ lit.positive = polarity := by
    exact of_decide_eq_true hmatch
  rcases hprop with ⟨hvar, hpol⟩
  have hval : lit.var.val = v.val := congrArg Fin.val hvar
  unfold CNFLiteral.eval forceAssignment
  rw [hpol]
  cases polarity <;> simp [hval]

/-- THEOREM 2: a clause containing the pure literal is satisfied under the
forced assignment. -/
theorem clause_eval_true_of_contains_literal {n : Nat}
    (clause : CNFClause n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hcontains : clauseContainsLiteral clause v polarity = true) :
    CNFClause.eval clause (forceAssignment v polarity assignment) = true := by
  unfold clauseContainsLiteral at hcontains
  rw [List.any_eq_true] at hcontains
  change clause.any
      (fun lit => CNFLiteral.eval lit (forceAssignment v polarity assignment)) =
    true
  rw [List.any_eq_true]
  rcases hcontains with ⟨lit, hlit, hmatch⟩
  exact ⟨lit, hlit, literal_eval_true_of_matches v polarity assignment lit hmatch⟩

/-- THEOREM 3: if a pure clause does not contain the selected pure literal,
then it contains no occurrence of that variable at all. -/
theorem no_var_of_pure_and_not_contains {n : Nat}
    {formula : CNFFormula n} {clause : CNFClause n}
    {v : Fin n} {polarity : Bool}
    (hpure : PureLiteralInFormula formula v polarity)
    (hclause : clause ∈ formula)
    (hnot : clauseContainsLiteral clause v polarity = false) :
    ∀ lit : CNFLiteral n, lit ∈ clause -> lit.var ≠ v := by
  intro lit hlit hvar
  have hpol : lit.positive = polarity :=
    hpure clause hclause lit hlit hvar
  have hmatch : literalMatches v polarity lit = true := by
    simp [literalMatches, hvar, hpol]
  have hcontains_true :
      clauseContainsLiteral clause v polarity = true := by
    rw [clauseContainsLiteral, List.any_eq_true]
    exact ⟨lit, hlit, hmatch⟩
  rw [hcontains_true] at hnot
  contradiction

/-- THEOREM 4: a literal whose variable is not forced evaluates the same before
and after forcing. -/
theorem literal_eval_force_eq_of_ne {n : Nat}
    (v : Fin n) (polarity : Bool) (assignment : Nat -> Bool)
    (lit : CNFLiteral n) (hne : lit.var ≠ v) :
    CNFLiteral.eval lit (forceAssignment v polarity assignment) =
      CNFLiteral.eval lit assignment := by
  have hval : lit.var.val ≠ v.val := by
    intro h
    exact hne (Fin.ext h)
  cases lit.positive <;>
    simp [CNFLiteral.eval, forceAssignment, hval]

/-- THEOREM 5: if a clause has no occurrence of the forced variable, its
truth value is invariant under forcing. -/
theorem clause_eval_force_eq_of_no_var {n : Nat}
    (clause : CNFClause n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hno : ∀ lit : CNFLiteral n, lit ∈ clause -> lit.var ≠ v) :
    CNFClause.eval clause (forceAssignment v polarity assignment) =
      CNFClause.eval clause assignment := by
  rw [CNFClause.eval, CNFClause.eval]
  induction clause with
  | nil =>
      simp
  | cons lit rest ih =>
      have hne : lit.var ≠ v := hno lit (by simp)
      have hrest : ∀ lit' : CNFLiteral n, lit' ∈ rest -> lit'.var ≠ v := by
        intro lit' hmem
        exact hno lit' (by simp [hmem])
      have hLit :=
        literal_eval_force_eq_of_ne v polarity assignment lit hne
      have hRest := ih hrest
      simp [List.any_cons, hLit, hRest]

/-! ## Formula-level pure-literal elimination -/

/-- THEOREM 6: a satisfying assignment for the residual formula lifts to a
satisfying assignment for the original formula by forcing the pure variable. -/
theorem pureLiteral_terminal_to_initial {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (hpure : PureLiteralInFormula formula v polarity)
    (assignment : Nat -> Bool)
    (hres :
      CNFFormula.eval (pureLiteralResidual formula v polarity) assignment =
        true) :
    CNFFormula.eval formula (forceAssignment v polarity assignment) = true := by
  rw [CNFFormula.eval]
  rw [List.all_eq_true]
  intro clause hclause
  by_cases hcontains : clauseContainsLiteral clause v polarity = true
  · exact clause_eval_true_of_contains_literal
      clause v polarity assignment hcontains
  · have hcontains_false :
        clauseContainsLiteral clause v polarity = false := by
      cases h :
          clauseContainsLiteral clause v polarity
      · rfl
      · exact False.elim (hcontains h)
    have hfilter :
        (!(clauseContainsLiteral clause v polarity)) = true := by
      simp [hcontains_false]
    have hclause_res :
        clause ∈ pureLiteralResidual formula v polarity := by
      rw [pureLiteralResidual, List.mem_filter]
      exact ⟨hclause, hfilter⟩
    have hres_clause :
        CNFClause.eval clause assignment = true := by
      have hall := (List.all_eq_true).mp hres
      exact hall clause hclause_res
    have hno :
        ∀ lit : CNFLiteral n, lit ∈ clause -> lit.var ≠ v :=
      no_var_of_pure_and_not_contains hpure hclause hcontains_false
    have hstable :
        CNFClause.eval clause (forceAssignment v polarity assignment) =
          CNFClause.eval clause assignment :=
      clause_eval_force_eq_of_no_var clause v polarity assignment hno
    rw [hstable]
    exact hres_clause

/-- THEOREM 7: any satisfying assignment of the original formula satisfies the
residual formula on the remaining clauses. -/
theorem pureLiteral_initial_to_terminal {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hinit : CNFFormula.eval formula assignment = true) :
    CNFFormula.eval (pureLiteralResidual formula v polarity) assignment =
      true := by
  rw [CNFFormula.eval]
  rw [List.all_eq_true]
  intro clause hclause
  have hmem_formula : clause ∈ formula :=
    (List.mem_filter.mp hclause).1
  have hall := (List.all_eq_true).mp hinit
  exact hall clause hmem_formula

/-- THEOREM 8: pure-literal elimination preserves satisfiability. -/
theorem pureLiteral_satisfiable_iff_residual {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (hpure : PureLiteralInFormula formula v polarity) :
    CNFSatisfiable formula ↔
      CNFSatisfiable (pureLiteralResidual formula v polarity) := by
  constructor
  · intro h
    rcases h with ⟨assignment, hinit⟩
    exact ⟨assignment,
      pureLiteral_initial_to_terminal formula v polarity assignment hinit⟩
  · intro h
    rcases h with ⟨assignment, hres⟩
    exact ⟨forceAssignment v polarity assignment,
      pureLiteral_terminal_to_initial formula v polarity hpure assignment hres⟩

/-- THEOREM 9: an active pure-literal layer strictly shortens the formula list.
-/
theorem pureLiteralResidual_length_lt {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (hOccurs : PureLiteralOccurs formula v polarity) :
    (pureLiteralResidual formula v polarity).length < formula.length := by
  let keep : CNFClause n -> Bool :=
    fun clause => !(clauseContainsLiteral clause v polarity)
  have hle : (formula.filter keep).length ≤ formula.length :=
    List.length_filter_le keep formula
  have hne : (formula.filter keep).length ≠ formula.length := by
    intro heq
    have hall : ∀ clause ∈ formula, keep clause = true :=
      (List.length_filter_eq_length_iff).mp heq
    rcases hOccurs with ⟨clause, hmem, hcontains⟩
    have hkeep_false : keep clause = false := by
      simp [keep, hcontains]
    have hkeep_true := hall clause hmem
    rw [hkeep_false] at hkeep_true
    contradiction
  have hlt : (formula.filter keep).length < formula.length :=
    Nat.lt_of_le_of_ne hle hne
  simpa [pureLiteralResidual, keep] using hlt

/-! ## Concrete P692 producer -/

/-- A concrete pure-literal exact layer.  `phase_exact` attaches the CNF
polarity fact to P116's exact/path-additive criterion. -/
structure CNFPureLiteralExactLayer {n : Nat}
    (formula : CNFFormula n) (Index : Type u) [Inhabited Index] where
  var : Fin n
  polarity : Bool
  phase : CNFVariablePhase n Index
  pure : PureLiteralInFormula formula var polarity
  occurs : PureLiteralOccurs formula var polarity
  phase_exact : PathAdditive (phase var)

namespace CNFPureLiteralExactLayer

variable {n : Nat} {formula : CNFFormula n} {Index : Type u}
variable [Inhabited Index]
variable (P : CNFPureLiteralExactLayer formula Index)

/-- The residual formula after deleting clauses satisfied by the pure literal.
-/
def residualFormula : CNFFormula n :=
  pureLiteralResidual formula P.var P.polarity

/-- THEOREM 10: the selected pure variable is exact in the P116 sense. -/
theorem selected_exact :
    PathAdditive (P.phase P.var) :=
  P.phase_exact

/-- THEOREM 11: the pure literal layer instantiates P692's layered
obstruction-elimination certificate. -/
def toLayeredObstructionElimination :
    CNFLayeredObstructionElimination formula Index where
  terminalFormula := P.residualFormula
  phase := P.phase
  layerCount := 1
  initialObstructionRank := formula.length
  terminalObstructionRank := P.residualFormula.length
  rank_nonincreasing := by
    dsimp [residualFormula, pureLiteralResidual]
    exact List.length_filter_le
      (fun clause : CNFClause n =>
        !(clauseContainsLiteral clause P.var P.polarity))
      formula
  rank_strict_if_layered := by
    intro _h
    exact pureLiteralResidual_length_lt
      formula P.var P.polarity P.occurs
  liftAssignment := forceAssignment P.var P.polarity
  terminal_to_initial_verify := by
    intro assignment hVerify
    constructor
    · exact pureLiteral_terminal_to_initial
        formula P.var P.polarity P.pure assignment hVerify.1
    · intro i hi
      simp [CNFSATNode.root] at hi
  initial_to_terminal_satisfiable := by
    intro h
    exact (pureLiteral_satisfiable_iff_residual
      formula P.var P.polarity P.pure).1 h

/-- THEOREM 12: pure-literal elimination preserves satisfiability. -/
theorem satisfiable_iff_residual :
    CNFSatisfiable formula ↔ CNFSatisfiable P.residualFormula :=
  pureLiteral_satisfiable_iff_residual
    formula P.var P.polarity P.pure

end CNFPureLiteralExactLayer

/-! ## Packaged certificate -/

/-- P693 certificate: pure-literal elimination is a concrete exact layer feeding
P692. -/
structure PureLiteralExactLayerSATCertificate where
  p692_layered_root :
    LayeredObstructionEliminationSATCertificate
  pure_literal_satisfiable_iff_residual :
    ∀ {n : Nat} {formula : CNFFormula n}
      (v : Fin n) (polarity : Bool)
      (_ : PureLiteralInFormula formula v polarity),
      CNFSatisfiable formula ↔
        CNFSatisfiable (pureLiteralResidual formula v polarity)
  pure_literal_residual_rank_decreases :
    ∀ {n : Nat} {formula : CNFFormula n}
      (v : Fin n) (polarity : Bool)
      (_ : PureLiteralOccurs formula v polarity),
      (pureLiteralResidual formula v polarity).length < formula.length
  to_layered_elimination :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (_ : CNFPureLiteralExactLayer formula Index),
      CNFLayeredObstructionElimination formula Index

/-- DEFINITION 1: canonical P693 pure-literal exact-layer certificate. -/
def pureLiteralExactLayerSATCertificate :
    PureLiteralExactLayerSATCertificate where
  p692_layered_root := layeredObstructionEliminationSATCertificate
  pure_literal_satisfiable_iff_residual := by
    intro n formula v polarity hpure
    exact pureLiteral_satisfiable_iff_residual formula v polarity hpure
  pure_literal_residual_rank_decreases := by
    intro n formula v polarity hOccurs
    exact pureLiteralResidual_length_lt formula v polarity hOccurs
  to_layered_elimination := by
    intro n formula Index _ P
    exact P.toLayeredObstructionElimination

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P693 grand root: concrete pure-literal exact-layer elimination feeds the
P692 layered obstruction-elimination root. -/
structure PureLiteralExactLayerSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p692_root :
    LayeredObstructionEliminationSATUnifiedRootCertificate.{u, v, w, z} E0
  pure_literal_layer :
    PureLiteralExactLayerSATCertificate.{v}

/-- THEOREM 13: the pure-literal exact-layer unified root is inhabited. -/
def pureLiteralExactLayerSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    PureLiteralExactLayerSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p692_root := layeredObstructionEliminationSATUnifiedRootCertificate (E0 := E0)
  pure_literal_layer := pureLiteralExactLayerSATCertificate

end GrandUnification

end SaturationMonoid

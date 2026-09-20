import H0mework.Computation.SelfReduction.P693

/-!
# Proposition 694: concrete unit-propagation layer elimination

P693 supplied a pure-literal exact layer.  This file supplies the other standard
CNF preprocessing layer named in the P116 discussion: unit propagation.

Given a unit clause `[v := polarity]`, force that variable, delete every clause
already satisfied by the forced literal, and remove the opposite literal from
the remaining clauses.  Lean proves that this residual formula is satisfiable
iff the original formula is satisfiable, and that an active unit layer strictly
shortens the clause list.  The resulting concrete layer instantiates P692's
layered-obstruction certificate.

Boundary: this is one certified unit-propagation layer.  It does not implement
automatic repeated unit discovery, watched literals, a propagation queue, or a
polynomial bound on total preprocessing iterations.
-/

noncomputable section

namespace SaturationMonoid
namespace ComplexityProjection

set_option linter.checkUnivs false

universe u

/-! ## Unit clauses and residual formulas -/

/-- The literal with the selected variable and polarity. -/
def mkCNFLiteral {n : Nat} (v : Fin n) (polarity : Bool) : CNFLiteral n where
  var := v
  positive := polarity

/-- The unit clause forcing the selected variable and polarity. -/
def unitLiteralClause {n : Nat} (v : Fin n) (polarity : Bool) :
    CNFClause n :=
  [mkCNFLiteral v polarity]

/-- A formula contains the selected unit clause. -/
def UnitLiteralInFormula {n : Nat} (formula : CNFFormula n)
    (v : Fin n) (polarity : Bool) : Prop :=
  unitLiteralClause v polarity ∈ formula

/-- Remove the opposite literal from a clause after the selected unit literal
has been forced. -/
def clauseRemoveOpposite {n : Nat} (clause : CNFClause n)
    (v : Fin n) (polarity : Bool) : CNFClause n :=
  clause.filter (fun lit => !(literalMatches v (!polarity) lit))

/-- Unit-propagation residual: delete satisfied clauses and remove the forced
literal's opposite from every remaining clause. -/
def unitPropagationResidual {n : Nat} (formula : CNFFormula n)
    (v : Fin n) (polarity : Bool) : CNFFormula n :=
  (formula.filter (fun clause => !(clauseContainsLiteral clause v polarity))).map
    (fun clause => clauseRemoveOpposite clause v polarity)

/-! ## Literal and clause facts -/

/-- THEOREM 1: the selected unit clause contains its selected literal. -/
theorem unit_clause_contains_literal {n : Nat}
    (v : Fin n) (polarity : Bool) :
    clauseContainsLiteral (unitLiteralClause v polarity) v polarity = true := by
  simp [unitLiteralClause, mkCNFLiteral, clauseContainsLiteral, literalMatches]

/-- THEOREM 2: a literal matching the opposite polarity is false under the
forced assignment. -/
theorem literal_eval_false_of_opposite_matches {n : Nat}
    (v : Fin n) (polarity : Bool) (assignment : Nat -> Bool)
    (lit : CNFLiteral n)
    (hmatch : literalMatches v (!polarity) lit = true) :
    CNFLiteral.eval lit (forceAssignment v polarity assignment) = false := by
  have hprop : lit.var = v ∧ lit.positive = !polarity := by
    exact of_decide_eq_true hmatch
  rcases hprop with ⟨hvar, hpol⟩
  have hval : lit.var.val = v.val := congrArg Fin.val hvar
  unfold CNFLiteral.eval forceAssignment
  rw [hpol]
  cases polarity <;> simp [hval]

/-- THEOREM 3: if a literal matches neither the forced polarity nor its
opposite, then it is not a literal over the forced variable. -/
theorem literal_var_ne_of_no_polarity_match {n : Nat}
    (v : Fin n) (polarity : Bool) (lit : CNFLiteral n)
    (hsame : literalMatches v polarity lit = false)
    (hopp : literalMatches v (!polarity) lit = false) :
    lit.var ≠ v := by
  intro hvar
  cases hpos : lit.positive <;> cases hpol : polarity <;>
    simp [literalMatches, hvar, hpos, hpol] at hsame hopp

/-- THEOREM 4: after a unit assignment, deleting opposite literals from a
clause that does not already contain the forced literal preserves truth value.
-/
theorem clause_eval_force_eq_remove_opposite_of_not_contains {n : Nat}
    (clause : CNFClause n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hnot : clauseContainsLiteral clause v polarity = false) :
    CNFClause.eval clause (forceAssignment v polarity assignment) =
      CNFClause.eval (clauseRemoveOpposite clause v polarity) assignment := by
  induction clause with
  | nil =>
      simp [CNFClause.eval, clauseRemoveOpposite]
  | cons lit rest ih =>
      have hparts :
          literalMatches v polarity lit = false ∧
            clauseContainsLiteral rest v polarity = false := by
        unfold clauseContainsLiteral at hnot
        simp at hnot
        rcases hnot with ⟨hLit, hRest⟩
        constructor
        · exact hLit
        · unfold clauseContainsLiteral
          rw [List.any_eq_false]
          intro x hx htrue
          have hfalse := hRest x hx
          rw [hfalse] at htrue
          contradiction
      have hsame : literalMatches v polarity lit = false := hparts.1
      have hrest : clauseContainsLiteral rest v polarity = false := hparts.2
      have hRestEval := ih hrest
      cases hopp : literalMatches v (!polarity) lit
      · have hne : lit.var ≠ v :=
          literal_var_ne_of_no_polarity_match v polarity lit hsame hopp
        have hLitEval :=
          literal_eval_force_eq_of_ne v polarity assignment lit hne
        simpa [CNFClause.eval, clauseRemoveOpposite, hopp, hLitEval] using
          congrArg (fun b => CNFLiteral.eval lit assignment || b) hRestEval
      · have hLitFalse :=
          literal_eval_false_of_opposite_matches v polarity assignment lit hopp
        simpa [CNFClause.eval, clauseRemoveOpposite, hopp, hLitFalse] using
          hRestEval

/-- THEOREM 5: a satisfying assignment for a formula containing the selected
unit clause assigns the unit variable to the forced polarity. -/
theorem assignment_eq_polarity_of_unit_clause_satisfied {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hunit : UnitLiteralInFormula formula v polarity)
    (hinit : CNFFormula.eval formula assignment = true) :
    assignment v.val = polarity := by
  have hclause :
      CNFClause.eval (unitLiteralClause v polarity) assignment = true := by
    have hall := (List.all_eq_true).mp hinit
    exact hall (unitLiteralClause v polarity) hunit
  cases polarity <;>
    simp [unitLiteralClause, mkCNFLiteral, CNFClause.eval, CNFLiteral.eval] at hclause ⊢ <;>
      exact hclause

/-- THEOREM 6: if an assignment already has the forced value, forcing it is
extensionally the identity. -/
theorem forceAssignment_eq_self_of_value {n : Nat}
    (v : Fin n) (polarity : Bool) (assignment : Nat -> Bool)
    (hval : assignment v.val = polarity) :
    forceAssignment v polarity assignment = assignment := by
  funext i
  by_cases hi : i = v.val
  · simp [forceAssignment, hi, hval]
  · simp [forceAssignment, hi]

/-! ## Formula-level unit propagation -/

/-- THEOREM 7: a residual satisfying assignment lifts to a satisfying
assignment for the original formula by forcing the unit variable. -/
theorem unitPropagation_terminal_to_initial {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hres :
      CNFFormula.eval (unitPropagationResidual formula v polarity) assignment =
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
    let simplified := clauseRemoveOpposite clause v polarity
    have hfilter :
        (!(clauseContainsLiteral clause v polarity)) = true := by
      simp [hcontains_false]
    have hclause_res :
        simplified ∈ unitPropagationResidual formula v polarity := by
      unfold unitPropagationResidual
      rw [List.mem_map]
      exact ⟨clause, by
        rw [List.mem_filter]
        exact ⟨hclause, hfilter⟩, rfl⟩
    have hres_clause :
        CNFClause.eval simplified assignment = true := by
      have hall := (List.all_eq_true).mp hres
      exact hall simplified hclause_res
    have hstable :
        CNFClause.eval clause (forceAssignment v polarity assignment) =
          CNFClause.eval simplified assignment :=
      clause_eval_force_eq_remove_opposite_of_not_contains
        clause v polarity assignment hcontains_false
    rw [hstable]
    exact hres_clause

/-- THEOREM 8: any satisfying assignment of the original formula satisfies the
unit-propagation residual formula. -/
theorem unitPropagation_initial_to_terminal {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (assignment : Nat -> Bool)
    (hunit : UnitLiteralInFormula formula v polarity)
    (hinit : CNFFormula.eval formula assignment = true) :
    CNFFormula.eval (unitPropagationResidual formula v polarity) assignment =
      true := by
  have hval :
      assignment v.val = polarity :=
    assignment_eq_polarity_of_unit_clause_satisfied
      formula v polarity assignment hunit hinit
  have hforce :
      forceAssignment v polarity assignment = assignment :=
    forceAssignment_eq_self_of_value v polarity assignment hval
  rw [CNFFormula.eval]
  rw [List.all_eq_true]
  intro simplified hsimplified
  rcases (List.mem_map.mp hsimplified) with ⟨clause, hclause_filter, hsimp⟩
  rcases (List.mem_filter.mp hclause_filter) with ⟨hclause, hkeep⟩
  have hcontains_false :
      clauseContainsLiteral clause v polarity = false := by
    cases h : clauseContainsLiteral clause v polarity
    · rfl
    · simp [h] at hkeep
  have horig :
      CNFClause.eval clause assignment = true := by
    have hall := (List.all_eq_true).mp hinit
    exact hall clause hclause
  have hforced :
      CNFClause.eval clause (forceAssignment v polarity assignment) = true := by
    simpa [hforce] using horig
  have hstable :
      CNFClause.eval clause (forceAssignment v polarity assignment) =
        CNFClause.eval (clauseRemoveOpposite clause v polarity) assignment :=
    clause_eval_force_eq_remove_opposite_of_not_contains
      clause v polarity assignment hcontains_false
  have hsimplified_eval :
      CNFClause.eval (clauseRemoveOpposite clause v polarity) assignment =
        true := by
    rwa [hstable] at hforced
  simpa [hsimp] using hsimplified_eval

/-- THEOREM 9: unit propagation preserves satisfiability. -/
theorem unitPropagation_satisfiable_iff_residual {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (hunit : UnitLiteralInFormula formula v polarity) :
    CNFSatisfiable formula ↔
      CNFSatisfiable (unitPropagationResidual formula v polarity) := by
  constructor
  · intro h
    rcases h with ⟨assignment, hinit⟩
    exact ⟨assignment,
      unitPropagation_initial_to_terminal
        formula v polarity assignment hunit hinit⟩
  · intro h
    rcases h with ⟨assignment, hres⟩
    exact ⟨forceAssignment v polarity assignment,
      unitPropagation_terminal_to_initial
        formula v polarity assignment hres⟩

/-- THEOREM 10: an active unit-propagation layer strictly shortens the formula
list by deleting at least the selected unit clause. -/
theorem unitPropagationResidual_length_lt {n : Nat}
    (formula : CNFFormula n) (v : Fin n) (polarity : Bool)
    (hunit : UnitLiteralInFormula formula v polarity) :
    (unitPropagationResidual formula v polarity).length < formula.length := by
  let keep : CNFClause n -> Bool :=
    fun clause => !(clauseContainsLiteral clause v polarity)
  have hle : (formula.filter keep).length ≤ formula.length :=
    List.length_filter_le keep formula
  have hne : (formula.filter keep).length ≠ formula.length := by
    intro heq
    have hall : ∀ clause ∈ formula, keep clause = true :=
      (List.length_filter_eq_length_iff).mp heq
    have hkeep_false : keep (unitLiteralClause v polarity) = false := by
      simp [keep, unit_clause_contains_literal]
    have hkeep_true := hall (unitLiteralClause v polarity) hunit
    rw [hkeep_false] at hkeep_true
    contradiction
  have hlt : (formula.filter keep).length < formula.length :=
    Nat.lt_of_le_of_ne hle hne
  simpa [unitPropagationResidual, keep] using hlt

/-! ## Concrete P692 producer -/

/-- A concrete unit-propagation layer.  `phase_forced` records the selected
variable's phase data; unlike pure literals, unit propagation is a forced
constraint layer and need not assert that the selected variable is
path-additive. -/
structure CNFUnitPropagationLayer {n : Nat}
    (formula : CNFFormula n) (Index : Type u) [Inhabited Index] where
  var : Fin n
  polarity : Bool
  phase : CNFVariablePhase n Index
  unit : UnitLiteralInFormula formula var polarity

namespace CNFUnitPropagationLayer

variable {n : Nat} {formula : CNFFormula n} {Index : Type u}
variable [Inhabited Index]
variable (P : CNFUnitPropagationLayer formula Index)

/-- The residual formula after one unit-propagation layer. -/
def residualFormula : CNFFormula n :=
  unitPropagationResidual formula P.var P.polarity

/-- THEOREM 11: the unit-propagation layer instantiates P692's layered
obstruction-elimination certificate. -/
def toLayeredObstructionElimination :
    CNFLayeredObstructionElimination formula Index where
  terminalFormula := P.residualFormula
  phase := P.phase
  layerCount := 1
  initialObstructionRank := formula.length
  terminalObstructionRank := P.residualFormula.length
  rank_nonincreasing := by
    dsimp [residualFormula, unitPropagationResidual]
    simpa using
      List.length_filter_le
        (fun clause : CNFClause n =>
          !(clauseContainsLiteral clause P.var P.polarity))
        formula
  rank_strict_if_layered := by
    intro _h
    exact unitPropagationResidual_length_lt
      formula P.var P.polarity P.unit
  liftAssignment := forceAssignment P.var P.polarity
  terminal_to_initial_verify := by
    intro assignment hVerify
    constructor
    · exact unitPropagation_terminal_to_initial
        formula P.var P.polarity assignment hVerify.1
    · intro i hi
      simp [CNFSATNode.root] at hi
  initial_to_terminal_satisfiable := by
    intro h
    exact (unitPropagation_satisfiable_iff_residual
      formula P.var P.polarity P.unit).1 h

/-- THEOREM 12: unit propagation preserves satisfiability. -/
theorem satisfiable_iff_residual :
    CNFSatisfiable formula ↔ CNFSatisfiable P.residualFormula :=
  unitPropagation_satisfiable_iff_residual
    formula P.var P.polarity P.unit

end CNFUnitPropagationLayer

/-! ## Packaged certificate -/

/-- P694 certificate: unit propagation is a concrete forced layer feeding P692.
-/
structure UnitPropagationSATCertificate where
  p692_layered_root :
    LayeredObstructionEliminationSATCertificate
  unit_propagation_satisfiable_iff_residual :
    ∀ {n : Nat} {formula : CNFFormula n}
      (v : Fin n) (polarity : Bool)
      (_ : UnitLiteralInFormula formula v polarity),
      CNFSatisfiable formula ↔
        CNFSatisfiable (unitPropagationResidual formula v polarity)
  unit_propagation_residual_rank_decreases :
    ∀ {n : Nat} {formula : CNFFormula n}
      (v : Fin n) (polarity : Bool)
      (_ : UnitLiteralInFormula formula v polarity),
      (unitPropagationResidual formula v polarity).length < formula.length
  to_layered_elimination :
    ∀ {n : Nat} {formula : CNFFormula n} {Index : Type u}
      [Inhabited Index]
      (_ : CNFUnitPropagationLayer formula Index),
      CNFLayeredObstructionElimination formula Index

/-- DEFINITION 1: canonical P694 unit-propagation certificate. -/
def unitPropagationSATCertificate :
    UnitPropagationSATCertificate where
  p692_layered_root := layeredObstructionEliminationSATCertificate
  unit_propagation_satisfiable_iff_residual := by
    intro n formula v polarity hunit
    exact unitPropagation_satisfiable_iff_residual formula v polarity hunit
  unit_propagation_residual_rank_decreases := by
    intro n formula v polarity hunit
    exact unitPropagationResidual_length_lt formula v polarity hunit
  to_layered_elimination := by
    intro n formula Index _ P
    exact P.toLayeredObstructionElimination

end ComplexityProjection

/-! ## Grand-root packaging -/

namespace GrandUnification

open ComplexityProjection

set_option linter.checkUnivs false

universe u v w z

/-- P694 grand root: concrete unit propagation feeds the P692 layered
obstruction-elimination root, alongside P693's pure-literal producer. -/
structure UnitPropagationSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] where
  p693_root :
    PureLiteralExactLayerSATUnifiedRootCertificate.{u, v, w, z} E0
  unit_propagation_layer :
    UnitPropagationSATCertificate.{v}

/-- THEOREM 13: the unit-propagation unified root is inhabited. -/
def unitPropagationSATUnifiedRootCertificate
    (E0 : Type u) [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
    [CompleteSpace E0] :
    UnitPropagationSATUnifiedRootCertificate.{u, v, w, z} E0 where
  p693_root := pureLiteralExactLayerSATUnifiedRootCertificate (E0 := E0)
  unit_propagation_layer := unitPropagationSATCertificate

end GrandUnification

end SaturationMonoid

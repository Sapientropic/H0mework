/-
  Proposition 39: external-budget cost bound for finite generative queries.

  Proposition 31 proves the structural work bound for finite materialized
  Kleisli queries.  That theorem intentionally prices only the query AST work:
  set scans, selections, and bind fanout over an already-materialized domain.

  This file turns the remaining runtime costs into an explicit oracle budget.
  The theorem is simple by design: total cost is bounded by

    external/materialization budget + structural Kleisli workBound.

  This is the mathematical shape needed for agent-native databases: expensive
  source reopen, model proposal, cache fill, and materialization costs are not
  hidden inside the algebra; they are named inputs that must be supplied by a
  runtime certificate.
-/

import H0mework.Realization.QueryPlans.P31

/-! ## External oracle/materialization budget -/

/-- Runtime-owned budget knobs for costs outside the pure finite Kleisli
algebra.  `baseCost` can price source table access, source reopen, model-backed
candidate materialization, or cache-fill work for each primitive relation.
`selectCost` and `bindOverhead` are optional external charges not already
counted by Proposition 31's structural scans. -/
structure ExternalOracleBudget (Row Base : Type*) where
  baseCost : Base -> Nat
  selectCost : Nat
  bindOverhead : Nat

namespace FiniteKleisliFieldAlg

/-- External/oracle budget for a query over a finite materialized domain.  The
`bind` case budgets every possible continuation over the finite domain, matching
Proposition 31's worst-case structural bound. -/
def externalBudget {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (budget : ExternalOracleBudget Row Base) :
    FiniteKleisliFieldAlg Row Base -> Nat
  | empty => 0
  | top => 0
  | base b => budget.baseCost b
  | union p q => externalBudget domain budget p + externalBudget domain budget q
  | inter p q => externalBudget domain budget p + externalBudget domain budget q
  | diff p q => externalBudget domain budget p + externalBudget domain budget q
  | select _ q => externalBudget domain budget q + budget.selectCost
  | bind q k =>
      externalBudget domain budget q + budget.bindOverhead +
        domain.sum (fun source => externalBudget domain budget (k source))

/-- Total executable cost: runtime external budget plus the structural finite
Kleisli evaluator cost. -/
def evalWithTotalCost {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteKleisliFieldAlg Row Base) : Finset Row × Nat :=
  let evaluated := evalWithCost domain env q
  (evaluated.1, externalBudget domain budget q + evaluated.2)

/-- Total worst-case bound: external budget plus Proposition 31's structural
`workBound`. -/
def totalWorkBound {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (budget : ExternalOracleBudget Row Base)
    (q : FiniteKleisliFieldAlg Row Base) : Nat :=
  externalBudget domain budget q + workBound domain q

/-- THEOREM 1: adding external budget accounting does not change the query
result. -/
theorem evalWithTotalCost_result_eq {Row Base : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteKleisliFieldAlg Row Base) :
    (evalWithTotalCost domain env budget q).1 = evalFinset domain env q := by
  simp [evalWithTotalCost, evalWithCost_result_eq domain env q]

/-- THEOREM 2: the total executable cost is bounded by explicit external budget
plus structural Kleisli work. -/
theorem evalWithTotalCost_cost_le_totalWorkBound {Row Base : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteKleisliFieldAlg Row Base) :
    (evalWithTotalCost domain env budget q).2 ≤
      totalWorkBound domain budget q := by
  have hstruct := evalWithCost_cost_le_workBound domain env hEnv q
  simp [evalWithTotalCost, totalWorkBound]
  omega

/-- THEOREM 3: total-cost results stay inside the materialized finite domain
whenever primitive base relations do. -/
theorem evalWithTotalCost_result_subset_domain {Row Base : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteKleisliFieldAlg Row Base) :
    (evalWithTotalCost domain env budget q).1 ⊆ domain := by
  intro x hx
  have hxEval : x ∈ evalFinset domain env q := by
    simpa [evalWithTotalCost_result_eq domain env budget q] using hx
  exact evalFinset_subset_domain domain env hEnv q hxEval

end FiniteKleisliFieldAlg

/-!
  Boundary:
  - This is not an amortized cache theorem and not a model-cost theorem.  It
    states the exact accounting interface: supply an external budget, then the
    total finite-query cost is bounded by that budget plus structural work.
  - If a runtime cannot produce a finite domain or a finite external budget,
    this theorem deliberately does not apply.
-/

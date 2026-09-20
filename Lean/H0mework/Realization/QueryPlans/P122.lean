/-
  Proposition 122: amortized cost for materialized generative queries.

  Propositions 31/39/47/49 give a one-shot finite/materialized query cost
  certificate.  The agent-native database pressure is repeated recall/query:
  once a field generator relation has been materialized, warm queries should
  not silently pay model/source/cache-fill costs again.

  This file proves the algebraic amortization shape:

      cold materialization cost + n warm executions
        <= coldCost + n * structuralWorkBound(compiled query)

  and, when the cold cost is itself allocated across `n` runs,

      coldCost <= n * allowance
        ->
      total <= n * (allowance + structuralWorkBound).

  Boundary: this theorem does not prove a runtime cache is valid or fresh.  It
  states the exact certificate a runtime needs: one cold materialization cost,
  a stable finite domain/env/generator relation, and subsequent warm runs over
  the compiled finite Kleisli query.
-/

import H0mework.Realization.QueryPlans.P49

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Warm execution after materialization -/

/-- The compiled finite Kleisli query for a runtime-shaped finite plan. -/
def compiledWarmQuery
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    FiniteKleisliFieldAlg Row Base :=
  finiteRuntimePlanToKleisli runtimeRel q

/-- Result of a warm execution after domain/generator materialization. -/
def warmResult
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) : Finset Row :=
  (FiniteKleisliFieldAlg.evalWithCost domain env
    (compiledWarmQuery runtimeRel q)).1

/-- Cost of one warm execution after materialization. -/
def warmCost
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) : Nat :=
  (FiniteKleisliFieldAlg.evalWithCost domain env
    (compiledWarmQuery runtimeRel q)).2

/-- Structural bound for one warm execution. -/
def warmWorkBound
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) : Nat :=
  FiniteKleisliFieldAlg.workBound domain (compiledWarmQuery runtimeRel q)

/-- Total cost of `n` warm executions after paying one cold materialization
cost. -/
def coldThenWarmCost
    (coldCost : Nat) (n : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) : Nat :=
  coldCost + n * warmCost domain env runtimeRel q

/-! ## Denotational soundness of warm runs -/

/-- THEOREM 1: a warm compiled execution returns exactly the finite runtime
plan's denotation. -/
theorem warmResult_eq_runtime_eval
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    warmResult domain env runtimeRel q =
      evalFinset domain env runtimeRel q := by
  calc
    warmResult domain env runtimeRel q =
        FiniteKleisliFieldAlg.evalFinset domain env
          (compiledWarmQuery runtimeRel q) := by
          exact FiniteKleisliFieldAlg.evalWithCost_result_eq
            domain env (compiledWarmQuery runtimeRel q)
    _ = evalFinset domain env runtimeRel q :=
          finiteRuntimePlanToKleisli_sound domain env runtimeRel q

/-! ## Repeated warm-cost bounds -/

/-- THEOREM 2: one warm execution is bounded by the compiled structural
`workBound`. -/
theorem warmCost_le_workBound
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    warmCost domain env runtimeRel q ≤
      warmWorkBound domain runtimeRel q := by
  exact FiniteKleisliFieldAlg.evalWithCost_cost_le_workBound
    domain env hEnv (compiledWarmQuery runtimeRel q)

/-- THEOREM 3: after one cold materialization, `n` warm executions are bounded
linearly by the compiled structural work bound. -/
theorem coldThenWarmCost_le_cold_plus_n_workBound
    (coldCost n : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    coldThenWarmCost coldCost n domain env runtimeRel q ≤
      coldCost + n * warmWorkBound domain runtimeRel q := by
  unfold coldThenWarmCost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left n
      (warmCost_le_workBound domain env runtimeRel hEnv q))
    coldCost

/-- THEOREM 4: if the cold cost is allocated across `n` runs by an explicit
per-run allowance, the total repeated cost is bounded by `n` times the warm
structural bound plus that allowance. -/
theorem coldThenWarmCost_le_n_mul_allowance_plus_workBound
    (coldCost allowance n : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (hcold : coldCost ≤ n * allowance) :
    coldThenWarmCost coldCost n domain env runtimeRel q ≤
      n * (allowance + warmWorkBound domain runtimeRel q) := by
  have hwarm :
      n * warmCost domain env runtimeRel q ≤
        n * warmWorkBound domain runtimeRel q :=
    Nat.mul_le_mul_left n
      (warmCost_le_workBound domain env runtimeRel hEnv q)
  unfold coldThenWarmCost
  calc
    coldCost + n * warmCost domain env runtimeRel q
        ≤ n * allowance + n * warmWorkBound domain runtimeRel q := by
          exact Nat.add_le_add hcold hwarm
    _ = n * (allowance + warmWorkBound domain runtimeRel q) := by
          rw [Nat.mul_add]

/-!
  Summary:
  - Warm executions of a materialized finite runtime plan preserve the runtime
    denotation and are bounded by the compiled finite Kleisli `workBound`.
  - Repeated warm executions have a linear total bound after one explicit cold
    materialization cost.
  - If the cold cost can be allocated across `n` runs, the usual amortized
    shape follows without hiding model/source/cache-fill costs inside the query
    algebra.
-/


end FiniteRuntimeGenerativePlan

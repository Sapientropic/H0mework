/-
  Proposition 123: a finite generative database certificate.

  Earlier modules close separate pieces of the finite/materialized fragment:

  * P49: finite runtime plans have runtime/Kleisli/calculus completeness and a
    one-shot total-cost certificate;
  * P50: certified rewrites preserve finite denotation and do not increase
    structural `workBound`;
  * P122: repeated warm executions after one cold materialization have a
    division-free amortized cost bound.

  This file packages those pieces into one finite "Codd-style" certificate for
  the current agent-native generative query slice.  The theorem is deliberately
  scoped: it is a closed finite/materialized database slice, not a claim about
  source-schema joins, unrestricted quantification, recursion, cache freshness,
  or model/source materialization costs.
-/

import H0mework.Realization.QueryPlans.P50
import H0mework.Realization.QueryPlans.P122

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## The closed finite/materialized certificate -/

/-- A single finite/materialized certificate for one runtime generative plan:
denotational completeness, calculus expressibility, one-shot cost, warm-path
result soundness, repeated warm cost, and explicit cold-cost amortization. -/
structure FiniteGenerativeDatabaseCertificate
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (coldCost allowance n : Nat) where
  completenessCost :
    FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q
  warm_result_eq :
    warmResult domain env runtimeRel q =
      evalFinset domain env runtimeRel q
  warm_cost_le_workBound :
    warmCost domain env runtimeRel q <=
      warmWorkBound domain runtimeRel q
  cold_then_warm_le :
    coldThenWarmCost coldCost n domain env runtimeRel q <=
      coldCost + n * warmWorkBound domain runtimeRel q
  amortized_if_allocated :
    coldCost <= n * allowance ->
      coldThenWarmCost coldCost n domain env runtimeRel q <=
        n * (allowance + warmWorkBound domain runtimeRel q)

/-- THEOREM 1: every finite/materialized runtime generative plan has the closed
certificate once primitive base relations stay inside the materialized domain.
-/
def finiteGenerativeDatabaseCertificate
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (coldCost allowance n : Nat) :
    FiniteGenerativeDatabaseCertificate domain env runtimeRel budget q coldCost
      allowance n where
  completenessCost :=
    finiteRuntimeCompletenessCostCertificate domain env runtimeRel budget hEnv q
  warm_result_eq :=
    warmResult_eq_runtime_eval domain env runtimeRel q
  warm_cost_le_workBound :=
    warmCost_le_workBound domain env runtimeRel hEnv q
  cold_then_warm_le :=
    coldThenWarmCost_le_cold_plus_n_workBound
      coldCost n domain env runtimeRel hEnv q
  amortized_if_allocated := by
    intro hcold
    exact coldThenWarmCost_le_n_mul_allowance_plus_workBound
      coldCost allowance n domain env runtimeRel hEnv q hcold

namespace FiniteGenerativeDatabaseCertificate

variable {domain : Finset Row} {env : Base -> Finset Row}
variable {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {q : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
variable {coldCost allowance n : Nat}

/-- THEOREM 2: the certificate exposes finite runtime/Kleisli/calculus
completeness from P49. -/
theorem kleisli_complete
    (C : FiniteGenerativeDatabaseCertificate domain env runtimeRel budget q
      coldCost allowance n)
    (row : Row) :
    KleisliFieldAlg.eval (finiteRuntimeEnvProp env)
        C.completenessCost.kleisliAlg row <->
      row ∈ evalFinset domain env runtimeRel q :=
  C.completenessCost.kleisli_complete row

/-- THEOREM 3: the certificate exposes calculus completeness from P49. -/
theorem calc_complete
    (C : FiniteGenerativeDatabaseCertificate domain env runtimeRel budget q
      coldCost allowance n)
    (row : Row) :
    KleisliFieldCalc.eval (finiteRuntimeEnvProp env)
        C.completenessCost.calcFormula row <->
      row ∈ evalFinset domain env runtimeRel q :=
  C.completenessCost.calc_complete row

/-- THEOREM 4: the certificate exposes the repeated warm-path bound. -/
theorem repeated_warm_bound
    (C : FiniteGenerativeDatabaseCertificate domain env runtimeRel budget q
      coldCost allowance n) :
    coldThenWarmCost coldCost n domain env runtimeRel q <=
      coldCost + n * warmWorkBound domain runtimeRel q :=
  C.cold_then_warm_le

/-- THEOREM 5: the certificate exposes the allowance/amortized warm-path bound.
-/
theorem amortized_bound
    (C : FiniteGenerativeDatabaseCertificate domain env runtimeRel budget q
      coldCost allowance n)
    (hcold : coldCost <= n * allowance) :
    coldThenWarmCost coldCost n domain env runtimeRel q <=
      n * (allowance + warmWorkBound domain runtimeRel q) :=
  C.amortized_if_allocated hcold

end FiniteGenerativeDatabaseCertificate

/-! ## Cost-aware warm rewrites stay inside the same certificate boundary -/

/-- Warm result for an already optimized finite Kleisli query. -/
def optimizedWarmResult
    (domain : Finset Row) (env : Base -> Finset Row)
    (optimized : FiniteKleisliFieldAlg Row Base) : Finset Row :=
  (FiniteKleisliFieldAlg.evalWithCost domain env optimized).1

/-- Warm cost for an already optimized finite Kleisli query. -/
def optimizedWarmCost
    (domain : Finset Row) (env : Base -> Finset Row)
    (optimized : FiniteKleisliFieldAlg Row Base) : Nat :=
  (FiniteKleisliFieldAlg.evalWithCost domain env optimized).2

/-- Repeated optimized warm cost after one cold materialization. -/
def optimizedColdThenWarmCost
    (coldCost n : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (optimized : FiniteKleisliFieldAlg Row Base) : Nat :=
  coldCost + n * optimizedWarmCost domain env optimized

/-- THEOREM 6: a certified cost-aware rewrite of the compiled warm query
preserves the original runtime plan result. -/
theorem optimizedWarmResult_eq_runtime_eval_of_rewrite
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (optimized : FiniteKleisliFieldAlg Row Base)
    (R :
      FiniteKleisliFieldAlg.RewriteCertificate domain
        (compiledWarmQuery runtimeRel q) optimized) :
    optimizedWarmResult domain env optimized =
      evalFinset domain env runtimeRel q := by
  calc
    optimizedWarmResult domain env optimized =
        FiniteKleisliFieldAlg.evalFinset domain env optimized := by
          exact FiniteKleisliFieldAlg.evalWithCost_result_eq domain env optimized
    _ = FiniteKleisliFieldAlg.evalFinset domain env
          (compiledWarmQuery runtimeRel q) := by
          exact (R.preserves_eval env hEnv).symm
    _ = evalFinset domain env runtimeRel q :=
          finiteRuntimePlanToKleisli_sound domain env runtimeRel q

/-- THEOREM 7: a certified rewrite's structural bound is no larger than the
original compiled warm query's bound. -/
theorem optimized_workBound_le_warmWorkBound_of_rewrite
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (optimized : FiniteKleisliFieldAlg Row Base)
    (R :
      FiniteKleisliFieldAlg.RewriteCertificate domain
        (compiledWarmQuery runtimeRel q) optimized) :
    FiniteKleisliFieldAlg.workBound domain optimized <=
      warmWorkBound domain runtimeRel q :=
  R.nonincreasing

/-- THEOREM 8: the optimized warm execution cost is still bounded by the
original compiled warm bound. -/
theorem optimizedWarmCost_le_warmWorkBound_of_rewrite
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (optimized : FiniteKleisliFieldAlg Row Base)
    (R :
      FiniteKleisliFieldAlg.RewriteCertificate domain
        (compiledWarmQuery runtimeRel q) optimized) :
    optimizedWarmCost domain env optimized <=
      warmWorkBound domain runtimeRel q := by
  have hcost :
      optimizedWarmCost domain env optimized <=
        FiniteKleisliFieldAlg.workBound domain optimized := by
    exact FiniteKleisliFieldAlg.evalWithCost_cost_le_workBound
      domain env hEnv optimized
  exact le_trans hcost
    (optimized_workBound_le_warmWorkBound_of_rewrite
      domain runtimeRel q optimized R)

/-- THEOREM 9: repeated optimized warm executions are bounded by the original
compiled warm bound. -/
theorem optimizedColdThenWarmCost_le_cold_plus_n_warmWorkBound_of_rewrite
    (coldCost n : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (optimized : FiniteKleisliFieldAlg Row Base)
    (R :
      FiniteKleisliFieldAlg.RewriteCertificate domain
        (compiledWarmQuery runtimeRel q) optimized) :
    optimizedColdThenWarmCost coldCost n domain env optimized <=
      coldCost + n * warmWorkBound domain runtimeRel q := by
  unfold optimizedColdThenWarmCost
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left n
      (optimizedWarmCost_le_warmWorkBound_of_rewrite
        domain env runtimeRel hEnv q optimized R))
    coldCost

/-!
  Summary:
  - The finite/materialized runtime query slice now has one Lean object carrying
    runtime/Kleisli/calculus completeness, one-shot finite cost, warm repeated
    cost, and explicit cold-cost amortization.
  - Cost-aware rewrites of the compiled warm query preserve runtime denotation
    and stay under the original warm structural bound.
  - The remaining boundaries are the intentional ones: coverage,
    materialization/source/model faithfulness, cache freshness, schemas/joins,
    aggregation, recursion, and unrestricted quantification.
-/


end FiniteRuntimeGenerativePlan

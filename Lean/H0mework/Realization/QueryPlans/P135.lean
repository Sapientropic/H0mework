/-
  Proposition 135: max-bound warm workload certificate for named finite queries.

  P134 proves the finite/materialized warm-path workload bound:

      one cold materialization + Σ warmCost(qᵢ)
        <= coldCost + Σ warmWorkBound(qᵢ).

  P62/P111 already give a broader total-cost certificate with external budgets
  and a `query_count * max_per_query_bound` shape.  This file proves the
  matching hot-path statement for P134 itself: after materialization, a finite
  workload of named generated queries is bounded by

      coldCost + query_count * max_warm_workBound.

  This is the agent-facing complexity shape: once source/model/materialization
  costs have been paid and kept explicit, repeated warm generated queries are
  linear in the number of queries and the largest compiled warm query bound.
-/

import H0mework.Realization.QueryPlans.P134

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Maximum warm structural bound -/

/-- Maximum compiled warm structural bound in a finite materialized workload.
-/
def warmWorkBoundMax
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  queries.foldr
    (fun q total => Nat.max (warmWorkBound domain runtimeRel q) total) 0

/-- THEOREM 1: the sum of per-query warm bounds is bounded by
`query_count * max_warm_bound`. -/
theorem warmWorkBoundList_le_length_mul_max
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    forall queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen),
      warmWorkBoundList domain runtimeRel queries <=
        queries.length * warmWorkBoundMax domain runtimeRel queries := by
  intro queries
  induction queries with
  | nil =>
      simp [warmWorkBoundList, warmWorkBoundMax]
  | cons q rest ih =>
      let b := warmWorkBound domain runtimeRel q
      let m := warmWorkBoundMax domain runtimeRel rest
      have hhead : b <= Nat.max b m := Nat.le_max_left b m
      have htail :
          warmWorkBoundList domain runtimeRel rest <= rest.length * m := ih
      have htail' :
          warmWorkBoundList domain runtimeRel rest <=
            rest.length * Nat.max b m := by
        exact le_trans htail
          (Nat.mul_le_mul_left rest.length (Nat.le_max_right b m))
      dsimp [warmWorkBoundList, warmWorkBoundMax]
      calc
        b + warmWorkBoundList domain runtimeRel rest
            <= Nat.max b m + rest.length * Nat.max b m := by
              exact Nat.add_le_add hhead htail'
        _ = Nat.succ rest.length * Nat.max b m := by
              rw [Nat.succ_mul]
              omega

/-- THEOREM 2: the finite warm workload cost is bounded by
`query_count * max_warm_bound`. -/
theorem warmCostList_le_length_mul_max
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    warmCostList domain env runtimeRel queries <=
      queries.length * warmWorkBoundMax domain runtimeRel queries := by
  exact le_trans
    (warmCostList_le_workBoundList domain env runtimeRel hEnv queries)
    (warmWorkBoundList_le_length_mul_max domain runtimeRel queries)

/-- THEOREM 3: after one cold materialization, warm workload cost is bounded by
cold cost plus `query_count * max_warm_bound`. -/
theorem coldThenWarmBatchCost_le_cold_plus_length_mul_max
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    coldThenWarmBatchCost coldCost domain env runtimeRel queries <=
      coldCost + queries.length *
        warmWorkBoundMax domain runtimeRel queries := by
  unfold coldThenWarmBatchCost
  exact Nat.add_le_add_left
    (warmCostList_le_length_mul_max domain env runtimeRel hEnv queries)
    coldCost

/-- THEOREM 4: if the cold materialization cost is allocated across the
workload, the whole batch is bounded by
`query_count * (allowance + max_warm_bound)`. -/
theorem coldThenWarmBatchCost_le_length_mul_allowance_plus_max
    (coldCost allowance : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen))
    (hcold : coldCost <= queries.length * allowance) :
    coldThenWarmBatchCost coldCost domain env runtimeRel queries <=
      queries.length *
        (allowance + warmWorkBoundMax domain runtimeRel queries) := by
  unfold coldThenWarmBatchCost
  have hwarm :
      warmCostList domain env runtimeRel queries <=
        queries.length * warmWorkBoundMax domain runtimeRel queries :=
    warmCostList_le_length_mul_max domain env runtimeRel hEnv queries
  calc
    coldCost + warmCostList domain env runtimeRel queries
        <= queries.length * allowance +
            queries.length * warmWorkBoundMax domain runtimeRel queries := by
          exact Nat.add_le_add hcold hwarm
    _ = queries.length *
          (allowance + warmWorkBoundMax domain runtimeRel queries) := by
          rw [Nat.mul_add]

end FiniteRuntimeGenerativePlan

/-! ## Named workload max-bound certificate -/

/-- P134 workload certificate plus the hotter `length * max_warm_bound` shape.
-/
structure NamedFiniteGenerativeWorkloadMaxCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (queries :
      List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator))
    (coldCost allowance : Nat) where
  workload :
    NamedFiniteGenerativeWorkloadCertificate coverage domain env runtimeRel
      budget queries coldCost allowance
  warm_cost_le_length_mul_max :
    FiniteRuntimeGenerativePlan.warmCostList domain env runtimeRel queries <=
      queries.length *
        FiniteRuntimeGenerativePlan.warmWorkBoundMax domain runtimeRel queries
  cold_then_warm_le_length_mul_max :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      coldCost + queries.length *
        FiniteRuntimeGenerativePlan.warmWorkBoundMax domain runtimeRel queries
  amortized_max_if_allocated :
    coldCost <= queries.length * allowance ->
      FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
          coldCost domain env runtimeRel queries <=
        queries.length *
          (allowance +
            FiniteRuntimeGenerativePlan.warmWorkBoundMax domain runtimeRel
              queries)

/-- THEOREM 5: the named finite/materialized workload certificate can always
be strengthened to the hot-path `query_count * max_warm_bound` certificate. -/
theorem namedFiniteGenerativeWorkloadMaxCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (bridge : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (queries :
      List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator))
    (coldCost allowance : Nat) :
    NamedFiniteGenerativeWorkloadMaxCertificate coverage domain env runtimeRel
      budget queries coldCost allowance where
  workload :=
    namedFiniteGenerativeWorkloadCertificate coverage domain env runtimeRel
      budget hEnv bridge queries coldCost allowance
  warm_cost_le_length_mul_max :=
    FiniteRuntimeGenerativePlan.warmCostList_le_length_mul_max
      domain env runtimeRel hEnv queries
  cold_then_warm_le_length_mul_max :=
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost_le_cold_plus_length_mul_max
      coldCost domain env runtimeRel hEnv queries
  amortized_max_if_allocated := by
    intro hcold
    exact
      FiniteRuntimeGenerativePlan.coldThenWarmBatchCost_le_length_mul_allowance_plus_max
        coldCost allowance domain env runtimeRel hEnv queries hcold

namespace NamedFiniteGenerativeWorkloadMaxCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {queries :
  List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)}
variable {coldCost allowance : Nat}

/-- THEOREM 6: every query in the max-bound workload certificate still has the
P134 executable/named denotation bridge. -/
theorem query_eval_iff_named
    (C : NamedFiniteGenerativeWorkloadMaxCertificate coverage domain env
      runtimeRel budget queries coldCost allowance)
    {q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
    (hq : q ∈ queries) (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row :=
  C.workload.query_eval_iff_named hq row

/-- THEOREM 7: expose the hot-path max-bound. -/
theorem workload_cold_then_warm_max_bound
    (C : NamedFiniteGenerativeWorkloadMaxCertificate coverage domain env
      runtimeRel budget queries coldCost allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      coldCost + queries.length *
        FiniteRuntimeGenerativePlan.warmWorkBoundMax domain runtimeRel queries :=
  C.cold_then_warm_le_length_mul_max

/-- THEOREM 8: expose the allocated hot-path max-bound. -/
theorem workload_amortized_max_bound
    (C : NamedFiniteGenerativeWorkloadMaxCertificate coverage domain env
      runtimeRel budget queries coldCost allowance)
    (hcold : coldCost <= queries.length * allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      queries.length *
        (allowance +
          FiniteRuntimeGenerativePlan.warmWorkBoundMax domain runtimeRel
            queries) :=
  C.amortized_max_if_allocated hcold

end NamedFiniteGenerativeWorkloadMaxCertificate

/-!
  Summary:
  - P135 does not replace P62/P111's broader total-cost story.  It specializes
    the max-bound shape to P134's already-materialized warm path.
  - The named workload still carries executable/named denotational agreement
    for every query, while the hot-path cost has the readable form
    `cold + query_count * max_warm_bound`.
-/

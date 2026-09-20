/-
  Proposition 134: finite workload completeness and batch warm-cost bounds.

  P129/P132 close the denotational seam for one finite materialized runtime
  plan: executable Bool membership is exactly the named Prop-valued runtime
  denotation once the pointwise runtime relation bridge is supplied.

  P122/P123 close the repeated-warm-cost seam for one query.  Agent-native
  memory consumers, however, usually issue a finite workload of different
  generated queries against the same materialized slice.  This file proves the
  algebraic shape needed for that workload:

      one cold materialization + Σ warmCost(qᵢ)
        <= coldCost + Σ structuralWorkBound(qᵢ)

  and packages that with the named/executable denotation bridge for every query
  in the workload.

  Boundary: this is still the finite/materialized slice.  It does not prove
  source/model materialization faithfulness, cache freshness, schemas/joins,
  aggregation, recursion, unrestricted quantification, or empirical optimizer
  behavior.
-/

import H0mework.Realization.QueryPlans.P132

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Finite warm workloads -/

/-- Total warm execution cost for a finite list of generated queries over one
materialized domain. -/
def warmCostList
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  queries.foldr
    (fun q total => warmCost domain env runtimeRel q + total) 0

/-- Sum of structural warm-work bounds for a finite query workload. -/
def warmWorkBoundList
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  queries.foldr
    (fun q total => warmWorkBound domain runtimeRel q + total) 0

/-- One cold materialization followed by a finite workload of warm generated
queries. -/
def coldThenWarmBatchCost
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  coldCost + warmCostList domain env runtimeRel queries

/-- THEOREM 1: a finite warm workload is bounded by the sum of the compiled
structural work bounds for its queries. -/
theorem warmCostList_le_workBoundList
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    warmCostList domain env runtimeRel queries <=
      warmWorkBoundList domain runtimeRel queries := by
  induction queries with
  | nil =>
      simp [warmCostList, warmWorkBoundList]
  | cons q qs ih =>
      simp [warmCostList, warmWorkBoundList]
      exact Nat.add_le_add
        (warmCost_le_workBound domain env runtimeRel hEnv q) ih

/-- THEOREM 2: one cold materialization plus a finite warm workload is bounded
by cold cost plus the workload's structural bound sum. -/
theorem coldThenWarmBatchCost_le_cold_plus_workBoundList
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    coldThenWarmBatchCost coldCost domain env runtimeRel queries <=
      coldCost + warmWorkBoundList domain runtimeRel queries := by
  unfold coldThenWarmBatchCost
  exact Nat.add_le_add_left
    (warmCostList_le_workBoundList domain env runtimeRel hEnv queries)
    coldCost

/-- THEOREM 3: if the one-time cold cost is allocated across the workload by a
per-query allowance, the total workload cost is bounded by that allocation plus
the structural warm-work sum. -/
theorem coldThenWarmBatchCost_le_length_allowance_plus_workBoundList
    (coldCost allowance : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (queries : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen))
    (hcold : coldCost <= queries.length * allowance) :
    coldThenWarmBatchCost coldCost domain env runtimeRel queries <=
      queries.length * allowance + warmWorkBoundList domain runtimeRel queries := by
  unfold coldThenWarmBatchCost
  exact Nat.add_le_add hcold
    (warmCostList_le_workBoundList domain env runtimeRel hEnv queries)

end FiniteRuntimeGenerativePlan

/-! ## Named finite workload certificate -/

/-- A Codd-style finite/materialized workload certificate for the named
AIppocampus generator basis.

It says every query in the workload has executable/named denotational
agreement, and the whole workload has a structural warm-cost bound after one
cold materialization. -/
structure NamedFiniteGenerativeWorkloadCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (queries :
      List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator))
    (coldCost allowance : Nat) where
  relationBridge :
    NamedFiniteRuntimeRelationBridge coverage domain runtimeRel
  finite_eval_iff_named :
    forall q, q ∈ queries ->
      forall row,
        row ∈ FiniteRuntimeGenerativePlan.evalFinset
            domain env runtimeRel q <->
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
            coverage.runtimeRel
            (finiteRuntimePlanToRuntimePlan domain q) row
  warm_cost_le :
    FiniteRuntimeGenerativePlan.warmCostList domain env runtimeRel queries <=
      FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries
  cold_then_warm_le :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      coldCost +
        FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries
  amortized_if_allocated :
    coldCost <= queries.length * allowance ->
      FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
          coldCost domain env runtimeRel queries <=
        queries.length * allowance +
          FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries

/-- THEOREM 4: coverage + finite materialization + the Bool/Prop transition
bridge give a workload-level named finite generative database certificate. -/
theorem namedFiniteGenerativeWorkloadCertificate
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
    NamedFiniteGenerativeWorkloadCertificate coverage domain env runtimeRel
      budget queries coldCost allowance := by
  refine
    { relationBridge := bridge
      finite_eval_iff_named := ?_
      warm_cost_le :=
        FiniteRuntimeGenerativePlan.warmCostList_le_workBoundList
          domain env runtimeRel hEnv queries
      cold_then_warm_le :=
        FiniteRuntimeGenerativePlan.coldThenWarmBatchCost_le_cold_plus_workBoundList
          coldCost domain env runtimeRel hEnv queries
      amortized_if_allocated := ?_ }
  ·
    intro q _hq row
    let C :=
      namedFiniteGenerativeDatabaseCertificate
        coverage domain env runtimeRel budget hEnv bridge q coldCost allowance
        queries.length
    exact C.finite_eval_iff_named_runtime_eval row
  ·
    intro hcold
    exact
      FiniteRuntimeGenerativePlan.coldThenWarmBatchCost_le_length_allowance_plus_workBoundList
        coldCost allowance domain env runtimeRel hEnv queries hcold

namespace NamedFiniteGenerativeWorkloadCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {queries :
  List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)}
variable {coldCost allowance : Nat}

/-- THEOREM 5: executable finite membership is sound and complete for the
named runtime denotation for every workload query. -/
theorem query_eval_iff_named
    (C : NamedFiniteGenerativeWorkloadCertificate coverage domain env
      runtimeRel budget queries coldCost allowance)
    {q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
    (hq : q ∈ queries) (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row :=
  C.finite_eval_iff_named q hq row

/-- THEOREM 6: the workload certificate exposes the batch structural warm-cost
bound. -/
theorem workload_warm_bound
    (C : NamedFiniteGenerativeWorkloadCertificate coverage domain env
      runtimeRel budget queries coldCost allowance) :
    FiniteRuntimeGenerativePlan.warmCostList domain env runtimeRel queries <=
      FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries :=
  C.warm_cost_le

/-- THEOREM 7: the workload certificate exposes the cold-plus-warm structural
bound. -/
theorem workload_cold_then_warm_bound
    (C : NamedFiniteGenerativeWorkloadCertificate coverage domain env
      runtimeRel budget queries coldCost allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      coldCost +
        FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries :=
  C.cold_then_warm_le

/-- THEOREM 8: the workload certificate exposes the per-query cold-allocation
bound. -/
theorem workload_amortized_bound
    (C : NamedFiniteGenerativeWorkloadCertificate coverage domain env
      runtimeRel budget queries coldCost allowance)
    (hcold : coldCost <= queries.length * allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmBatchCost
        coldCost domain env runtimeRel queries <=
      queries.length * allowance +
        FiniteRuntimeGenerativePlan.warmWorkBoundList domain runtimeRel queries :=
  C.amortized_if_allocated hcold

end NamedFiniteGenerativeWorkloadCertificate

/-!
  Summary:
  - A finite workload of generated queries over one materialized slice has a
    total warm cost bounded by the sum of structural warm-work bounds.
  - One cold materialization cost stays explicit; if allocated across the
    workload, the batch bound reflects that allocation rather than hiding it.
  - The named workload certificate carries executable/named denotational
    agreement for every query in the list plus the batch complexity bound.
-/

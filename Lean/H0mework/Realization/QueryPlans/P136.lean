/-
  Proposition 136: workload-level cost-aware rewrites for named finite queries.

  P50 gives local cost-aware rewrite certificates for finite Kleisli queries.
  P123 uses such a certificate for one compiled warm query.  P134/P135 then
  give workload-level warm-path bounds for unoptimized finite runtime plans.

  This file closes the next Codd-style optimization seam: a finite workload may
  rewrite every compiled warm query to an optimized finite Kleisli query.  If
  each rewrite preserves denotation and does not increase structural work, then

    * every optimized query still denotes the named Prop-valued runtime plan it
      came from;
    * the whole optimized workload cost is bounded by the original workload's
      structural sum and max-bound;
    * cold materialization remains explicit.

  Boundary: this proves correctness of a supplied workload rewrite certificate.
  It is not a complete optimizer, nor a proof that production chose the best
  rewrite sequence.
-/

import H0mework.Realization.QueryPlans.P135

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Workload rewrite items -/

/-- One optimized warm-path query in a workload: the original finite runtime
plan, the optimized finite Kleisli query, and a rewrite certificate from the
compiled warm query to that optimized query. -/
structure WarmRewriteItem
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) where
  query : FiniteRuntimeGenerativePlan Row Base RuntimeGen
  optimized : FiniteKleisliFieldAlg Row Base
  rewrite :
    FiniteKleisliFieldAlg.RewriteCertificate domain
      (compiledWarmQuery runtimeRel query) optimized

/-- Total warm cost for an optimized finite workload. -/
def optimizedWarmCostList
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total => optimizedWarmCost domain env item.optimized + total) 0

/-- Sum of the original compiled warm bounds for an optimized workload. -/
def originalWarmWorkBoundList
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total => warmWorkBound domain runtimeRel item.query + total) 0

/-- Maximum original compiled warm bound for an optimized workload. -/
def originalWarmWorkBoundMax
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total =>
      Nat.max (warmWorkBound domain runtimeRel item.query) total) 0

/-- One cold materialization plus the optimized warm workload. -/
def optimizedColdThenWarmRewriteBatchCost
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  coldCost + optimizedWarmCostList domain env items

/-! ## Denotation preservation for optimized workload items -/

/-- THEOREM 1: a workload rewrite item preserves the original finite runtime
result set. -/
theorem optimizedWarmResult_eq_evalFinset
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (item : WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel) :
    optimizedWarmResult domain env item.optimized =
      evalFinset domain env runtimeRel item.query :=
  optimizedWarmResult_eq_runtime_eval_of_rewrite
    domain env runtimeRel hEnv item.query item.optimized item.rewrite

/-! ## Optimized workload cost bounds -/

/-- THEOREM 2: an optimized workload's warm cost is bounded by the sum of the
original compiled warm bounds. -/
theorem optimizedWarmCostList_le_originalWarmWorkBoundList
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    optimizedWarmCostList domain env items <=
      originalWarmWorkBoundList domain items := by
  induction items with
  | nil =>
      simp [optimizedWarmCostList, originalWarmWorkBoundList]
  | cons item rest ih =>
      simp [optimizedWarmCostList, originalWarmWorkBoundList]
      exact Nat.add_le_add
        (optimizedWarmCost_le_warmWorkBound_of_rewrite
          domain env runtimeRel hEnv item.query item.optimized item.rewrite)
        ih

/-- THEOREM 3: the original bound sum is bounded by
`query_count * max_original_warm_bound`. -/
theorem originalWarmWorkBoundList_le_length_mul_max
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool} :
    forall items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel),
      originalWarmWorkBoundList domain items <=
        items.length * originalWarmWorkBoundMax domain items := by
  intro items
  induction items with
  | nil =>
      simp [originalWarmWorkBoundList, originalWarmWorkBoundMax]
  | cons item rest ih =>
      let b := warmWorkBound domain runtimeRel item.query
      let m := originalWarmWorkBoundMax domain rest
      have hhead : b <= Nat.max b m := Nat.le_max_left b m
      have htail :
          originalWarmWorkBoundList domain rest <= rest.length * m := ih
      have htail' :
          originalWarmWorkBoundList domain rest <=
            rest.length * Nat.max b m := by
        exact le_trans htail
          (Nat.mul_le_mul_left rest.length (Nat.le_max_right b m))
      dsimp [originalWarmWorkBoundList, originalWarmWorkBoundMax]
      calc
        b + originalWarmWorkBoundList domain rest
            <= Nat.max b m + rest.length * Nat.max b m := by
              exact Nat.add_le_add hhead htail'
        _ = Nat.succ rest.length * Nat.max b m := by
              rw [Nat.succ_mul]
              omega

/-- THEOREM 4: an optimized warm workload is bounded by
`query_count * max_original_warm_bound`. -/
theorem optimizedWarmCostList_le_length_mul_originalMax
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    optimizedWarmCostList domain env items <=
      items.length * originalWarmWorkBoundMax domain items := by
  exact le_trans
    (optimizedWarmCostList_le_originalWarmWorkBoundList
      domain env runtimeRel hEnv items)
    (originalWarmWorkBoundList_le_length_mul_max domain items)

/-- THEOREM 5: after one cold materialization, the optimized workload is
bounded by cold cost plus `query_count * max_original_warm_bound`. -/
theorem optimizedColdThenWarmRewriteBatchCost_le_cold_plus_length_mul_originalMax
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    optimizedColdThenWarmRewriteBatchCost coldCost domain env items <=
      coldCost + items.length * originalWarmWorkBoundMax domain items := by
  unfold optimizedColdThenWarmRewriteBatchCost
  exact Nat.add_le_add_left
    (optimizedWarmCostList_le_length_mul_originalMax
      domain env runtimeRel hEnv items)
    coldCost

/-- THEOREM 6: if the cold cost is allocated across the optimized workload,
the batch is bounded by `query_count * (allowance + max_original_warm_bound)`.
-/
theorem optimizedColdThenWarmRewriteBatchCost_le_length_mul_allowance_plus_originalMax
    (coldCost allowance : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel))
    (hcold : coldCost <= items.length * allowance) :
    optimizedColdThenWarmRewriteBatchCost coldCost domain env items <=
      items.length * (allowance + originalWarmWorkBoundMax domain items) := by
  unfold optimizedColdThenWarmRewriteBatchCost
  have hwarm :
      optimizedWarmCostList domain env items <=
        items.length * originalWarmWorkBoundMax domain items :=
    optimizedWarmCostList_le_length_mul_originalMax
      domain env runtimeRel hEnv items
  calc
    coldCost + optimizedWarmCostList domain env items
        <= items.length * allowance +
            items.length * originalWarmWorkBoundMax domain items := by
          exact Nat.add_le_add hcold hwarm
    _ = items.length *
          (allowance + originalWarmWorkBoundMax domain items) := by
          rw [Nat.mul_add]

end FiniteRuntimeGenerativePlan

/-! ## Named optimized workload certificate -/

/-- A named finite workload whose compiled warm queries have each been
optimized by a cost-aware rewrite certificate. -/
structure NamedFiniteOptimizedWorkloadCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (items :
      List (FiniteRuntimeGenerativePlan.WarmRewriteItem (Row := Row)
        (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel))
    (coldCost allowance : Nat) where
  optimized_eval_iff_named :
    forall item, item ∈ items ->
      forall row,
        row ∈ FiniteRuntimeGenerativePlan.optimizedWarmResult
            domain env item.optimized <->
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
            coverage.runtimeRel
            (finiteRuntimePlanToRuntimePlan domain item.query) row
  optimized_warm_cost_le_original_sum :
    FiniteRuntimeGenerativePlan.optimizedWarmCostList domain env items <=
      FiniteRuntimeGenerativePlan.originalWarmWorkBoundList domain items
  optimized_cold_then_warm_le_max :
    FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost
        coldCost domain env items <=
      coldCost + items.length *
        FiniteRuntimeGenerativePlan.originalWarmWorkBoundMax domain items
  optimized_amortized_if_allocated :
    coldCost <= items.length * allowance ->
      FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost
          coldCost domain env items <=
        items.length *
          (allowance +
            FiniteRuntimeGenerativePlan.originalWarmWorkBoundMax domain items)

/-- THEOREM 7: a workload of certified cost-aware rewrites preserves named
denotation query-by-query and inherits the original workload's max-bound. -/
theorem namedFiniteOptimizedWorkloadCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (bridge : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (items :
      List (FiniteRuntimeGenerativePlan.WarmRewriteItem (Row := Row)
        (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel))
    (coldCost allowance : Nat) :
    NamedFiniteOptimizedWorkloadCertificate coverage domain env runtimeRel
      items coldCost allowance where
  optimized_eval_iff_named := by
    intro item _hitem row
    have hopt :
        FiniteRuntimeGenerativePlan.optimizedWarmResult domain env
            item.optimized =
          FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
            item.query :=
      FiniteRuntimeGenerativePlan.optimizedWarmResult_eq_evalFinset
        domain env runtimeRel hEnv item
    calc
      row ∈ FiniteRuntimeGenerativePlan.optimizedWarmResult domain env
          item.optimized
          <->
        row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
          item.query := by
            rw [hopt]
      _ <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel
          (finiteRuntimePlanToRuntimePlan domain item.query) row := by
            exact
              (finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel
                item.query row).trans
              (bridge.runtimePlan_eval_iff_named item.query row)
  optimized_warm_cost_le_original_sum :=
    FiniteRuntimeGenerativePlan.optimizedWarmCostList_le_originalWarmWorkBoundList
      domain env runtimeRel hEnv items
  optimized_cold_then_warm_le_max :=
    FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost_le_cold_plus_length_mul_originalMax
      coldCost domain env runtimeRel hEnv items
  optimized_amortized_if_allocated := by
    intro hcold
    exact
      FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost_le_length_mul_allowance_plus_originalMax
        coldCost allowance domain env runtimeRel hEnv items hcold

namespace NamedFiniteOptimizedWorkloadCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {items :
  List (FiniteRuntimeGenerativePlan.WarmRewriteItem (Row := Row)
    (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
    domain runtimeRel)}
variable {coldCost allowance : Nat}

/-- THEOREM 8: expose denotational correctness for an optimized workload item.
-/
theorem query_eval_iff_named
    (C : NamedFiniteOptimizedWorkloadCertificate coverage domain env runtimeRel
      items coldCost allowance)
    {item : FiniteRuntimeGenerativePlan.WarmRewriteItem (Row := Row)
      (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
      domain runtimeRel}
    (hitem : item ∈ items) (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.optimizedWarmResult
        domain env item.optimized <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain item.query) row :=
  C.optimized_eval_iff_named item hitem row

/-- THEOREM 9: expose the optimized workload max-bound. -/
theorem optimized_workload_max_bound
    (C : NamedFiniteOptimizedWorkloadCertificate coverage domain env runtimeRel
      items coldCost allowance) :
    FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost
        coldCost domain env items <=
      coldCost + items.length *
        FiniteRuntimeGenerativePlan.originalWarmWorkBoundMax domain items :=
  C.optimized_cold_then_warm_le_max

/-- THEOREM 10: expose the allocated optimized workload max-bound. -/
theorem optimized_workload_amortized_bound
    (C : NamedFiniteOptimizedWorkloadCertificate coverage domain env runtimeRel
      items coldCost allowance)
    (hcold : coldCost <= items.length * allowance) :
    FiniteRuntimeGenerativePlan.optimizedColdThenWarmRewriteBatchCost
        coldCost domain env items <=
      items.length *
        (allowance +
          FiniteRuntimeGenerativePlan.originalWarmWorkBoundMax domain items) :=
  C.optimized_amortized_if_allocated hcold

end NamedFiniteOptimizedWorkloadCertificate

/-!
  Summary:
  - P136 lifts cost-aware finite Kleisli rewrites from one compiled warm query
    to an entire named finite workload.
  - The optimized workload preserves named denotation for every item and keeps
    the P135 hot-path complexity shape, measured against the original compiled
    warm bounds.
-/

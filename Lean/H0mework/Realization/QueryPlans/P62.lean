/-
  Proposition 62: finite workload and division-free amortized cost bounds.

  Proposition 21 gives the exact cost of one materialized field-interference
  cross-product.  Propositions 31/39/47/49 give single-query finite
  generative cost certificates.  This file lifts those one-shot statements to
  finite workloads:

    * a batch of materialized interference covers has exact total pair-check
      cost equal to the sum of the per-cover products;
    * a batch of finite runtime generative plans has total executable cost
      bounded by the sum of the compiled total-work bounds;
    * the same batch is bounded by `query_count * max_per_query_bound`;
    * adding one shared materialization/cache-fill cost yields a
      division-free amortized certificate:

          total <= shared + query_count * max_per_query_bound.

  Boundary: this is still a finite/materialized workload theorem.  It does not
  prove that the runtime can cheaply produce the materialized domain, nor does
  it derive a cache replacement policy or a probabilistic amortized model.
-/

import H0mework.Realization.QueryPlans.P49
import H0mework.Realization.QuerySupport.P61

/-! ## Batch field-interference scans -/

/-- Concatenate the complete pairwise interference scans for a finite list of
materialized local-cover pairs. -/
def crossInterferenceWorkloadPairs {α β : Type*} :
    List (List α × List β) -> List (α × β)
  | [] => []
  | cover :: rest =>
      crossInterferencePairs cover.1 cover.2 ++
        crossInterferenceWorkloadPairs rest

/-- The exact numeric batch bound for materialized pairwise interference. -/
def crossInterferenceWorkloadBound {α β : Type*} :
    List (List α × List β) -> Nat
  | [] => 0
  | cover :: rest =>
      cover.1.length * cover.2.length + crossInterferenceWorkloadBound rest

/-- THEOREM 1: a workload of materialized local-cover interference checks has
exact cost equal to the sum of per-cover cross products. -/
theorem crossInterferenceWorkloadPairs_length {α β : Type*}
    (covers : List (List α × List β)) :
    (crossInterferenceWorkloadPairs covers).length =
      crossInterferenceWorkloadBound covers := by
  induction covers with
  | nil =>
      rfl
  | cons cover rest ih =>
      simp [crossInterferenceWorkloadPairs, crossInterferenceWorkloadBound,
        crossInterferencePairs_length, ih]

/-! ## Finite runtime generative workloads -/

/-- Total executable cost for a list of finite runtime generative plans after
compiling every plan to the finite Kleisli algebra. -/
def finiteRuntimeWorkloadTotalCost
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base) :
    List (FiniteRuntimeGenerativePlan Row Base RuntimeGen) -> Nat
  | [] => 0
  | q :: rest =>
      (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
        (finiteRuntimePlanToKleisli runtimeRel q)).2 +
          finiteRuntimeWorkloadTotalCost domain env runtimeRel budget rest

/-- Sum of the compiled total-work bounds for a finite runtime workload. -/
def finiteRuntimeWorkloadTotalBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base) :
    List (FiniteRuntimeGenerativePlan Row Base RuntimeGen) -> Nat
  | [] => 0
  | q :: rest =>
      FiniteKleisliFieldAlg.totalWorkBound domain budget
        (finiteRuntimePlanToKleisli runtimeRel q) +
          finiteRuntimeWorkloadTotalBound domain runtimeRel budget rest

/-- Maximum compiled per-query total-work bound in a finite runtime workload. -/
def finiteRuntimeWorkloadMaxBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base) :
    List (FiniteRuntimeGenerativePlan Row Base RuntimeGen) -> Nat
  | [] => 0
  | q :: rest =>
      Nat.max
        (FiniteKleisliFieldAlg.totalWorkBound domain budget
          (finiteRuntimePlanToKleisli runtimeRel q))
        (finiteRuntimeWorkloadMaxBound domain runtimeRel budget rest)

/-- THEOREM 2: finite runtime workload executable cost is bounded by the sum
of per-query total-work bounds. -/
theorem finiteRuntimeWorkloadTotalCost_le_totalBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain) :
    forall qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen),
      finiteRuntimeWorkloadTotalCost domain env runtimeRel budget qs ≤
        finiteRuntimeWorkloadTotalBound domain runtimeRel budget qs := by
  intro qs
  induction qs with
  | nil =>
      simp [finiteRuntimeWorkloadTotalCost, finiteRuntimeWorkloadTotalBound]
  | cons q rest ih =>
      have hq :
          (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
            (finiteRuntimePlanToKleisli runtimeRel q)).2 ≤
          FiniteKleisliFieldAlg.totalWorkBound domain budget
            (finiteRuntimePlanToKleisli runtimeRel q) :=
        FiniteKleisliFieldAlg.evalWithTotalCost_cost_le_totalWorkBound
          domain env budget hEnv (finiteRuntimePlanToKleisli runtimeRel q)
      simp [finiteRuntimeWorkloadTotalCost, finiteRuntimeWorkloadTotalBound]
      omega

/-- THEOREM 3: the sum of per-query bounds is bounded by
`query_count * max_per_query_bound`.  This is the division-free amortized
shape: after paying any shared cost separately, each query is bounded by the
maximum compiled per-query bound. -/
theorem finiteRuntimeWorkloadTotalBound_le_length_mul_maxBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base) :
    forall qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen),
      finiteRuntimeWorkloadTotalBound domain runtimeRel budget qs ≤
        qs.length * finiteRuntimeWorkloadMaxBound domain runtimeRel budget qs := by
  intro qs
  induction qs with
  | nil =>
      simp [finiteRuntimeWorkloadTotalBound, finiteRuntimeWorkloadMaxBound]
  | cons q rest ih =>
      let b :=
        FiniteKleisliFieldAlg.totalWorkBound domain budget
          (finiteRuntimePlanToKleisli runtimeRel q)
      let m := finiteRuntimeWorkloadMaxBound domain runtimeRel budget rest
      have hhead : b ≤ Nat.max b m := Nat.le_max_left b m
      have htail :
          finiteRuntimeWorkloadTotalBound domain runtimeRel budget rest ≤
            rest.length * m := ih
      have htail' :
          finiteRuntimeWorkloadTotalBound domain runtimeRel budget rest ≤
            rest.length * Nat.max b m := by
        exact le_trans htail
          (Nat.mul_le_mul_left rest.length (Nat.le_max_right b m))
      dsimp [finiteRuntimeWorkloadTotalBound, finiteRuntimeWorkloadMaxBound]
      calc
        b + finiteRuntimeWorkloadTotalBound domain runtimeRel budget rest
            ≤ Nat.max b m + rest.length * Nat.max b m := by
              exact Nat.add_le_add hhead htail'
        _ = Nat.succ rest.length * Nat.max b m := by
              rw [Nat.succ_mul]
              omega

/-- THEOREM 4: executable workload cost is bounded by
`query_count * max_per_query_bound`. -/
theorem finiteRuntimeWorkloadTotalCost_le_length_mul_maxBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    finiteRuntimeWorkloadTotalCost domain env runtimeRel budget qs ≤
      qs.length * finiteRuntimeWorkloadMaxBound domain runtimeRel budget qs := by
  exact le_trans
    (finiteRuntimeWorkloadTotalCost_le_totalBound
      domain env runtimeRel budget hEnv qs)
    (finiteRuntimeWorkloadTotalBound_le_length_mul_maxBound
      domain runtimeRel budget qs)

/-! ## Shared materialization / cache-fill budget -/

/-- Total workload cost after paying a shared one-time materialization/cache-fill
cost. -/
def finiteRuntimeSharedWorkloadTotalCost
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (sharedCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  sharedCost + finiteRuntimeWorkloadTotalCost domain env runtimeRel budget qs

/-- Division-free amortized workload bound:
one shared cost plus `query_count * max_per_query_bound`. -/
def finiteRuntimeSharedWorkloadAmortizedBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (sharedCost : Nat)
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) : Nat :=
  sharedCost + qs.length *
    finiteRuntimeWorkloadMaxBound domain runtimeRel budget qs

/-- THEOREM 5: after one shared materialization/cache-fill charge, the finite
runtime workload is bounded by the division-free amortized expression. -/
theorem finiteRuntimeSharedWorkloadTotalCost_le_amortizedBound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (sharedCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    finiteRuntimeSharedWorkloadTotalCost sharedCost domain env runtimeRel budget qs ≤
      finiteRuntimeSharedWorkloadAmortizedBound sharedCost domain runtimeRel budget qs := by
  have h :=
    finiteRuntimeWorkloadTotalCost_le_length_mul_maxBound
      domain env runtimeRel budget hEnv qs
  simp [finiteRuntimeSharedWorkloadTotalCost,
    finiteRuntimeSharedWorkloadAmortizedBound]
  omega

/-- A packaged certificate for a finite runtime generative workload. -/
structure FiniteRuntimeWorkloadCostCertificate
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (sharedCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) where
  totalCost_le_totalBound :
    finiteRuntimeWorkloadTotalCost domain env runtimeRel budget qs ≤
      finiteRuntimeWorkloadTotalBound domain runtimeRel budget qs
  totalBound_le_length_mul_max :
    finiteRuntimeWorkloadTotalBound domain runtimeRel budget qs ≤
      qs.length * finiteRuntimeWorkloadMaxBound domain runtimeRel budget qs
  totalCost_le_length_mul_max :
    finiteRuntimeWorkloadTotalCost domain env runtimeRel budget qs ≤
      qs.length * finiteRuntimeWorkloadMaxBound domain runtimeRel budget qs
  sharedCost_le_amortizedBound :
    finiteRuntimeSharedWorkloadTotalCost sharedCost domain env runtimeRel budget qs ≤
      finiteRuntimeSharedWorkloadAmortizedBound sharedCost domain runtimeRel budget qs

/-- THEOREM 6: every finite runtime workload has a cost certificate once the
environment is materialized inside the finite domain. -/
theorem finiteRuntimeWorkloadCostCertificate
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (sharedCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (qs : List (FiniteRuntimeGenerativePlan Row Base RuntimeGen)) :
    FiniteRuntimeWorkloadCostCertificate sharedCost domain env runtimeRel budget qs where
  totalCost_le_totalBound :=
    finiteRuntimeWorkloadTotalCost_le_totalBound
      domain env runtimeRel budget hEnv qs
  totalBound_le_length_mul_max :=
    finiteRuntimeWorkloadTotalBound_le_length_mul_maxBound
      domain runtimeRel budget qs
  totalCost_le_length_mul_max :=
    finiteRuntimeWorkloadTotalCost_le_length_mul_maxBound
      domain env runtimeRel budget hEnv qs
  sharedCost_le_amortizedBound :=
    finiteRuntimeSharedWorkloadTotalCost_le_amortizedBound
      sharedCost domain env runtimeRel budget hEnv qs

/-!
  Summary:
  - Materialized field-interference batches have exact pair-check cost.
  - Finite runtime generative query workloads inherit the single-query
    external-budget + structural-work bounds query-by-query.
  - A finite workload has a division-free amortized certificate:
    `total <= shared + query_count * max_per_query_bound`.

  Remaining boundary:
  - No cache replacement policy is proved.
  - No probabilistic or average-case model is assumed.
  - Source reopen/model proposal/materialized-domain construction still enters
    only through explicit external/shared budgets.
-/

/-
  Proposition 137: multi-step rewrite chains for finite generative queries.

  P50/P97 prove local cost-aware rewrite laws.  P136 consumes a direct rewrite
  certificate for each optimized workload item.  Real optimizers normally
  produce a sequence of local rewrites, not one monolithic certificate.

  This file closes that algebraic seam:

    local rewrite certificates compose;
    finite rewrite chains collapse to one denotation-preserving,
      cost-nonincreasing certificate;
    named optimized workloads may therefore carry a rewrite chain per item and
      still inherit P136's denotation and hot-path complexity bounds.

  Boundary: this is optimizer-correctness for supplied finite rewrite chains.
  It is not a search algorithm, a completeness theorem for all possible
  optimizations, or a best-plan theorem.
-/

import H0mework.Realization.QueryPlans.P136
import H0mework.Realization.QueryPlans.P97

/-! ## Stateless finite Kleisli rewrite chains -/

namespace FiniteKleisliFieldAlg

variable {Row Base : Type*} [DecidableEq Row]
variable {domain : Finset Row}

/-- THEOREM 1: identity rewrite certificate. -/
theorem RewriteCertificate.refl
    (q : FiniteKleisliFieldAlg Row Base) :
    RewriteCertificate domain q q where
  result_eq := by
    intro _env _hEnv
    rfl
  workBound_le := le_rfl

/-- THEOREM 2: cost-aware rewrite certificates compose. -/
theorem RewriteCertificate.trans
    {lhs mid rhs : FiniteKleisliFieldAlg Row Base}
    (C₁ : RewriteCertificate domain lhs mid)
    (C₂ : RewriteCertificate domain mid rhs) :
    RewriteCertificate domain lhs rhs where
  result_eq := by
    intro env hEnv
    unfold FiniteEquivalent
    calc
      evalFinset domain env lhs = evalFinset domain env mid :=
        C₁.preserves_eval env hEnv
      _ = evalFinset domain env rhs :=
        C₂.preserves_eval env hEnv
  workBound_le := by
    exact le_trans C₂.nonincreasing C₁.nonincreasing

/-- A concrete finite chain of cost-aware rewrites.  The chain lives in `Type`
because we want to compute a composite certificate from it. -/
inductive RewriteChain
    (domain : Finset Row) :
    FiniteKleisliFieldAlg Row Base ->
    FiniteKleisliFieldAlg Row Base -> Type _ where
  | refl (q : FiniteKleisliFieldAlg Row Base) : RewriteChain domain q q
  | step {lhs mid rhs : FiniteKleisliFieldAlg Row Base}
      (head : RewriteCertificate domain lhs mid)
      (tail : RewriteChain domain mid rhs) :
      RewriteChain domain lhs rhs

namespace RewriteChain

/-- THEOREM 3: every finite rewrite chain collapses to one rewrite
certificate. -/
theorem toCertificate :
    {lhs rhs : FiniteKleisliFieldAlg Row Base} ->
    RewriteChain domain lhs rhs ->
      RewriteCertificate domain lhs rhs
  | _lhs, _rhs, chain => by
      induction chain with
      | refl q =>
          exact RewriteCertificate.refl q
      | step head _tail ih =>
          exact RewriteCertificate.trans head ih

/-- THEOREM 4: a rewrite chain preserves finite denotation. -/
theorem preserves_eval
    {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteChain domain lhs rhs)
    (env : Base -> Finset Row)
    (hEnv : forall b, env b ⊆ domain) :
    evalFinset domain env lhs = evalFinset domain env rhs :=
  C.toCertificate.preserves_eval env hEnv

/-- THEOREM 5: a rewrite chain is structurally cost-nonincreasing. -/
theorem nonincreasing
    {lhs rhs : FiniteKleisliFieldAlg Row Base}
    (C : RewriteChain domain lhs rhs) :
    workBound domain rhs <= workBound domain lhs :=
  C.toCertificate.nonincreasing

end RewriteChain

end FiniteKleisliFieldAlg

/-! ## Stateful finite rewrite chains -/

namespace FiniteStatefulGenAlg

variable {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
variable {stateDomain : Finset State} {rowDomain : Finset Row}

/-- THEOREM 6: identity stateful rewrite certificate. -/
theorem RewriteCertificate.refl
    (q : FiniteStatefulGenAlg State Row Prim) :
    RewriteCertificate stateDomain rowDomain q q where
  result_eq := by
    intro _env _hEnv _hRow _hCurrent _x
    rfl
  workBound_le := le_rfl

/-- THEOREM 7: stateful cost-aware rewrite certificates compose. -/
theorem RewriteCertificate.trans
    {lhs mid rhs : FiniteStatefulGenAlg State Row Prim}
    (C₁ : RewriteCertificate stateDomain rowDomain lhs mid)
    (C₂ : RewriteCertificate stateDomain rowDomain mid rhs) :
    RewriteCertificate stateDomain rowDomain lhs rhs where
  result_eq := by
    intro env hEnv hRow hCurrent x
    calc
      evalFinset stateDomain rowDomain env lhs x =
          evalFinset stateDomain rowDomain env mid x :=
        C₁.preserves_eval env hEnv hRow hCurrent x
      _ = evalFinset stateDomain rowDomain env rhs x :=
        C₂.preserves_eval env hEnv hRow hCurrent x
  workBound_le := by
    exact le_trans C₂.nonincreasing C₁.nonincreasing

/-- A concrete finite chain of stateful rewrites. -/
inductive RewriteChain
    (stateDomain : Finset State) (rowDomain : Finset Row) :
    FiniteStatefulGenAlg State Row Prim ->
    FiniteStatefulGenAlg State Row Prim -> Type _ where
  | refl (q : FiniteStatefulGenAlg State Row Prim) :
      RewriteChain stateDomain rowDomain q q
  | step {lhs mid rhs : FiniteStatefulGenAlg State Row Prim}
      (head : RewriteCertificate stateDomain rowDomain lhs mid)
      (tail : RewriteChain stateDomain rowDomain mid rhs) :
      RewriteChain stateDomain rowDomain lhs rhs

namespace RewriteChain

/-- THEOREM 8: every finite stateful rewrite chain collapses to one stateful
rewrite certificate. -/
theorem toCertificate :
    {lhs rhs : FiniteStatefulGenAlg State Row Prim} ->
    RewriteChain stateDomain rowDomain lhs rhs ->
      RewriteCertificate stateDomain rowDomain lhs rhs
  | _lhs, _rhs, chain => by
      induction chain with
      | refl q =>
          exact RewriteCertificate.refl q
      | step head _tail ih =>
          exact RewriteCertificate.trans head ih

/-- THEOREM 9: a stateful rewrite chain preserves finite denotation at every
current state. -/
theorem preserves_eval
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteChain stateDomain rowDomain lhs rhs)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv : forall p x, env p x ⊆ pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (x : State) :
    evalFinset stateDomain rowDomain env lhs x =
      evalFinset stateDomain rowDomain env rhs x :=
  C.toCertificate.preserves_eval env hEnv hRow hCurrent x

/-- THEOREM 10: a stateful rewrite chain is structurally
cost-nonincreasing. -/
theorem nonincreasing
    {lhs rhs : FiniteStatefulGenAlg State Row Prim}
    (C : RewriteChain stateDomain rowDomain lhs rhs) :
    workBound stateDomain rowDomain rhs <=
      workBound stateDomain rowDomain lhs :=
  C.toCertificate.nonincreasing

end RewriteChain

end FiniteStatefulGenAlg

/-! ## Named optimized workloads from rewrite chains -/

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-- One optimized warm-path query whose optimization is a finite chain of
local cost-aware rewrites. -/
structure WarmRewriteChainItem
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) where
  query : FiniteRuntimeGenerativePlan Row Base RuntimeGen
  optimized : FiniteKleisliFieldAlg Row Base
  chain :
    FiniteKleisliFieldAlg.RewriteChain domain
      (compiledWarmQuery runtimeRel query) optimized

/-- Turn a chain item into the direct certificate shape consumed by P136. -/
def WarmRewriteChainItem.toWarmRewriteItem
    {domain : Finset Row}
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (item : WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel) :
    WarmRewriteItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel where
  query := item.query
  optimized := item.optimized
  rewrite := item.chain.toCertificate

/-- Total warm cost for a workload optimized by rewrite chains. -/
def chainOptimizedWarmCostList
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total => optimizedWarmCost domain env item.optimized + total) 0

/-- Sum of original compiled warm bounds for a chain-optimized workload. -/
def chainOriginalWarmWorkBoundList
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total => warmWorkBound domain runtimeRel item.query + total) 0

/-- Maximum original compiled warm bound for a chain-optimized workload. -/
def chainOriginalWarmWorkBoundMax
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  items.foldr
    (fun item total =>
      Nat.max (warmWorkBound domain runtimeRel item.query) total) 0

/-- One cold materialization plus a chain-optimized warm workload. -/
def chainOptimizedColdThenWarmBatchCost
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) : Nat :=
  coldCost + chainOptimizedWarmCostList domain env items

/-- THEOREM 11: a chain-optimized workload item's result equals the original
finite runtime result. -/
theorem chainOptimizedWarmResult_eq_evalFinset
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (item : WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel) :
    optimizedWarmResult domain env item.optimized =
      evalFinset domain env runtimeRel item.query :=
  optimizedWarmResult_eq_runtime_eval_of_rewrite
    domain env runtimeRel hEnv item.query item.optimized
    item.chain.toCertificate

/-- THEOREM 12: a chain-optimized warm workload is bounded by the sum of the
original compiled warm bounds. -/
theorem chainOptimizedWarmCostList_le_originalWarmWorkBoundList
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    chainOptimizedWarmCostList domain env items <=
      chainOriginalWarmWorkBoundList domain items := by
  induction items with
  | nil =>
      simp [chainOptimizedWarmCostList, chainOriginalWarmWorkBoundList]
  | cons item rest ih =>
      simp [chainOptimizedWarmCostList, chainOriginalWarmWorkBoundList]
      exact Nat.add_le_add
        (optimizedWarmCost_le_warmWorkBound_of_rewrite
          domain env runtimeRel hEnv item.query item.optimized
          item.chain.toCertificate)
        ih

/-- THEOREM 13: the original bound sum is bounded by
`query_count * max_original_warm_bound`. -/
theorem chainOriginalWarmWorkBoundList_le_length_mul_max
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool} :
    forall items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel),
      chainOriginalWarmWorkBoundList domain items <=
        items.length * chainOriginalWarmWorkBoundMax domain items := by
  intro items
  induction items with
  | nil =>
      simp [chainOriginalWarmWorkBoundList, chainOriginalWarmWorkBoundMax]
  | cons item rest ih =>
      let b := warmWorkBound domain runtimeRel item.query
      let m := chainOriginalWarmWorkBoundMax domain rest
      have hhead : b <= Nat.max b m := Nat.le_max_left b m
      have htail :
          chainOriginalWarmWorkBoundList domain rest <= rest.length * m := ih
      have htail' :
          chainOriginalWarmWorkBoundList domain rest <=
            rest.length * Nat.max b m := by
        exact le_trans htail
          (Nat.mul_le_mul_left rest.length (Nat.le_max_right b m))
      dsimp [chainOriginalWarmWorkBoundList, chainOriginalWarmWorkBoundMax]
      calc
        b + chainOriginalWarmWorkBoundList domain rest
            <= Nat.max b m + rest.length * Nat.max b m := by
              exact Nat.add_le_add hhead htail'
        _ = Nat.succ rest.length * Nat.max b m := by
              rw [Nat.succ_mul]
              omega

/-- THEOREM 14: a chain-optimized warm workload is bounded by
`query_count * max_original_warm_bound`. -/
theorem chainOptimizedWarmCostList_le_length_mul_originalMax
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    chainOptimizedWarmCostList domain env items <=
      items.length * chainOriginalWarmWorkBoundMax domain items := by
  exact le_trans
    (chainOptimizedWarmCostList_le_originalWarmWorkBoundList
      domain env runtimeRel hEnv items)
    (chainOriginalWarmWorkBoundList_le_length_mul_max domain items)

/-- THEOREM 15: after one cold materialization, the chain-optimized workload is
bounded by cold cost plus `query_count * max_original_warm_bound`. -/
theorem chainOptimizedColdThenWarmBatchCost_le_cold_plus_length_mul_originalMax
    (coldCost : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel)) :
    chainOptimizedColdThenWarmBatchCost coldCost domain env items <=
      coldCost + items.length * chainOriginalWarmWorkBoundMax domain items := by
  unfold chainOptimizedColdThenWarmBatchCost
  exact Nat.add_le_add_left
    (chainOptimizedWarmCostList_le_length_mul_originalMax
      domain env runtimeRel hEnv items)
    coldCost

/-- THEOREM 16: if the cold cost is allocated across the chain-optimized
workload, the batch is bounded by
`query_count * (allowance + max_original_warm_bound)`. -/
theorem chainOptimizedColdThenWarmBatchCost_le_length_mul_allowance_plus_originalMax
    (coldCost allowance : Nat)
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (items : List (WarmRewriteChainItem (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel))
    (hcold : coldCost <= items.length * allowance) :
    chainOptimizedColdThenWarmBatchCost coldCost domain env items <=
      items.length * (allowance + chainOriginalWarmWorkBoundMax domain items) := by
  unfold chainOptimizedColdThenWarmBatchCost
  have hwarm :
      chainOptimizedWarmCostList domain env items <=
        items.length * chainOriginalWarmWorkBoundMax domain items :=
    chainOptimizedWarmCostList_le_length_mul_originalMax
      domain env runtimeRel hEnv items
  calc
    coldCost + chainOptimizedWarmCostList domain env items
        <= items.length * allowance +
            items.length * chainOriginalWarmWorkBoundMax domain items := by
          exact Nat.add_le_add hcold hwarm
    _ = items.length *
          (allowance + chainOriginalWarmWorkBoundMax domain items) := by
          rw [Nat.mul_add]

end FiniteRuntimeGenerativePlan

/-! ## Named chain-optimized workload certificate -/

/-- A named finite workload whose compiled warm queries have each been
optimized by a finite rewrite chain. -/
structure NamedFiniteChainOptimizedWorkloadCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (items :
      List (FiniteRuntimeGenerativePlan.WarmRewriteChainItem (Row := Row)
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
    FiniteRuntimeGenerativePlan.chainOptimizedWarmCostList domain env items <=
      FiniteRuntimeGenerativePlan.chainOriginalWarmWorkBoundList domain items
  optimized_cold_then_warm_le_max :
    FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost
        coldCost domain env items <=
      coldCost + items.length *
        FiniteRuntimeGenerativePlan.chainOriginalWarmWorkBoundMax domain items
  optimized_amortized_if_allocated :
    coldCost <= items.length * allowance ->
      FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost
          coldCost domain env items <=
        items.length *
          (allowance +
            FiniteRuntimeGenerativePlan.chainOriginalWarmWorkBoundMax
              domain items)

/-- THEOREM 17: a workload of finite rewrite chains preserves named denotation
query-by-query and inherits the original workload's max-bound. -/
theorem namedFiniteChainOptimizedWorkloadCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (bridge : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (items :
      List (FiniteRuntimeGenerativePlan.WarmRewriteChainItem (Row := Row)
        (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel))
    (coldCost allowance : Nat) :
    NamedFiniteChainOptimizedWorkloadCertificate coverage domain env runtimeRel
      items coldCost allowance where
  optimized_eval_iff_named := by
    intro item _hitem row
    have hopt :
        FiniteRuntimeGenerativePlan.optimizedWarmResult domain env
            item.optimized =
          FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
            item.query :=
      FiniteRuntimeGenerativePlan.chainOptimizedWarmResult_eq_evalFinset
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
    FiniteRuntimeGenerativePlan.chainOptimizedWarmCostList_le_originalWarmWorkBoundList
      domain env runtimeRel hEnv items
  optimized_cold_then_warm_le_max :=
    FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost_le_cold_plus_length_mul_originalMax
      coldCost domain env runtimeRel hEnv items
  optimized_amortized_if_allocated := by
    intro hcold
    exact
      FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost_le_length_mul_allowance_plus_originalMax
        coldCost allowance domain env runtimeRel hEnv items hcold

namespace NamedFiniteChainOptimizedWorkloadCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {items :
  List (FiniteRuntimeGenerativePlan.WarmRewriteChainItem (Row := Row)
    (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
    domain runtimeRel)}
variable {coldCost allowance : Nat}

/-- THEOREM 18: expose denotational correctness for a chain-optimized workload
item. -/
theorem query_eval_iff_named
    (C : NamedFiniteChainOptimizedWorkloadCertificate coverage domain env
      runtimeRel items coldCost allowance)
    {item : FiniteRuntimeGenerativePlan.WarmRewriteChainItem (Row := Row)
      (Base := Base) (RuntimeGen := AippocampusRuntimeGenerator)
      domain runtimeRel}
    (hitem : item ∈ items) (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.optimizedWarmResult
        domain env item.optimized <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain item.query) row :=
  C.optimized_eval_iff_named item hitem row

/-- THEOREM 19: expose the chain-optimized workload max-bound. -/
theorem optimized_workload_max_bound
    (C : NamedFiniteChainOptimizedWorkloadCertificate coverage domain env
      runtimeRel items coldCost allowance) :
    FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost
        coldCost domain env items <=
      coldCost + items.length *
        FiniteRuntimeGenerativePlan.chainOriginalWarmWorkBoundMax domain items :=
  C.optimized_cold_then_warm_le_max

/-- THEOREM 20: expose the allocated chain-optimized workload max-bound. -/
theorem optimized_workload_amortized_bound
    (C : NamedFiniteChainOptimizedWorkloadCertificate coverage domain env
      runtimeRel items coldCost allowance)
    (hcold : coldCost <= items.length * allowance) :
    FiniteRuntimeGenerativePlan.chainOptimizedColdThenWarmBatchCost
        coldCost domain env items <=
      items.length *
        (allowance +
          FiniteRuntimeGenerativePlan.chainOriginalWarmWorkBoundMax
            domain items) :=
  C.optimized_amortized_if_allocated hcold

end NamedFiniteChainOptimizedWorkloadCertificate

/-!
  Summary:
  - Local rewrite certificates now form a preorder-like optimization algebra:
    reflexive, transitive, and collapsible from concrete finite chains.
  - This holds for both stateless finite Kleisli queries and stateful
    read/generate/write queries.
  - Named optimized workloads can carry a rewrite chain per item and still
    preserve named denotation with the same max-bound complexity shape.
-/

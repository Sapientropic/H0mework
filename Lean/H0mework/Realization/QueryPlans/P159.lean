/-
  Proposition 159: product-closure cost optimality for finite generated
  workloads.

  P145 proves per-query rewrite-closure optimality: a selected candidate is no
  more expensive than any rewrite-chain candidate for that query once candidate
  enumeration is dominance-complete.

  A workload needs the product version: if every item is no more expensive than
  its alternative, the selected workload is no more expensive than the whole
  alternative workload.  This file proves that summation bridge and supplies
  the direct per-item hook from P145.

  Boundary: this is product-of-independent-query optimality.  It does not yet
  optimize across queries by sharing subplans, changing materialization, or
  exploiting cache reuse.
-/

import H0mework.Realization.RelaxationFlow.P158
import H0mework.Realization.QueryPlans.P145

namespace NamedFiniteClosureOptimalWorkload

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-! ## Selected and alternative workload costs -/

/-- Total selected warm cost for a closure-optimal workload. -/
def closureSelectedCostList :
    List (NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel) ->
      Nat
  | [] => 0
  | item :: items =>
      item.item.selectedCost + closureSelectedCostList items

/-- Sum of an alternative workload cost vector. -/
def alternativeCostList : List Nat -> Nat
  | [] => 0
  | cost :: costs => cost + alternativeCostList costs

/-- A cost vector is a product alternative for a selected workload when it has
the same shape and every selected item is no more expensive than the matching
alternative component.  Actual rewrite-chain candidates feed this predicate via
`candidateCost_dominates_item` below. -/
def ProductAlternativeCostDominates :
    List (NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel) ->
      List Nat -> Prop
  | [], [] => True
  | item :: items, cost :: costs =>
      item.item.selectedCost <= cost /\
        ProductAlternativeCostDominates items costs
  | _, _ => False

/-! ## Product optimality -/

/-- THEOREM 1: componentwise closure optimality sums to workload-level product
optimality. -/
theorem closureSelectedCostList_le_alternativeCostList :
    forall
      (items :
        List (NamedFiniteClosureOptimalWorkloadItem
          coverage domain env runtimeRel))
      (costs : List Nat),
      ProductAlternativeCostDominates items costs ->
        closureSelectedCostList items <= alternativeCostList costs
  | [], [], _ => by
      simp [closureSelectedCostList, alternativeCostList]
  | [], _ :: _, h => by
      cases h
  | _ :: _, [], h => by
      cases h
  | item :: items, cost :: costs, h => by
      rcases h with ⟨hitem, hrest⟩
      simp [closureSelectedCostList, alternativeCostList]
      exact Nat.add_le_add hitem
        (closureSelectedCostList_le_alternativeCostList items costs hrest)

/-- THEOREM 2: P145 supplies the componentwise dominance needed for a real
rewrite-chain candidate alternative. -/
theorem candidateCost_dominates_item
    (item :
      NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel item.item.query) :
    item.item.selectedCost <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate :=
  item.selectedCost_le_any_rewrite_candidate candidate

/-- THEOREM 3: prepending a real rewrite-chain candidate cost to an alternative
cost vector preserves product dominance. -/
theorem cons_candidateCost_dominates
    (item :
      NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel item.item.query)
    (items :
      List (NamedFiniteClosureOptimalWorkloadItem coverage domain env
        runtimeRel))
    (costs : List Nat)
    (hrest : ProductAlternativeCostDominates items costs) :
    ProductAlternativeCostDominates (item :: items)
      (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate :: costs) := by
  exact ⟨candidateCost_dominates_item item candidate, hrest⟩

/-- One cold materialization plus selected closure-optimal warm workload. -/
def coldThenClosureSelectedCost
    (coldCost : Nat)
    (items :
      List (NamedFiniteClosureOptimalWorkloadItem coverage domain env
        runtimeRel)) : Nat :=
  coldCost + closureSelectedCostList items

/-- One cold materialization plus an alternative workload cost vector. -/
def coldThenAlternativeCost (coldCost : Nat) (costs : List Nat) : Nat :=
  coldCost + alternativeCostList costs

/-- THEOREM 4: adding the same cold materialization cost preserves product
closure optimality. -/
theorem coldThenClosureSelectedCost_le_coldThenAlternativeCost
    (coldCost : Nat)
    (items :
      List (NamedFiniteClosureOptimalWorkloadItem coverage domain env
        runtimeRel))
    (costs : List Nat)
    (h :
      ProductAlternativeCostDominates
        (coverage := coverage) (domain := domain) (env := env)
        (runtimeRel := runtimeRel) items costs) :
    coldThenClosureSelectedCost coldCost items <=
      coldThenAlternativeCost coldCost costs := by
  unfold coldThenClosureSelectedCost coldThenAlternativeCost
  exact Nat.add_le_add_left
    (closureSelectedCostList_le_alternativeCostList items costs h) coldCost

/-- THEOREM 5: closure-selected cost is exactly the P144 selected-cost list
after forgetting closure-completeness evidence. -/
theorem closureSelectedCostList_eq_bestSelectedCostList :
    forall items :
      List (NamedFiniteClosureOptimalWorkloadItem coverage domain env
        runtimeRel),
      closureSelectedCostList items =
        NamedFiniteBestWorkload.selectedCostList
          (toBestWorkloadItems items)
  | [] => by
      simp [closureSelectedCostList, toBestWorkloadItems,
        NamedFiniteBestWorkload.selectedCostList]
  | item :: items => by
      simp [closureSelectedCostList, toBestWorkloadItems,
        NamedFiniteClosureOptimalWorkloadItem.toBestWorkloadItem,
        NamedFiniteBestWorkload.selectedCostList,
        NamedFiniteBestWorkloadItem.selectedCost,
        closureSelectedCostList_eq_bestSelectedCostList items]

/-!
  Summary:
  - P159 turns per-query closure optimality into product workload optimality.
  - The dependent candidate space is intentionally reflected through a cost
    vector plus per-item dominance proof; real candidates produce those
    component proofs via `candidateCost_dominates_item`.
  - The remaining optimizer debt is cross-query sharing/common-subplan
    optimization, not independent per-query product closure.
-/


end NamedFiniteClosureOptimalWorkload

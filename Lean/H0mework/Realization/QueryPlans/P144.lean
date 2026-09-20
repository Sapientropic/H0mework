/-
  Proposition 144: workload-level finite best-choice certificate.

  P138 proves a best-choice certificate for one compiled finite runtime query:
  the selected rewrite-chain candidate preserves named denotation, is best among
  the finite candidates the optimizer enumerated, and remains under the
  original compiled warm bound.

  Agent-native workloads are usually lists of such queries.  This proposition
  lifts P138 to the workload level without claiming global optimizer
  completeness: if each workload item carries a named finite best-choice
  certificate, then the whole selected workload has pointwise named denotation
  correctness and its total selected warm cost is bounded by the sum of the
  original structural warm bounds.

  Boundary: candidate enumeration is still an input for each item.  This proves
  "best among each item's enumerated candidates" and a workload cost envelope,
  not "globally best among all possible rewrites".
-/

import H0mework.Realization.QueryPlans.P138

/-! ## Workload-level best-choice items -/

/-- One query in a workload, bundled with its finite best-choice certificate. -/
structure NamedFiniteBestWorkloadItem
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool) where
  query :
    FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator
  candidates :
    List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
      (Row := Row) (Base := Base)
      (RuntimeGen := AippocampusRuntimeGenerator)
      domain runtimeRel query)
  cert :
    NamedFiniteBestRewriteChoiceCertificate
      coverage domain env runtimeRel query candidates

namespace NamedFiniteBestWorkloadItem

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- Selected warm cost for one best-choice workload item. -/
def selectedCost
    (item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel) : Nat :=
  FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
    domain env item.cert.best.selected

/-- Original structural warm bound for one best-choice workload item. -/
def originalBound
    (item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel) : Nat :=
  FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel item.query

/-- THEOREM 1: the selected candidate for one workload item preserves named
runtime denotation. -/
theorem selected_eval_iff_named
    (item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env item.cert.best.selected <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain item.query) row :=
  item.cert.query_eval_iff_named row

/-- THEOREM 2: the selected candidate remains under the original structural
warm bound for that item. -/
theorem selectedCost_le_originalBound
    (item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel) :
    selectedCost item <= originalBound item :=
  item.cert.selected_cost_le_original_bound

/-- THEOREM 3: the selected candidate is no more expensive than any enumerated
candidate for that item. -/
theorem selectedCost_le_candidate
    (item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel)
    {candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel item.query}
    (hmem : candidate ∈ item.candidates) :
    selectedCost item <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate :=
  item.cert.selected_cost_le_candidate hmem

end NamedFiniteBestWorkloadItem

/-! ## Workload totals -/

namespace NamedFiniteBestWorkload

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- Total selected warm cost for a workload of best-choice items. -/
def selectedCostList :
    List (NamedFiniteBestWorkloadItem coverage domain env runtimeRel) -> Nat
  | [] => 0
  | item :: items =>
      item.selectedCost + selectedCostList items

/-- Sum of original structural warm bounds for the same workload. -/
def originalBoundList :
    List (NamedFiniteBestWorkloadItem coverage domain env runtimeRel) -> Nat
  | [] => 0
  | item :: items =>
      item.originalBound + originalBoundList items

/-- One cold materialization followed by the selected optimized workload. -/
def coldThenSelectedCost
    (coldCost : Nat)
    (items : List (NamedFiniteBestWorkloadItem coverage domain env runtimeRel)) :
    Nat :=
  coldCost + selectedCostList items

/-- THEOREM 4: total selected warm cost is bounded by the sum of the original
compiled warm bounds. -/
theorem selectedCostList_le_originalBoundList :
    forall items : List
      (NamedFiniteBestWorkloadItem coverage domain env runtimeRel),
      selectedCostList items <= originalBoundList items
  | [] => by
      simp [selectedCostList, originalBoundList]
  | item :: items => by
      simp [selectedCostList, originalBoundList]
      exact Nat.add_le_add
        item.selectedCost_le_originalBound
        (selectedCostList_le_originalBoundList items)

/-- THEOREM 5: after one cold materialization, the selected workload stays
inside the cold-plus-original-bounds envelope. -/
theorem coldThenSelectedCost_le_cold_plus_originalBoundList
    (coldCost : Nat)
    (items : List
      (NamedFiniteBestWorkloadItem coverage domain env runtimeRel)) :
    coldThenSelectedCost coldCost items <=
      coldCost + originalBoundList items := by
  unfold coldThenSelectedCost
  exact Nat.add_le_add_left (selectedCostList_le_originalBoundList items)
    coldCost

/-- THEOREM 6: if the one-time cold cost is allocated across the workload, the
selected workload has the same per-item amortized envelope shape as P134/P137.
-/
theorem coldThenSelectedCost_le_length_allowance_plus_originalBoundList
    (coldCost allowance : Nat)
    (items : List
      (NamedFiniteBestWorkloadItem coverage domain env runtimeRel))
    (hcold : coldCost <= items.length * allowance) :
    coldThenSelectedCost coldCost items <=
      items.length * allowance + originalBoundList items := by
  unfold coldThenSelectedCost
  exact Nat.add_le_add hcold (selectedCostList_le_originalBoundList items)

end NamedFiniteBestWorkload

/-!
  Summary:
  - P144 turns the single-query P138 best-choice theorem into a workload-level
    certificate.
  - Every selected item remains named-denotation correct.
  - The selected workload's total warm cost is bounded by the original workload
    structural warm-bound sum, with the same cold-cost amortization shape used
    by the earlier workload certificates.

  Boundary:
  - The theorem is still relative to each item's finite candidate enumeration.
    It does not prove the optimizer has enumerated all possible rewrites.
-/

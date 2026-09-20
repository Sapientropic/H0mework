/-
  Proposition 145: from finite-candidate best choice to rewrite-closure
  optimality.

  P138 proves "best among the finite candidates the optimizer enumerated".
  P144 lifts that to finite workloads.  The remaining optimizer boundary is
  candidate-enumeration completeness: did the optimizer enumerate enough
  candidates to represent the whole rewrite closure?

  This file makes that boundary explicit.  A candidate enumeration is complete
  when every rewrite-chain candidate is cost-dominated by some enumerated
  candidate.  Under that certificate, P138's selected candidate is not merely
  best in the finite list; it is optimal over the whole rewrite-chain candidate
  type for that query.

  Boundary: this still does not construct the enumeration.  It proves the
  theorem that a real optimizer can earn by supplying a dominance-complete
  candidate list.
-/

import H0mework.Realization.QueryPlans.P144

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Candidate enumeration completeness -/

/-- A finite candidate list is complete for rewrite-closure optimization when
every possible rewrite-chain candidate is cost-dominated by an enumerated
candidate.  This is weaker and more useful than requiring syntactic equality:
the optimizer may omit redundant candidates if it keeps a no-more-expensive
representative. -/
structure CandidateEnumerationComplete
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidates :
      List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query)) where
  dominates_all :
    forall candidate :
      WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query,
      exists listed, listed ∈ candidates /\
        listed.cost domain env <= candidate.cost domain env

namespace CandidateEnumerationComplete

variable {domain : Finset Row} {env : Base -> Finset Row}
variable {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
variable {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
variable {candidates :
  List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
    (RuntimeGen := RuntimeGen) domain runtimeRel query)}

/-- THEOREM 1: expose the enumerated representative dominated by any rewrite
candidate. -/
theorem representative
    (C : CandidateEnumerationComplete domain env runtimeRel query candidates)
    (candidate :
      WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query) :
    exists listed, listed ∈ candidates /\
      listed.cost domain env <= candidate.cost domain env :=
  C.dominates_all candidate

end CandidateEnumerationComplete

/-! ## Closure-optimal best choice -/

/-- A best-choice certificate plus a dominance-complete candidate enumeration.
-/
structure RewriteClosureOptimalChoice
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidates :
      List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query)) where
  best : BestWarmRewriteChainChoice domain env runtimeRel query candidates
  complete : CandidateEnumerationComplete domain env runtimeRel query candidates

namespace RewriteClosureOptimalChoice

variable {domain : Finset Row} {env : Base -> Finset Row}
variable {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
variable {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
variable {candidates :
  List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
    (RuntimeGen := RuntimeGen) domain runtimeRel query)}

/-- THEOREM 2: a finite-list best choice with complete enumeration is optimal
over every rewrite-chain candidate for the query. -/
theorem selected_cost_le_any_rewrite_candidate
    (C : RewriteClosureOptimalChoice domain env runtimeRel query candidates)
    (candidate :
      WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query) :
    C.best.selected.cost domain env <= candidate.cost domain env := by
  rcases C.complete.representative candidate with
    ⟨listed, hlisted, hlisted_le_candidate⟩
  exact le_trans (C.best.selected_cost_le_candidate hlisted)
    hlisted_le_candidate

/-- THEOREM 3: closure optimality still preserves the original compiled warm
bound. -/
theorem selected_cost_le_original_bound
    (C : RewriteClosureOptimalChoice domain env runtimeRel query candidates)
    (hEnv : forall b, env b ⊆ domain) :
    C.best.selected.cost domain env <=
      warmWorkBound domain runtimeRel query :=
  C.best.selected_cost_le_original hEnv

end RewriteClosureOptimalChoice

end FiniteRuntimeGenerativePlan

/-! ## Named certificate and workload lift -/

/-- Named version of rewrite-closure optimality for one AIppocampus runtime
query. -/
structure NamedFiniteRewriteClosureOptimalCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (candidates :
      List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel query)) where
  namedBest :
    NamedFiniteBestRewriteChoiceCertificate
      coverage domain env runtimeRel query candidates
  complete :
    FiniteRuntimeGenerativePlan.CandidateEnumerationComplete
      domain env runtimeRel query candidates

namespace NamedFiniteRewriteClosureOptimalCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {query :
  FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
variable {candidates :
  List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
    (Row := Row) (Base := Base)
    (RuntimeGen := AippocampusRuntimeGenerator)
    domain runtimeRel query)}

/-- THEOREM 4: named closure-optimal certificates preserve named denotation. -/
theorem selected_eval_iff_named
    (C : NamedFiniteRewriteClosureOptimalCertificate coverage domain env
      runtimeRel query candidates)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env C.namedBest.best.selected <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain query) row :=
  C.namedBest.query_eval_iff_named row

/-- THEOREM 5: the selected named candidate is optimal over all rewrite-chain
candidates for this query, not merely the finite list. -/
theorem selected_cost_le_any_rewrite_candidate
    (C : NamedFiniteRewriteClosureOptimalCertificate coverage domain env
      runtimeRel query candidates)
    (candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel query) :
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env C.namedBest.best.selected <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate := by
  rcases C.complete.representative candidate with
    ⟨listed, hlisted, hlisted_le_candidate⟩
  exact le_trans (C.namedBest.selected_cost_le_candidate hlisted)
    hlisted_le_candidate

end NamedFiniteRewriteClosureOptimalCertificate

/-- One workload item with rewrite-closure optimality. -/
structure NamedFiniteClosureOptimalWorkloadItem
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool) where
  item : NamedFiniteBestWorkloadItem coverage domain env runtimeRel
  complete :
    FiniteRuntimeGenerativePlan.CandidateEnumerationComplete
      domain env runtimeRel item.query item.candidates

namespace NamedFiniteClosureOptimalWorkloadItem

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- Forget the extra closure-completeness evidence and recover the P144
best-workload item. -/
def toBestWorkloadItem
    (item :
      NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel) :
    NamedFiniteBestWorkloadItem coverage domain env runtimeRel :=
  item.item

/-- THEOREM 6: a closure-optimal workload item is optimal over every
rewrite-chain candidate for its query. -/
theorem selectedCost_le_any_rewrite_candidate
    (item :
      NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel item.item.query) :
    item.item.selectedCost <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate := by
  rcases item.complete.representative candidate with
    ⟨listed, hlisted, hlisted_le_candidate⟩
  exact le_trans (item.item.selectedCost_le_candidate hlisted)
    hlisted_le_candidate

end NamedFiniteClosureOptimalWorkloadItem

namespace NamedFiniteClosureOptimalWorkload

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- Forget closure-completeness from a workload, keeping the P144 best-choice
items. -/
def toBestWorkloadItems :
    List (NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel) ->
      List (NamedFiniteBestWorkloadItem coverage domain env runtimeRel)
  | [] => []
  | item :: items => item.toBestWorkloadItem :: toBestWorkloadItems items

/-- THEOREM 7: closure-optimal workloads inherit P144's selected-cost envelope.
-/
theorem selectedCostList_le_originalBoundList
    (items :
      List (NamedFiniteClosureOptimalWorkloadItem
        coverage domain env runtimeRel)) :
    NamedFiniteBestWorkload.selectedCostList
        (toBestWorkloadItems items) <=
      NamedFiniteBestWorkload.originalBoundList
        (toBestWorkloadItems items) :=
  NamedFiniteBestWorkload.selectedCostList_le_originalBoundList
    (toBestWorkloadItems items)

end NamedFiniteClosureOptimalWorkload

/-!
  Summary:
  - P145 does not assume optimizer completeness silently.
  - It names the exact certificate needed: every rewrite-chain candidate is
    cost-dominated by an enumerated candidate.
  - With that certificate, finite-list best choice becomes global optimality
    over the rewrite-chain candidate type for that query, and finite workloads
    retain the P144 cost envelope.

  Boundary:
  - Constructing the complete enumeration remains outside this theorem.  This
    is the theorem a production optimizer can plug into once it has an
    exhaustive/dominating rewrite-candidate generator.
-/

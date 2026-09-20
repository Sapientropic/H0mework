/-
  Proposition 138: finite best-choice certificates for rewrite-chain
  optimizers.

  P137 proves that finite rewrite chains are sound and cost-nonincreasing.
  This file adds the next optimization layer: a finite enumerated candidate set
  may carry a best-choice certificate.  The selected candidate is then known to
  preserve named denotation, remain under the original compiled warm bound, and
  be no more expensive than any candidate in that enumerated set.

  Boundary: this is a finite candidate-set best-plan theorem, not a global
  optimizer completeness theorem.  It proves "best among the candidates the
  optimizer enumerated", not "best among all possible rewrites".
-/

import H0mework.Realization.QueryPlans.P137

namespace FiniteRuntimeGenerativePlan

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]

/-! ## Candidate-set optimizer objects -/

/-- One candidate optimization for a fixed finite runtime query. -/
structure WarmRewriteChainCandidate
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen) where
  optimized : FiniteKleisliFieldAlg Row Base
  chain :
    FiniteKleisliFieldAlg.RewriteChain domain
      (compiledWarmQuery runtimeRel query) optimized

/-- Candidate result set. -/
def WarmRewriteChainCandidate.result
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) : Finset Row :=
  optimizedWarmResult domain env candidate.optimized

/-- Candidate warm execution cost. -/
def WarmRewriteChainCandidate.cost
    (domain : Finset Row) (env : Base -> Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) : Nat :=
  optimizedWarmCost domain env candidate.optimized

/-- Candidate structural work bound. -/
def WarmRewriteChainCandidate.workBound
    (domain : Finset Row)
    {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
    {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) : Nat :=
  FiniteKleisliFieldAlg.workBound domain candidate.optimized

/-- THEOREM 1: every candidate preserves the fixed runtime query result. -/
theorem WarmRewriteChainCandidate.result_eq_evalFinset
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) :
    candidate.result domain env =
      evalFinset domain env runtimeRel query :=
  optimizedWarmResult_eq_runtime_eval_of_rewrite
    domain env runtimeRel hEnv query candidate.optimized
    candidate.chain.toCertificate

/-- THEOREM 2: every candidate's structural bound is no larger than the
original compiled warm query's bound. -/
theorem WarmRewriteChainCandidate.workBound_le_original
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) :
    candidate.workBound domain <=
      warmWorkBound domain runtimeRel query :=
  optimized_workBound_le_warmWorkBound_of_rewrite
    domain runtimeRel query candidate.optimized candidate.chain.toCertificate

/-- THEOREM 3: every candidate's actual warm cost is no larger than the
original compiled warm query's bound. -/
theorem WarmRewriteChainCandidate.cost_le_original
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidate : WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query) :
    candidate.cost domain env <= warmWorkBound domain runtimeRel query :=
  optimizedWarmCost_le_warmWorkBound_of_rewrite
    domain env runtimeRel hEnv query candidate.optimized
    candidate.chain.toCertificate

/-- A finite candidate-set best-choice certificate for one query.  The selected
candidate must be in the enumerated set and have warm cost no greater than any
enumerated candidate. -/
structure BestWarmRewriteChainChoice
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (query : FiniteRuntimeGenerativePlan Row Base RuntimeGen)
    (candidates :
      List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query)) where
  selected :
    WarmRewriteChainCandidate (Row := Row) (Base := Base)
      (RuntimeGen := RuntimeGen) domain runtimeRel query
  selected_mem : selected ∈ candidates
  selected_cost_le_all :
    forall candidate, candidate ∈ candidates ->
      selected.cost domain env <= candidate.cost domain env

namespace BestWarmRewriteChainChoice

variable {domain : Finset Row} {env : Base -> Finset Row}
variable {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
variable {query : FiniteRuntimeGenerativePlan Row Base RuntimeGen}
variable {candidates :
  List (WarmRewriteChainCandidate (Row := Row) (Base := Base)
    (RuntimeGen := RuntimeGen) domain runtimeRel query)}

/-- THEOREM 4: the chosen candidate preserves the fixed runtime query result. -/
theorem selected_result_eq_evalFinset
    (C : BestWarmRewriteChainChoice domain env runtimeRel query candidates)
    (hEnv : forall b, env b ⊆ domain) :
    C.selected.result domain env =
      evalFinset domain env runtimeRel query :=
  WarmRewriteChainCandidate.result_eq_evalFinset
    domain env runtimeRel hEnv query C.selected

/-- THEOREM 5: the chosen candidate is no more expensive than any enumerated
candidate. -/
theorem selected_cost_le_candidate
    (C : BestWarmRewriteChainChoice domain env runtimeRel query candidates)
    {candidate :
      WarmRewriteChainCandidate (Row := Row) (Base := Base)
        (RuntimeGen := RuntimeGen) domain runtimeRel query}
    (hmem : candidate ∈ candidates) :
    C.selected.cost domain env <= candidate.cost domain env :=
  C.selected_cost_le_all candidate hmem

/-- THEOREM 6: the chosen candidate's structural bound is under the original
compiled warm query. -/
theorem selected_workBound_le_original
    (C : BestWarmRewriteChainChoice domain env runtimeRel query candidates) :
    C.selected.workBound domain <= warmWorkBound domain runtimeRel query :=
  WarmRewriteChainCandidate.workBound_le_original
    domain runtimeRel query C.selected

/-- THEOREM 7: the chosen candidate's actual warm cost is under the original
compiled warm query. -/
theorem selected_cost_le_original
    (C : BestWarmRewriteChainChoice domain env runtimeRel query candidates)
    (hEnv : forall b, env b ⊆ domain) :
    C.selected.cost domain env <= warmWorkBound domain runtimeRel query :=
  WarmRewriteChainCandidate.cost_le_original
    domain env runtimeRel hEnv query C.selected

end BestWarmRewriteChainChoice

end FiniteRuntimeGenerativePlan

/-! ## Named best-choice certificate -/

/-- A named finite best-choice certificate for one runtime query.  It combines
the finite candidate-set minimum with the named Bool/Prop relation bridge. -/
structure NamedFiniteBestRewriteChoiceCertificate
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
  best :
    FiniteRuntimeGenerativePlan.BestWarmRewriteChainChoice
      domain env runtimeRel query candidates
  selected_eval_iff_named :
    forall row,
      row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
          domain env best.selected <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel
          (finiteRuntimePlanToRuntimePlan domain query) row
  selected_cost_le_all_candidates :
    forall candidate, candidate ∈ candidates ->
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
          domain env best.selected <=
        FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
          domain env candidate
  selected_cost_le_original :
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env best.selected <=
      FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel query

/-- THEOREM 8: build a named finite best-choice certificate from a candidate
minimum and the named relation bridge. -/
def namedFiniteBestRewriteChoiceCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (hEnv : forall b, env b ⊆ domain)
    (bridge : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (query : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (candidates :
      List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel query))
    (best :
      FiniteRuntimeGenerativePlan.BestWarmRewriteChainChoice
        domain env runtimeRel query candidates) :
    NamedFiniteBestRewriteChoiceCertificate coverage domain env runtimeRel query
      candidates where
  best := best
  selected_eval_iff_named := by
    intro row
    have hresult :
        best.selected.result domain env =
          FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
            query :=
      best.selected_result_eq_evalFinset hEnv
    calc
      row ∈ best.selected.result domain env
          <->
        row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
          query := by
            rw [hresult]
      _ <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel
          (finiteRuntimePlanToRuntimePlan domain query) row := by
            exact
              (finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel
                query row).trans
              (bridge.runtimePlan_eval_iff_named query row)
  selected_cost_le_all_candidates := by
    intro candidate hmem
    exact best.selected_cost_le_candidate hmem
  selected_cost_le_original :=
    best.selected_cost_le_original hEnv

namespace NamedFiniteBestRewriteChoiceCertificate

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

/-- THEOREM 9: expose named denotation correctness for the chosen candidate. -/
theorem query_eval_iff_named
    (C : NamedFiniteBestRewriteChoiceCertificate coverage domain env
      runtimeRel query candidates)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env C.best.selected <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain query) row :=
  C.selected_eval_iff_named row

/-- THEOREM 10: expose finite-candidate optimality for the chosen candidate. -/
theorem selected_cost_le_candidate
    (C : NamedFiniteBestRewriteChoiceCertificate coverage domain env
      runtimeRel query candidates)
    {candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel query}
    (hmem : candidate ∈ candidates) :
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env C.best.selected <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate :=
  C.selected_cost_le_all_candidates candidate hmem

/-- THEOREM 11: expose the original compiled warm bound for the chosen
candidate. -/
theorem selected_cost_le_original_bound
    (C : NamedFiniteBestRewriteChoiceCertificate coverage domain env
      runtimeRel query candidates) :
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env C.best.selected <=
      FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel query :=
  C.selected_cost_le_original

end NamedFiniteBestRewriteChoiceCertificate

/-!
  Summary:
  - P138 is the finite enumerated best-plan slice missing after P137.
  - A selected rewrite-chain candidate is certified best among the optimizer's
    finite candidate set, not merely sound.
  - The named certificate connects that local optimality back to named
    Prop-valued query denotation.

  Boundary:
  - Candidate enumeration itself is an input.  This theorem does not prove the
    enumeration is complete for all possible rewrites or that the chosen plan is
    globally optimal outside the finite candidate set.
-/

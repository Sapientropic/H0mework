import H0mework.Realization.Query.P154
import H0mework.Realization.QueryPlans.P159

/-!
# Proposition 175: workload-level agent-native query theory certificate

P154 packages the current finite query theory for one named/materialized query:
mutual expressiveness, executable denotation, amortized warm bounds, and
rewrite-closure optimality.  P159 proves product cost optimality for a workload
of independently closure-optimal queries.

This file packages the next layer up: one certificate for a finite agent-native
query workload over the same named generator basis.  It exposes:

* runtime/Kleisli/calculus mutual completeness for the basis;
* exact Bool/Prop relation bridge on the materialized slice;
* per-item selected denotation correctness;
* workload-level structural and alternative-cost envelopes.

Boundary: this is still finite, named, materialized, and certificate-relative.
It is not an unrestricted database completeness theorem and it does not solve
cross-query common-subplan optimization.
-/

namespace SaturationMonoid

/-- A finite workload-level query-theory certificate for the current
AIppocampus named generator basis. -/
structure AgentNativeFiniteQueryTheoryCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base → Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool)
    where
  relationBridge :
    NamedFiniteRuntimeRelationBridge coverage domain runtimeRel
  domainCoversEnv :
    ∀ b, env b ⊆ domain
  items :
    List (NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)

namespace AgentNativeFiniteQueryTheoryCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base → Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool}

/-- THEOREM 1: the workload certificate exposes the named
runtime/Kleisli/calculus mutual-completeness theorem for the shared basis. -/
theorem named_mutual_completeness
    (_C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel) :
    (∀ p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      ∃ alg : KleisliFieldAlg Row Base,
        ∀ row,
          KleisliFieldAlg.eval (finiteRuntimeEnvProp env) alg row ↔
            RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row) ∧
    (∀ alg : KleisliFieldAlg Row Base,
      ∃ p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        ∀ row,
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row ↔
            KleisliFieldAlg.eval (finiteRuntimeEnvProp env) alg row) ∧
    (∀ p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      ∃ formula : KleisliFieldCalc Row Base,
        ∀ row,
          KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row ↔
            RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row) ∧
    (∀ formula : KleisliFieldCalc Row Base,
      ∃ p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        ∀ row,
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row ↔
            KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row) :=
  coverage.named_runtime_kleisli_calc_mutual_completeness
    (finiteRuntimeEnvProp env)

/-- THEOREM 2: executable finite runtime relations are sound for the named
Prop-valued runtime relation. -/
theorem executable_relation_sound
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : finiteRuntimeRelProp domain runtimeRel generator source target) :
    coverage.runtimeRel generator source target :=
  C.relationBridge.executable_sound h

/-- THEOREM 3: named Prop-valued runtime relations are complete for the
materialized executable relation. -/
theorem executable_relation_complete
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : coverage.runtimeRel generator source target) :
    finiteRuntimeRelProp domain runtimeRel generator source target :=
  C.relationBridge.executable_complete h

/-- THEOREM 4: each closure-optimal workload item preserves its named runtime
denotation.  The membership hypothesis records that this item belongs to the
certified workload; the proof itself is carried by the item certificate. -/
theorem item_selected_eval_iff_named
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    (item : NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (_hitem : item ∈ C.items)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env item.item.cert.best.selected ↔
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain item.item.query) row :=
  item.item.selected_eval_iff_named row

/-- THEOREM 5: the selected closure-optimal workload warm cost is bounded by
the sum of the original structural warm bounds. -/
theorem selectedCost_le_originalBoundList
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel) :
    NamedFiniteClosureOptimalWorkload.closureSelectedCostList C.items ≤
      NamedFiniteBestWorkload.originalBoundList
        (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems C.items) := by
  rw [NamedFiniteClosureOptimalWorkload.closureSelectedCostList_eq_bestSelectedCostList]
  exact NamedFiniteClosureOptimalWorkload.selectedCostList_le_originalBoundList
    C.items

/-- THEOREM 6: adding one shared cold materialization cost preserves the
structural workload envelope. -/
theorem coldThenSelectedCost_le_cold_plus_originalBoundList
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    (coldCost : Nat) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.items ≤
      coldCost +
        NamedFiniteBestWorkload.originalBoundList
          (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems C.items) := by
  unfold NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost
  exact Nat.add_le_add_left C.selectedCost_le_originalBoundList coldCost

/-- Helper: forgetting closure-completeness evidence preserves workload
length. -/
theorem toBestWorkloadItems_length
    (items :
      List (NamedFiniteClosureOptimalWorkloadItem coverage domain env
        runtimeRel)) :
    (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems items).length =
      items.length := by
  induction items with
  | nil =>
      simp [NamedFiniteClosureOptimalWorkload.toBestWorkloadItems]
  | cons item items ih =>
      simp [NamedFiniteClosureOptimalWorkload.toBestWorkloadItems, ih]

/-- THEOREM 7: if the shared cold materialization cost is allocated across
the workload, the selected closure-optimal workload has the same amortized
envelope shape as P144. -/
theorem coldThenSelectedCost_le_length_allowance_plus_originalBoundList
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    (coldCost allowance : Nat)
    (hcold : coldCost ≤ C.items.length * allowance) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.items ≤
      C.items.length * allowance +
        NamedFiniteBestWorkload.originalBoundList
          (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems C.items) := by
  unfold NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost
  exact Nat.add_le_add hcold C.selectedCost_le_originalBoundList

/-- THEOREM 8: product closure optimality compares the selected workload to
any same-shape alternative cost vector that componentwise dominates it. -/
theorem selectedCost_le_alternativeCostList
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    (costs : List Nat)
    (h :
      NamedFiniteClosureOptimalWorkload.ProductAlternativeCostDominates
        (coverage := coverage) (domain := domain) (env := env)
        (runtimeRel := runtimeRel) C.items costs) :
    NamedFiniteClosureOptimalWorkload.closureSelectedCostList C.items ≤
      NamedFiniteClosureOptimalWorkload.alternativeCostList costs :=
  NamedFiniteClosureOptimalWorkload.closureSelectedCostList_le_alternativeCostList
    C.items costs h

/-- THEOREM 9: adding the same cold materialization cost preserves product
closure optimality against an alternative workload. -/
theorem coldThenSelectedCost_le_coldThenAlternativeCost
    (C : AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel)
    (coldCost : Nat)
    (costs : List Nat)
    (h :
      NamedFiniteClosureOptimalWorkload.ProductAlternativeCostDominates
        (coverage := coverage) (domain := domain) (env := env)
        (runtimeRel := runtimeRel) C.items costs) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.items ≤
      NamedFiniteClosureOptimalWorkload.coldThenAlternativeCost coldCost costs :=
  NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost_le_coldThenAlternativeCost
    coldCost C.items costs h

end AgentNativeFiniteQueryTheoryCertificate

/-!
  Summary:
  - P175 moves the first-layer query-theory result from one query to a finite
    agent-native workload certificate.
  - It is the current Codd-style slice: a named finite generator basis, exact
    runtime/Kleisli/calculus mutual expressiveness, executable materialization
    bridge, denotation-preserving selected rewrites, and workload cost
    envelopes.

  Remaining boundary:
  - This still depends on supplied mechanism-faithfulness certificates:
    relation bridge, materialized domain coverage, and per-item
    dominance-complete rewrite-candidate enumeration.
  - It does not yet cover unrestricted relational completeness, external
    source-open costs, shared-subplan optimization across queries, or the full
    production AIppocampus runtime.
-/


end SaturationMonoid

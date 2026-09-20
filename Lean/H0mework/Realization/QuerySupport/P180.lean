import H0mework.Realization.QueryPlans.P175

/-!
# Proposition 180: atom/field generative query algebra closeout

P61/P96/P129/P154/P175 prove the individual pieces of the first-layer query
theory:

* covered runtime plans, Kleisli field algebra, and range-restricted calculus
  are mutually expressive for the named AIppocampus generator basis;
* finite executable relations are sound and complete for the declared runtime
  relation on a materialized domain;
* selected rewrite-closure plans preserve denotation and satisfy structural,
  amortized, and same-shape alternative workload cost envelopes.

This file packages those pieces as one Codd-style closeout certificate for the
finite, named, materialized agent-native query fragment.  The purpose is not to
claim unrestricted database completeness; it is to make the already-proved
fragment available under one theorem surface.
-/

namespace SaturationMonoid

/-- A top-level certificate that the finite named AIppocampus query fragment is
closed as an atom/field generative query algebra: syntax, denotation, executable
materialization, and workload cost are all carried by one P175 certificate. -/
structure AtomFieldGenerativeQueryAlgebraCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base → Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool)
    where
  finiteWorkload :
    AgentNativeFiniteQueryTheoryCertificate coverage domain env runtimeRel

namespace AtomFieldGenerativeQueryAlgebraCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base → Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator → Row → Row → Bool}

/-- THEOREM 1: runtime plans, Kleisli field algebra, and range-restricted
calculus are mutually expressive for the certified named generator basis. -/
theorem runtime_kleisli_calculus_complete
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel) :
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
  C.finiteWorkload.named_mutual_completeness

/-- THEOREM 2: executable finite runtime edges are sound for the declared
Prop-valued runtime relation. -/
theorem executable_relation_sound
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : finiteRuntimeRelProp domain runtimeRel generator source target) :
    coverage.runtimeRel generator source target :=
  C.finiteWorkload.executable_relation_sound h

/-- THEOREM 3: declared runtime edges are complete for the executable finite
materialization. -/
theorem executable_relation_complete
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : coverage.runtimeRel generator source target) :
    finiteRuntimeRelProp domain runtimeRel generator source target :=
  C.finiteWorkload.executable_relation_complete h

/-- THEOREM 4: each selected workload plan preserves its named runtime
denotation. -/
theorem selected_plan_denotation
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (item : NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (hitem : item ∈ C.finiteWorkload.items)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env item.item.cert.best.selected ↔
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain item.item.query) row :=
  C.finiteWorkload.item_selected_eval_iff_named item hitem row

/-- THEOREM 4b: each selected optimized workload plan also preserves the
original executable finite query result.  This is the facade-level bridge from
optimization back to the finite runtime semantics, not merely to the named
Prop-valued denotation. -/
theorem selected_plan_iff_original_executable_query
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (item : NamedFiniteClosureOptimalWorkloadItem coverage domain env runtimeRel)
    (_hitem : item ∈ C.finiteWorkload.items)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env item.item.cert.best.selected ↔
      row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
        item.item.query := by
  have hresult :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
          domain env item.item.cert.best.selected =
        FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel
          item.item.query :=
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result_eq_evalFinset
      domain env runtimeRel C.finiteWorkload.domainCoversEnv item.item.query
      item.item.cert.best.selected
  rw [hresult]

/-- THEOREM 5: the selected workload warm cost is bounded by the sum of the
original structural warm bounds. -/
theorem selected_workload_cost_le_structural_bound
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel) :
    NamedFiniteClosureOptimalWorkload.closureSelectedCostList
        C.finiteWorkload.items ≤
      NamedFiniteBestWorkload.originalBoundList
        (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems
          C.finiteWorkload.items) :=
  C.finiteWorkload.selectedCost_le_originalBoundList

/-- THEOREM 6: one shared cold materialization cost preserves the structural
workload envelope. -/
theorem cold_then_selected_cost_le_cold_plus_structural_bound
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (coldCost : Nat) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.finiteWorkload.items ≤
      coldCost +
        NamedFiniteBestWorkload.originalBoundList
          (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems
            C.finiteWorkload.items) :=
  C.finiteWorkload.coldThenSelectedCost_le_cold_plus_originalBoundList
    coldCost

/-- THEOREM 7: if the cold materialization cost is allocated across the
workload, the selected plans satisfy the amortized structural envelope. -/
theorem amortized_workload_cost_bound
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (coldCost allowance : Nat)
    (hcold : coldCost ≤ C.finiteWorkload.items.length * allowance) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.finiteWorkload.items ≤
      C.finiteWorkload.items.length * allowance +
        NamedFiniteBestWorkload.originalBoundList
          (NamedFiniteClosureOptimalWorkload.toBestWorkloadItems
            C.finiteWorkload.items) :=
  C.finiteWorkload.coldThenSelectedCost_le_length_allowance_plus_originalBoundList
    coldCost allowance hcold

/-- THEOREM 8: product closure optimality compares the selected workload to any
same-shape alternative cost vector that componentwise dominates the selected
candidate costs. -/
theorem selected_cost_le_same_shape_alternative
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (costs : List Nat)
    (h :
      NamedFiniteClosureOptimalWorkload.ProductAlternativeCostDominates
        (coverage := coverage) (domain := domain) (env := env)
        (runtimeRel := runtimeRel) C.finiteWorkload.items costs) :
    NamedFiniteClosureOptimalWorkload.closureSelectedCostList
        C.finiteWorkload.items ≤
      NamedFiniteClosureOptimalWorkload.alternativeCostList costs :=
  C.finiteWorkload.selectedCost_le_alternativeCostList costs h

/-- THEOREM 9: adding the same cold materialization cost preserves product
closure optimality against a same-shape alternative workload. -/
theorem cold_then_selected_cost_le_same_shape_alternative
    (C :
      AtomFieldGenerativeQueryAlgebraCertificate coverage domain env
        runtimeRel)
    (coldCost : Nat)
    (costs : List Nat)
    (h :
      NamedFiniteClosureOptimalWorkload.ProductAlternativeCostDominates
        (coverage := coverage) (domain := domain) (env := env)
        (runtimeRel := runtimeRel) C.finiteWorkload.items costs) :
    NamedFiniteClosureOptimalWorkload.coldThenClosureSelectedCost coldCost
        C.finiteWorkload.items ≤
      NamedFiniteClosureOptimalWorkload.coldThenAlternativeCost coldCost
        costs :=
  C.finiteWorkload.coldThenSelectedCost_le_coldThenAlternativeCost
    coldCost costs h

end AtomFieldGenerativeQueryAlgebraCertificate

/-!
  Summary:
  - P180 is the first-layer query algebra closeout: for the finite named
    atom/field generator fragment, syntax, denotation, executable
    materialization, rewrite selection, and workload complexity are one
    certificate surface.

  Boundary:
  - This remains certificate-relative and finite/materialized.  It does not
    prove unrestricted relational completeness, recursion, external source-open
    latency, or cross-query common-subplan sharing.
-/


end SaturationMonoid

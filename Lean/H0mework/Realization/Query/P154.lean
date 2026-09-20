/-
  Proposition 154: one finite query-theory certificate.

  The first-layer database gap has two parts:

    * query algebra / calculus / runtime-plan expressiveness;
    * executable denotation and finite rewrite-cost control.

  P129 packages the named finite database certificate, P132 proves the exact
  Bool/Prop denotation bridge for whole finite plans, and P145 proves the
  rewrite-closure optimizer theorem under a dominance-complete candidate
  enumeration.  This file packages those three surfaces into one certificate
  so downstream documents can cite a single theorem instead of a scattered
  list of plumbing lemmas.

  Boundary: this is still certificate-relative.  It does not construct the
  runtime relation bridge, the materialized finite domain, or the complete
  candidate enumeration; it proves what follows once those mechanism-
  faithfulness certificates exist.
-/

import H0mework.Realization.QueryPlans.P132
import H0mework.Realization.QueryPlans.P145

/-! ## One certificate for finite query completeness plus finite cost control -/

/-- A finite, named, agent-native database slice with:

* exact executable-vs-named denotation;
* named runtime/Kleisli/calculus mutual completeness;
* warm/amortized execution bounds;
* rewrite-closure optimality for the selected finite candidate.
-/
structure NamedFiniteQueryTheoryCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (coldCost allowance n : Nat)
    (candidates :
      List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel q)) where
  database :
    NamedFiniteGenerativeDatabaseCertificate coverage domain env runtimeRel
      budget q coldCost allowance n
  closureOptimal :
    NamedFiniteRewriteClosureOptimalCertificate coverage domain env runtimeRel
      q candidates

namespace NamedFiniteQueryTheoryCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
variable {coldCost allowance n : Nat}
variable {candidates :
  List (FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
    (Row := Row) (Base := Base)
    (RuntimeGen := AippocampusRuntimeGenerator)
    domain runtimeRel q)}

/-! ## Denotation and expressiveness -/

/-- THEOREM 1: executable finite membership is exactly named runtime-plan
denotation for the compiled finite query. -/
theorem finite_eval_iff_named_runtime_eval
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row :=
  C.database.finite_eval_iff_named_runtime_eval row

/-- THEOREM 2: the named runtime/Kleisli/calculus mutual-completeness theorem
is exposed by the combined certificate. -/
theorem named_mutual_completeness
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates) :
    (forall p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists alg : KleisliFieldAlg Row Base,
        forall row,
          KleisliFieldAlg.eval (finiteRuntimeEnvProp env) alg row <->
            RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row) /\
    (forall alg : KleisliFieldAlg Row Base,
      exists p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row <->
            KleisliFieldAlg.eval (finiteRuntimeEnvProp env) alg row) /\
    (forall p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists formula : KleisliFieldCalc Row Base,
        forall row,
          KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row <->
            RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row) /\
    (forall formula : KleisliFieldCalc Row Base,
      exists p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
              coverage.runtimeRel p row <->
            KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row) :=
  C.database.named_mutual_completeness

/-! ## Finite cost control -/

/-- THEOREM 3: the finite warm path keeps the P123 repeated-execution bound. -/
theorem repeated_warm_bound
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates) :
    FiniteRuntimeGenerativePlan.coldThenWarmCost coldCost n domain env
        runtimeRel q <=
      coldCost + n *
        FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel q :=
  C.database.repeated_warm_bound

/-- THEOREM 4: after allocating cold materialization across `n` repetitions,
the combined certificate exposes the amortized finite-query bound. -/
theorem amortized_bound
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates)
    (hcold : coldCost <= n * allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmCost coldCost n domain env
        runtimeRel q <=
      n * (allowance +
        FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel q) :=
  C.database.amortized_bound hcold

/-! ## Rewrite-closure optimization -/

/-- THEOREM 5: the selected rewrite candidate denotes exactly the named
runtime query. -/
theorem selected_eval_iff_named
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates)
    (row : Row) :
    row ∈ FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.result
        domain env C.closureOptimal.namedBest.best.selected <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel
        (finiteRuntimePlanToRuntimePlan domain q) row :=
  C.closureOptimal.selected_eval_iff_named row

/-- THEOREM 6: the selected rewrite candidate is cost-optimal over every
candidate in the rewrite-chain closure, assuming the candidate enumeration
completeness certificate from P145. -/
theorem selected_cost_le_any_rewrite_candidate
    (C : NamedFiniteQueryTheoryCertificate coverage domain env runtimeRel
      budget q coldCost allowance n candidates)
    (candidate :
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate
        (Row := Row) (Base := Base)
        (RuntimeGen := AippocampusRuntimeGenerator)
        domain runtimeRel q) :
    FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env C.closureOptimal.namedBest.best.selected <=
      FiniteRuntimeGenerativePlan.WarmRewriteChainCandidate.cost
        domain env candidate :=
  C.closureOptimal.selected_cost_le_any_rewrite_candidate candidate

end NamedFiniteQueryTheoryCertificate

/-!
  Summary:
  - P154 gives one finite query-theory handle for the current first-layer
    results: named algebra/calculus expressiveness, exact executable denotation,
    amortized finite execution bounds, and rewrite-closure optimality.
  - The theorem is intentionally certificate-relative.  The runtime still owes
    the relation bridge, finite materialized-domain coverage, and complete
    rewrite-candidate enumeration before this can be claimed for production.
-/

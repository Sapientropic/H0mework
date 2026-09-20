/-
  Proposition 111: closed named query-layer certificate.

  The objective-level worry was that the agent-native database still lacked
  two Codd-style pieces:

    * a completeness theorem for generative atom-field queries;
    * a complexity theorem for on-the-fly field interference.

  Earlier modules proved those pieces in separate slices:

    * P61: covered runtime plans, Kleisli atom-field algebra, and
      range-restricted calculus are mutually expressive;
    * P62/P79: finite/runtime/stateful workloads have explicit structural and
      amortized bounds;
    * P96: the current AIppocampus named generator basis
      (score fusion / authority / gluing) inherits those facts when each
      surface supplies coverage;
    * P109/P110: projection-visible read guards have finite executable costs
      once the semantic projection supplies the atom oracle.

  This file packages the first three into one closed-layer certificate.  It is
  deliberately conditional on the mechanism-faithfulness inputs that cannot be
  proved by query algebra alone: named generator coverage, finite
  materialization, and explicit external/shared budgets.

  Boundary: this is not a new optimizer, and it does not prove that production
  code has supplied faithful coverage/materialization.  It proves that once
  those certificates are supplied, there is no remaining query-algebra
  completeness or finite workload complexity debt in the current named
  generator layer.
-/

import H0mework.Realization.QueryPlans.P96
import H0mework.Realization.QueryPlans.P62
import H0mework.Realization.QuerySupport.P110

/-! ## Inputs required to close the current named query layer -/

/-- All mechanism-faithfulness and finite-domain inputs needed to close the
current named AIppocampus query layer.

The shape is intentionally explicit: coverage and materialization are not
hidden inside the algebra.  If production cannot supply one of these fields,
the closed-layer theorem simply does not apply. -/
structure NamedQueryLayerInputs
    (Declared Row Base State : Type*) [DecidableEq Row] [DecidableEq State]
    where
  coverage : AippocampusNamedGeneratorCoverage Declared Row
  denotationEnv : Base -> Row -> Prop
  finiteDomain : Finset Row
  finiteEnv : Base -> Finset Row
  finiteRuntimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool
  externalBudget : ExternalOracleBudget Row Base
  finiteEnvCovered : forall b, finiteEnv b ⊆ finiteDomain
  sharedCost : Nat
  finiteRuntimeWorkload :
    List (FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
  stateDomain : Finset State
  rowDomain : Finset Row
  statefulEnv :
    AippocampusRuntimeGenerator -> State -> Finset (Row × State)
  statefulEnvCovered :
    forall p x,
      statefulEnv p x ⊆
        FiniteStatefulGenAlg.pairDomain stateDomain rowDomain
  rowCovered : forall row, row ∈ rowDomain
  stateCovered : forall x, x ∈ stateDomain
  finiteStatefulWorkload :
    List (FiniteStatefulWorkItem State Row AippocampusRuntimeGenerator)

/-! ## Closed-layer output certificate -/

/-- A single certificate that the current named query layer is closed on both
the denotational/completeness side and the finite workload complexity side. -/
structure ClosedNamedQueryLayerCertificate
    {Declared Row Base State : Type*} [DecidableEq Row] [DecidableEq State]
    (I : NamedQueryLayerInputs Declared Row Base State) where
  mutualCompleteness :
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists alg : KleisliFieldAlg Row Base,
        forall row,
          KleisliFieldAlg.eval I.denotationEnv alg row <->
            RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row) /\
    (forall alg : KleisliFieldAlg Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row <->
            KleisliFieldAlg.eval I.denotationEnv alg row) /\
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists formula : KleisliFieldCalc Row Base,
        forall row,
          KleisliFieldCalc.eval I.denotationEnv formula row <->
            RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row) /\
    (forall formula : KleisliFieldCalc Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row <->
            KleisliFieldCalc.eval I.denotationEnv formula row)
  runtimeRoundtrip :
    forall (q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
      (row : Row),
      RuntimeGenerativePlan.eval I.denotationEnv I.coverage.runtimeRel
          (kleisliAlgToRuntimePlan
            (runtimePlanToKleisli
              I.coverage.toRuntimeGeneratorCoverage q)) row <->
        RuntimeGenerativePlan.eval I.denotationEnv I.coverage.runtimeRel q row
  finiteRuntimeWorkloadCost :
    FiniteRuntimeWorkloadCostCertificate I.sharedCost I.finiteDomain
      I.finiteEnv I.finiteRuntimeRel I.externalBudget
      I.finiteRuntimeWorkload
  finiteStatefulWorkloadCost :
    FiniteStatefulWorkloadCostCertificate I.sharedCost I.stateDomain
      I.rowDomain I.statefulEnv I.finiteStatefulWorkload

/-- THEOREM 1: coverage + finite materialization + explicit budgets close the
current named query layer. -/
theorem closedNamedQueryLayerCertificate
    {Declared Row Base State : Type*} [DecidableEq Row] [DecidableEq State]
    (I : NamedQueryLayerInputs Declared Row Base State) :
    ClosedNamedQueryLayerCertificate I where
  mutualCompleteness :=
    I.coverage.named_runtime_kleisli_calc_mutual_completeness
      I.denotationEnv
  runtimeRoundtrip := by
    intro q row
    exact I.coverage.named_runtime_kleisli_runtime_roundtrip_sound
      I.denotationEnv q row
  finiteRuntimeWorkloadCost :=
    finiteRuntimeWorkloadCostCertificate I.sharedCost I.finiteDomain
      I.finiteEnv I.finiteRuntimeRel I.externalBudget I.finiteEnvCovered
      I.finiteRuntimeWorkload
  finiteStatefulWorkloadCost :=
    namedFiniteStatefulWorkloadCostCertificate I.sharedCost I.stateDomain
      I.rowDomain I.statefulEnv I.statefulEnvCovered I.rowCovered
      I.stateCovered I.finiteStatefulWorkload

namespace ClosedNamedQueryLayerCertificate

variable {Declared Row Base State : Type*} [DecidableEq Row] [DecidableEq State]
variable {I : NamedQueryLayerInputs Declared Row Base State}

/-- THEOREM 2: the closed-layer certificate exposes Codd-style mutual
expressibility for the named generative query fragment. -/
theorem completeness
    (C : ClosedNamedQueryLayerCertificate I) :
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists alg : KleisliFieldAlg Row Base,
        forall row,
          KleisliFieldAlg.eval I.denotationEnv alg row <->
            RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row) /\
    (forall alg : KleisliFieldAlg Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row <->
            KleisliFieldAlg.eval I.denotationEnv alg row) /\
    (forall q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
      exists formula : KleisliFieldCalc Row Base,
        forall row,
          KleisliFieldCalc.eval I.denotationEnv formula row <->
            RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row) /\
    (forall formula : KleisliFieldCalc Row Base,
      exists q : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator,
        forall row,
          RuntimeGenerativePlan.eval I.denotationEnv
              I.coverage.runtimeRel q row <->
            KleisliFieldCalc.eval I.denotationEnv formula row) :=
  C.mutualCompleteness

/-- THEOREM 3: every finite runtime workload in the closed layer inherits the
division-free amortized cost certificate from P62. -/
theorem runtimeWorkloadCost
    (C : ClosedNamedQueryLayerCertificate I) :
    FiniteRuntimeWorkloadCostCertificate I.sharedCost I.finiteDomain
      I.finiteEnv I.finiteRuntimeRel I.externalBudget
      I.finiteRuntimeWorkload :=
  C.finiteRuntimeWorkloadCost

/-- THEOREM 4: every finite stateful workload in the closed layer inherits the
stateful read/generate/write workload cost certificate from P79/P96. -/
theorem statefulWorkloadCost
    (C : ClosedNamedQueryLayerCertificate I) :
    FiniteStatefulWorkloadCostCertificate I.sharedCost I.stateDomain
      I.rowDomain I.statefulEnv I.finiteStatefulWorkload :=
  C.finiteStatefulWorkloadCost

end ClosedNamedQueryLayerCertificate

/-!
  Summary:
  - For the current named AIppocampus generator basis, the query layer is
    mathematically closed once three explicit inputs are present:
    per-surface generator coverage, finite materialization, and external/shared
    cost budgets.
  - Completeness is the P61/P96 three-way runtime/Kleisli/calculus theorem.
  - Complexity is the P62/P79 finite workload bound, carried here for both
    runtime-shaped generative plans and stateful read/generate/write plans.
  - P110 remains the read-guard specialization: projection-visible obligations
    get a canonical atom oracle and exact Boolean AST node-count cost.

  Remaining boundary:
  - This theorem deliberately does not prove that production runtime code has
    supplied the coverage/materialization certificates.
  - It does not cover source-schema joins, aggregation, recursion, unrestricted
    quantification, cache replacement policy, or probabilistic average-case
    optimization.
-/

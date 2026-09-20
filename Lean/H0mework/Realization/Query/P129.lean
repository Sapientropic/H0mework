/-
  Proposition 129: named finite generative database certificate.

  P96 closes the named-generator side: the current AIppocampus runtime
  generator basis (score fusion / authority / gluing) inherits the
  runtime/Kleisli/calculus completeness theorem once each surface supplies a
  coverage certificate.

  P123 closes the finite/materialized database side: a finite executable
  runtime plan has denotational completeness, executable warm-path cost, and
  explicit cold-cost amortization once base materialization is domain-covered.

  This file packages those two certificates together and names the remaining
  mechanism-faithfulness seam.  The seam is real: P96 is Prop-valued and
  coverage-facing, while P123 is finite/Bool-valued and executable.  The runtime
  therefore owes an explicit bridge saying that the executable finite
  transition relation is exactly the named coverage relation on this
  materialized slice.

  Boundary: this is not a production proof for score fusion, authority, or
  gluing by itself.  It is the theorem those production certificates plug into.
-/

import H0mework.Realization.Query.P111
import H0mework.Realization.QueryPlans.P123

/-! ## Bool/Prop materialization bridge for the named runtime basis -/

/-- The mechanism-faithfulness bridge from executable finite Boolean
transitions to the named Prop-valued runtime relation.

`finiteRuntimeRelProp` already includes the materialized-domain guard on the
target row.  This certificate says that guarded executable relation is
extensionally the same relation as the named coverage relation used by the
query algebra. -/
structure NamedFiniteRuntimeRelationBridge
    {Declared Row : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool) where
  relates_exactly :
    forall generator source target,
      finiteRuntimeRelProp domain runtimeRel generator source target <->
        coverage.runtimeRel generator source target

namespace NamedFiniteRuntimeRelationBridge

variable {Declared Row : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}

/-- THEOREM 1: the bridge exposes executable-to-named soundness. -/
theorem executable_sound
    (B : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h :
      finiteRuntimeRelProp domain runtimeRel generator source target) :
    coverage.runtimeRel generator source target :=
  (B.relates_exactly generator source target).mp h

/-- THEOREM 2: the bridge exposes named-to-executable completeness on the
materialized slice. -/
theorem executable_complete
    (B : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : coverage.runtimeRel generator source target) :
    finiteRuntimeRelProp domain runtimeRel generator source target :=
  (B.relates_exactly generator source target).mpr h

end NamedFiniteRuntimeRelationBridge

/-! ## One named finite/materialized database certificate -/

/-- A single certificate for one finite plan over the named AIppocampus
runtime generator basis.

It contains:
* the executable finite/materialized database certificate from P123;
* the named runtime/Kleisli/calculus completeness theorem from P96;
* the named runtime -> Kleisli -> runtime roundtrip theorem from P96;
* the Bool/Prop relation bridge that production code must supply.
-/
structure NamedFiniteGenerativeDatabaseCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (coldCost allowance n : Nat) where
  relationBridge :
    NamedFiniteRuntimeRelationBridge coverage domain runtimeRel
  finiteDb :
    FiniteRuntimeGenerativePlan.FiniteGenerativeDatabaseCertificate
      domain env runtimeRel budget q coldCost allowance n
  namedCompleteness :
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
            KleisliFieldCalc.eval (finiteRuntimeEnvProp env) formula row)
  namedRoundtrip :
    forall (p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
      (row : Row),
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env) coverage.runtimeRel
          (kleisliAlgToRuntimePlan
            (runtimePlanToKleisli
              coverage.toRuntimeGeneratorCoverage p)) row <->
        RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
          coverage.runtimeRel p row

/-- THEOREM 3: coverage + finite materialization + the explicit Bool/Prop
relation bridge give the named finite/materialized database certificate. -/
def namedFiniteGenerativeDatabaseCertificate
    {Declared Row Base : Type*} [DecidableEq Row]
    (coverage : AippocampusNamedGeneratorCoverage Declared Row)
    (domain : Finset Row)
    (env : Base -> Finset Row)
    (runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (bridge : NamedFiniteRuntimeRelationBridge coverage domain runtimeRel)
    (q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (coldCost allowance n : Nat) :
    NamedFiniteGenerativeDatabaseCertificate coverage domain env runtimeRel
      budget q coldCost allowance n where
  relationBridge := bridge
  finiteDb :=
    FiniteRuntimeGenerativePlan.finiteGenerativeDatabaseCertificate
      domain env runtimeRel budget hEnv q coldCost allowance n
  namedCompleteness :=
    coverage.named_runtime_kleisli_calc_mutual_completeness
      (finiteRuntimeEnvProp env)
  namedRoundtrip := by
    intro p row
    exact coverage.named_runtime_kleisli_runtime_roundtrip_sound
      (finiteRuntimeEnvProp env) p row

namespace NamedFiniteGenerativeDatabaseCertificate

variable {Declared Row Base : Type*} [DecidableEq Row]
variable {coverage : AippocampusNamedGeneratorCoverage Declared Row}
variable {domain : Finset Row}
variable {env : Base -> Finset Row}
variable {runtimeRel : AippocampusRuntimeGenerator -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {q : FiniteRuntimeGenerativePlan Row Base AippocampusRuntimeGenerator}
variable {coldCost allowance n : Nat}

/-- THEOREM 4: finite executable Kleisli completeness remains available from
the named finite certificate. -/
theorem finite_kleisli_complete
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (row : Row) :
    KleisliFieldAlg.eval (finiteRuntimeEnvProp env)
        C.finiteDb.completenessCost.kleisliAlg row <->
      row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  C.finiteDb.kleisli_complete row

/-- THEOREM 5: finite executable calculus completeness remains available from
the named finite certificate. -/
theorem finite_calc_complete
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (row : Row) :
    KleisliFieldCalc.eval (finiteRuntimeEnvProp env)
        C.finiteDb.completenessCost.calcFormula row <->
      row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  C.finiteDb.calc_complete row

/-- THEOREM 6: the finite warm path keeps the P123 repeated-execution bound. -/
theorem repeated_warm_bound
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n) :
    FiniteRuntimeGenerativePlan.coldThenWarmCost coldCost n domain env
        runtimeRel q <=
      coldCost + n *
        FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel q :=
  C.finiteDb.repeated_warm_bound

/-- THEOREM 7: the finite warm path keeps the P123 amortized bound when the
cold materialization cost is allocated across the requested repetitions. -/
theorem amortized_bound
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (hcold : coldCost <= n * allowance) :
    FiniteRuntimeGenerativePlan.coldThenWarmCost coldCost n domain env
        runtimeRel q <=
      n * (allowance +
        FiniteRuntimeGenerativePlan.warmWorkBound domain runtimeRel q) :=
  C.finiteDb.amortized_bound hcold

/-- THEOREM 8: the named generator layer still has runtime/Kleisli/calculus
mutual completeness under the finite environment. -/
theorem named_mutual_completeness
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n) :
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
  C.namedCompleteness

/-- THEOREM 9: the named runtime -> Kleisli -> runtime roundtrip is exposed by
the named finite certificate. -/
theorem named_runtime_roundtrip
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    (p : RuntimeGenerativePlan Row Base AippocampusRuntimeGenerator)
    (row : Row) :
    RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env) coverage.runtimeRel
        (kleisliAlgToRuntimePlan
          (runtimePlanToKleisli
            coverage.toRuntimeGeneratorCoverage p)) row <->
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        coverage.runtimeRel p row :=
  C.namedRoundtrip p row

/-- THEOREM 10: executable finite runtime transitions are sound for the named
coverage relation. -/
theorem executable_transition_sound
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h :
      finiteRuntimeRelProp domain runtimeRel generator source target) :
    coverage.runtimeRel generator source target :=
  C.relationBridge.executable_sound h

/-- THEOREM 11: named coverage transitions are complete for the executable
finite relation on this materialized slice. -/
theorem executable_transition_complete
    (C : NamedFiniteGenerativeDatabaseCertificate coverage domain env
      runtimeRel budget q coldCost allowance n)
    {generator : AippocampusRuntimeGenerator} {source target : Row}
    (h : coverage.runtimeRel generator source target) :
    finiteRuntimeRelProp domain runtimeRel generator source target :=
  C.relationBridge.executable_complete h

end NamedFiniteGenerativeDatabaseCertificate

/-!
  Summary:
  - P129 combines P96's named generator completeness with P123's finite
    generative database certificate.
  - The production-facing seam is explicit and small:
    `NamedFiniteRuntimeRelationBridge` must prove that finite executable Bool
    transitions match the named Prop-valued coverage relation.
  - Once that bridge is supplied, a single certificate exposes finite
    Kleisli/calculus completeness, repeated warm-path cost, cold-cost
    amortization, named runtime/Kleisli/calculus mutual completeness, and named
    runtime roundtrip.

  Remaining boundary:
  - This is still relative to coverage/materialization/source/model
    certificates.  It does not cover source-schema joins, aggregation,
    recursion, unrestricted quantification, cache freshness, or empirical
    average-case optimizer behavior.
-/

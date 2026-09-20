/-
  Proposition 49: finite executable runtime plans have one denotational,
  Kleisli/calculus, and cost certificate.

  Proposition 38 proves the denotational/runtime-generator bridge for
  `RuntimeGenerativePlan`.  Proposition 47 proves the finite executable cost
  bridge for `FiniteRuntimeGenerativePlan`.  This file welds those two surfaces:

    finite executable runtime plan
      -> domain-restricted denotational runtime plan
      -> covered Kleisli/generative algebra
      -> range-restricted calculus
      -> finite total-cost certificate.

  This is still not a Codd-sized theorem for arbitrary source tables, joins,
  aggregation, recursion, or unrestricted quantification.  It is the closed
  finite/materialized fragment needed by the current runtime shape: every
  executable finite runtime plan is simultaneously denotationally expressible
  and cost-certified, with all external/model/materialization work remaining
  explicit in the `ExternalOracleBudget`.
-/

import H0mework.Realization.QueryPlans.P38
import H0mework.Realization.QueryPlans.P47

/-! ## Finite executable semantics as a denotational runtime plan -/

/-- Turn a finite base environment into a Prop-valued environment. -/
def finiteRuntimeEnvProp {Row Base : Type*} [DecidableEq Row]
    (env : Base -> Finset Row) : Base -> Row -> Prop :=
  fun b row => row ∈ env b

/-- Turn a finite Boolean runtime generator into a Prop-valued relation,
restricted to the materialized finite domain on the target side. -/
def finiteRuntimeRelProp {Row RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    RuntimeGen -> Row -> Row -> Prop :=
  fun generator source target =>
    target ∈ domain /\ runtimeRel generator source target = true

/-- Compile a finite executable runtime plan to a denotational runtime plan.

The only nontrivial case is `top`: finite `top` means "the materialized finite
domain", while denotational `top` means all rows.  We therefore compile finite
`top` as a domain selection over denotational `top`.  Runtime `generate` can
then use the domain-restricted relation above. -/
def finiteRuntimePlanToRuntimePlan {Row Base RuntimeGen : Type*}
    [DecidableEq Row] (domain : Finset Row) :
    FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      RuntimeGenerativePlan Row Base RuntimeGen
  | FiniteRuntimeGenerativePlan.empty => RuntimeGenerativePlan.empty
  | FiniteRuntimeGenerativePlan.top =>
      RuntimeGenerativePlan.select (fun row => row ∈ domain)
        RuntimeGenerativePlan.top
  | FiniteRuntimeGenerativePlan.base b => RuntimeGenerativePlan.base b
  | FiniteRuntimeGenerativePlan.union p q =>
      RuntimeGenerativePlan.union
        (finiteRuntimePlanToRuntimePlan domain p)
        (finiteRuntimePlanToRuntimePlan domain q)
  | FiniteRuntimeGenerativePlan.inter p q =>
      RuntimeGenerativePlan.inter
        (finiteRuntimePlanToRuntimePlan domain p)
        (finiteRuntimePlanToRuntimePlan domain q)
  | FiniteRuntimeGenerativePlan.diff p q =>
      RuntimeGenerativePlan.diff
        (finiteRuntimePlanToRuntimePlan domain p)
        (finiteRuntimePlanToRuntimePlan domain q)
  | FiniteRuntimeGenerativePlan.select predicate q =>
      RuntimeGenerativePlan.select (fun row => predicate row = true)
        (finiteRuntimePlanToRuntimePlan domain q)
  | FiniteRuntimeGenerativePlan.generate generator q =>
      RuntimeGenerativePlan.generate generator
        (finiteRuntimePlanToRuntimePlan domain q)
  | FiniteRuntimeGenerativePlan.bind q k =>
      RuntimeGenerativePlan.bind
        (finiteRuntimePlanToRuntimePlan domain q)
        (fun source => finiteRuntimePlanToRuntimePlan domain (k source))

/-- THEOREM 1: the domain-restricted denotational runtime plan has exactly the
same result set as the finite executable runtime plan. -/
theorem finiteRuntimePlanToRuntimePlan_sound
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    forall q : FiniteRuntimeGenerativePlan Row Base RuntimeGen,
      forall row,
        row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q <->
          RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
            (finiteRuntimeRelProp domain runtimeRel)
            (finiteRuntimePlanToRuntimePlan domain q) row := by
  intro q
  induction q with
  | empty =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan]
  | top =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan]
  | base b =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan,
        finiteRuntimeEnvProp]
  | union p q ihp ihq =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan,
        ihp row, ihq row]
  | inter p q ihp ihq =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan,
        ihp row, ihq row]
  | diff p q ihp ihq =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan,
        ihp row, ihq row]
  | select predicate q ih =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan, ih row,
        and_comm]
  | generate generator q ih =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan,
        finiteRuntimeRelProp, ih]
  | bind q k ihq ihk =>
      intro row
      simp [FiniteRuntimeGenerativePlan.evalFinset,
        RuntimeGenerativePlan.eval, finiteRuntimePlanToRuntimePlan, ihq, ihk]

/-! ## Covered generator certificate for finite executable plans -/

/-- The identity coverage certificate for a finite runtime relation after it is
viewed as a domain-restricted Prop-valued relation. -/
def finiteRuntimeGeneratorCoverage {Row RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    RuntimeGeneratorCoverage RuntimeGen RuntimeGen Row where
  toDeclared := id
  runtimeRel := finiteRuntimeRelProp domain runtimeRel
  declaredRel := finiteRuntimeRelProp domain runtimeRel
  covers := by
    intro _generator _source _target
    rfl

/-- A single certificate for the finite executable runtime plan, its
denotational runtime plan, its Kleisli/calculus translations, and its finite
cost bound. -/
structure FiniteRuntimeCompletenessCostCertificate
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) where
  runtimePlan : RuntimeGenerativePlan Row Base RuntimeGen
  runtime_eval_iff_finite :
    forall row,
      RuntimeGenerativePlan.eval (finiteRuntimeEnvProp env)
        (finiteRuntimeRelProp domain runtimeRel) runtimePlan row <->
          row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q
  kleisliAlg : KleisliFieldAlg Row Base
  kleisli_eval_iff_finite :
    forall row,
      KleisliFieldAlg.eval (finiteRuntimeEnvProp env) kleisliAlg row <->
        row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q
  calcFormula : KleisliFieldCalc Row Base
  calc_eval_iff_finite :
    forall row,
      KleisliFieldCalc.eval (finiteRuntimeEnvProp env) calcFormula row <->
        row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q
  finiteCost :
    FiniteRuntimeGenerativeCostCertificate domain env runtimeRel budget q

/-- THEOREM 2: every finite executable runtime plan has a combined
completeness-and-cost certificate, once primitive base relations are inside the
materialized finite domain for the cost/subset part. -/
def finiteRuntimeCompletenessCostCertificate
    {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q where
  runtimePlan := finiteRuntimePlanToRuntimePlan domain q
  runtime_eval_iff_finite := by
    intro row
    exact (finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel q row).symm
  kleisliAlg :=
    runtimePlanToKleisli
      (finiteRuntimeGeneratorCoverage domain runtimeRel)
      (finiteRuntimePlanToRuntimePlan domain q)
  kleisli_eval_iff_finite := by
    intro row
    exact
      (runtimePlanToKleisli_sound
        (finiteRuntimeGeneratorCoverage domain runtimeRel)
        (finiteRuntimeEnvProp env)
        (finiteRuntimePlanToRuntimePlan domain q) row).trans
        ((finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel q row).symm)
  calcFormula :=
    kleisliAlgToCalc
      (runtimePlanToKleisli
        (finiteRuntimeGeneratorCoverage domain runtimeRel)
        (finiteRuntimePlanToRuntimePlan domain q))
  calc_eval_iff_finite := by
    intro row
    exact
      (kleisliAlgToCalc_sound (finiteRuntimeEnvProp env)
        (runtimePlanToKleisli
          (finiteRuntimeGeneratorCoverage domain runtimeRel)
          (finiteRuntimePlanToRuntimePlan domain q)) row).trans
        ((runtimePlanToKleisli_sound
          (finiteRuntimeGeneratorCoverage domain runtimeRel)
          (finiteRuntimeEnvProp env)
          (finiteRuntimePlanToRuntimePlan domain q) row).trans
          ((finiteRuntimePlanToRuntimePlan_sound domain env runtimeRel q row).symm))
  finiteCost :=
    finiteRuntimeGenerativeCostCertificate domain env runtimeRel budget hEnv q

namespace FiniteRuntimeCompletenessCostCertificate

variable {Row Base RuntimeGen : Type*} [DecidableEq Row]
variable {domain : Finset Row} {env : Base -> Finset Row}
variable {runtimeRel : RuntimeGen -> Row -> Row -> Bool}
variable {budget : ExternalOracleBudget Row Base}
variable {q : FiniteRuntimeGenerativePlan Row Base RuntimeGen}

/-- THEOREM 3: the certificate's Kleisli query is extensionally the original
finite executable runtime plan. -/
theorem kleisli_complete
    (C : FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q)
    (row : Row) :
    KleisliFieldAlg.eval (finiteRuntimeEnvProp env) C.kleisliAlg row <->
      row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  C.kleisli_eval_iff_finite row

/-- THEOREM 4: the certificate's calculus formula is extensionally the original
finite executable runtime plan. -/
theorem calc_complete
    (C : FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q)
    (row : Row) :
    KleisliFieldCalc.eval (finiteRuntimeEnvProp env) C.calcFormula row <->
      row ∈ FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  C.calc_eval_iff_finite row

/-- THEOREM 5: the finite cost certificate inside the combined certificate
keeps Proposition 39's explicit total-work bound. -/
theorem cost_le_totalWorkBound
    (C : FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q) :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
      C.finiteCost.alg).2 ≤
        FiniteKleisliFieldAlg.totalWorkBound domain budget C.finiteCost.alg :=
  C.finiteCost.cost_le_totalWorkBound

/-- THEOREM 6: the total-cost evaluator inside the combined certificate returns
the original finite executable runtime result. -/
theorem total_cost_result_eq
    (C : FiniteRuntimeCompletenessCostCertificate domain env runtimeRel budget q) :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
      C.finiteCost.alg).1 =
        FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
  C.finiteCost.total_result_eq

end FiniteRuntimeCompletenessCostCertificate

/-!
  Summary:
  - `finiteRuntimePlanToRuntimePlan_sound` is the missing finite-to-denotational
    bridge: finite executable semantics equals domain-restricted runtime-plan
    semantics.
  - `finiteRuntimeCompletenessCostCertificate` packages that bridge with
    Proposition 38's Kleisli/calculus expressibility and Proposition 47's
    finite cost certificate.
  - This closes the current finite/materialized runtime-query slice.  The
    remaining Codd-scale debt is broader: schemas, source joins, aggregation,
    recursion, unrestricted quantification, cache amortization, and the cost of
    producing the materialized domain still need separate theorems.
-/

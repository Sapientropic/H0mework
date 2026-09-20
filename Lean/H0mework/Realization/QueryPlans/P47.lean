/-
  Proposition 47: finite runtime generative query cost bridge.

  Proposition 30 proves denotational completeness for the Kleisli/generative
  atom-field query language.  Proposition 38 says runtime generators are covered
  when they are represented by declared relations.  Propositions 31 and 39 give
  finite-domain structural and external-budget cost bounds for Kleisli queries.

  This file joins those threads for the executable finite/runtime surface:

    * define finite runtime generative plans with Boolean predicates and
      Boolean generator relations over a materialized finite domain;
    * compile each plan into the finite Kleisli algebra;
    * prove the compiled Kleisli query has exactly the same finite result set;
    * package the total-cost bound from Proposition 39 as a certificate for the
      original runtime plan.

  Boundary: the theorem assumes the finite domain, primitive finite relations,
  Boolean generator relation, and external budget are already supplied.  It is
  not an amortized cache theorem and does not price model proposal internally.
-/

import H0mework.Realization.QueryPlans.P39

/-! ## Finite executable runtime generative plans -/

/-- Executable runtime generative plans over a finite materialized domain.  This
is the runtime-shaped syntax: `generate` names an external generator relation,
while `bind` is the general query-as-generation operation. -/
inductive FiniteRuntimeGenerativePlan (Row Base RuntimeGen : Type*) where
  | empty
  | top
  | base : Base -> FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | union :
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | inter :
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | diff :
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | select :
      (Row -> Bool) ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | generate :
      RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen
  | bind :
      FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      (Row -> FiniteRuntimeGenerativePlan Row Base RuntimeGen) ->
      FiniteRuntimeGenerativePlan Row Base RuntimeGen

namespace FiniteRuntimeGenerativePlan

/-- Finite-set semantics for runtime generative plans.  `generate g q` evaluates
`q`, then scans the finite materialized domain with the Boolean generator
relation for every source row produced by `q`. -/
def evalFinset {Row Base RuntimeGen : Type*} [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    FiniteRuntimeGenerativePlan Row Base RuntimeGen -> Finset Row
  | empty => ∅
  | top => domain
  | base b => env b
  | union p q => evalFinset domain env runtimeRel p ∪
      evalFinset domain env runtimeRel q
  | inter p q => evalFinset domain env runtimeRel p ∩
      evalFinset domain env runtimeRel q
  | diff p q => evalFinset domain env runtimeRel p \
      evalFinset domain env runtimeRel q
  | select predicate q =>
      (evalFinset domain env runtimeRel q).filter
        (fun row => predicate row = true)
  | generate generator q =>
      (evalFinset domain env runtimeRel q).biUnion
        (fun source =>
          domain.filter (fun target => runtimeRel generator source target = true))
  | bind q k =>
      (evalFinset domain env runtimeRel q).biUnion
        (fun source => evalFinset domain env runtimeRel (k source))

end FiniteRuntimeGenerativePlan

/-! ## Compilation to finite Kleisli algebra -/

/-- Compile a finite runtime generative plan into the finite Kleisli algebra.
The runtime `generate` node is represented as a bind followed by a selection
over `top`, i.e. a domain scan with the generator relation. -/
def finiteRuntimePlanToKleisli {Row Base RuntimeGen : Type*}
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    FiniteRuntimeGenerativePlan Row Base RuntimeGen ->
      FiniteKleisliFieldAlg Row Base
  | FiniteRuntimeGenerativePlan.empty => FiniteKleisliFieldAlg.empty
  | FiniteRuntimeGenerativePlan.top => FiniteKleisliFieldAlg.top
  | FiniteRuntimeGenerativePlan.base b => FiniteKleisliFieldAlg.base b
  | FiniteRuntimeGenerativePlan.union p q =>
      FiniteKleisliFieldAlg.union
        (finiteRuntimePlanToKleisli runtimeRel p)
        (finiteRuntimePlanToKleisli runtimeRel q)
  | FiniteRuntimeGenerativePlan.inter p q =>
      FiniteKleisliFieldAlg.inter
        (finiteRuntimePlanToKleisli runtimeRel p)
        (finiteRuntimePlanToKleisli runtimeRel q)
  | FiniteRuntimeGenerativePlan.diff p q =>
      FiniteKleisliFieldAlg.diff
        (finiteRuntimePlanToKleisli runtimeRel p)
        (finiteRuntimePlanToKleisli runtimeRel q)
  | FiniteRuntimeGenerativePlan.select predicate q =>
      FiniteKleisliFieldAlg.select predicate
        (finiteRuntimePlanToKleisli runtimeRel q)
  | FiniteRuntimeGenerativePlan.generate generator q =>
      FiniteKleisliFieldAlg.bind
        (finiteRuntimePlanToKleisli runtimeRel q)
        (fun source =>
          FiniteKleisliFieldAlg.select
            (fun target => runtimeRel generator source target)
            FiniteKleisliFieldAlg.top)
  | FiniteRuntimeGenerativePlan.bind q k =>
      FiniteKleisliFieldAlg.bind
        (finiteRuntimePlanToKleisli runtimeRel q)
        (fun source => finiteRuntimePlanToKleisli runtimeRel (k source))

/-- THEOREM 1: compiling finite runtime plans to the finite Kleisli algebra
preserves finite denotation exactly. -/
theorem finiteRuntimePlanToKleisli_sound {Row Base RuntimeGen : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool) :
    forall q : FiniteRuntimeGenerativePlan Row Base RuntimeGen,
      FiniteKleisliFieldAlg.evalFinset domain env
          (finiteRuntimePlanToKleisli runtimeRel q) =
        FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q := by
  intro q
  induction q with
  | empty =>
      rfl
  | top =>
      rfl
  | base b =>
      rfl
  | union p q ihp ihq =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ihp, ihq]
  | inter p q ihp ihq =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ihp, ihq]
  | diff p q ihp ihq =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ihp, ihq]
  | select predicate q ih =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ih]
  | generate generator q ih =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ih]
  | bind q k ihq ihk =>
      simp [finiteRuntimePlanToKleisli, FiniteKleisliFieldAlg.evalFinset,
        FiniteRuntimeGenerativePlan.evalFinset, ihq, ihk]

/-! ## Cost bridge for runtime plans -/

/-- A finite runtime plan cost certificate: the original runtime-shaped plan is
represented by a finite Kleisli query with the same result, total-cost result
equality, a total work bound, and finite-domain containment. -/
structure FiniteRuntimeGenerativeCostCertificate {Row Base RuntimeGen : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) where
  alg : FiniteKleisliFieldAlg Row Base
  result_eq :
    FiniteKleisliFieldAlg.evalFinset domain env alg =
      FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q
  total_result_eq :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget alg).1 =
      FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q
  cost_le_totalWorkBound :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget alg).2 ≤
      FiniteKleisliFieldAlg.totalWorkBound domain budget alg
  result_subset_domain :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget alg).1 ⊆ domain

/-- THEOREM 2: every finite runtime generative plan has a Kleisli cost
certificate once primitive base relations stay inside the materialized domain.
The certificate's cost bound is exactly Proposition 39's external budget plus
structural Kleisli work bound, applied to the compiled runtime plan. -/
def finiteRuntimeGenerativeCostCertificate {Row Base RuntimeGen : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    FiniteRuntimeGenerativeCostCertificate domain env runtimeRel budget q where
  alg := finiteRuntimePlanToKleisli runtimeRel q
  result_eq := finiteRuntimePlanToKleisli_sound domain env runtimeRel q
  total_result_eq := by
    calc
      (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
          (finiteRuntimePlanToKleisli runtimeRel q)).1
          = FiniteKleisliFieldAlg.evalFinset domain env
              (finiteRuntimePlanToKleisli runtimeRel q) := by
            exact FiniteKleisliFieldAlg.evalWithTotalCost_result_eq
              domain env budget (finiteRuntimePlanToKleisli runtimeRel q)
      _ = FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
            finiteRuntimePlanToKleisli_sound domain env runtimeRel q
  cost_le_totalWorkBound :=
    FiniteKleisliFieldAlg.evalWithTotalCost_cost_le_totalWorkBound
      domain env budget hEnv (finiteRuntimePlanToKleisli runtimeRel q)
  result_subset_domain :=
    FiniteKleisliFieldAlg.evalWithTotalCost_result_subset_domain
      domain env budget hEnv (finiteRuntimePlanToKleisli runtimeRel q)

/-- THEOREM 3: the runtime plan's compiled total-cost result is extensionally
the runtime finite semantics.  This is the direct result-soundness projection
from the certificate. -/
theorem finiteRuntimeGenerative_total_result_eq {Row Base RuntimeGen : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
      (finiteRuntimePlanToKleisli runtimeRel q)).1 =
        FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q := by
  calc
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
      (finiteRuntimePlanToKleisli runtimeRel q)).1
        = FiniteKleisliFieldAlg.evalFinset domain env
            (finiteRuntimePlanToKleisli runtimeRel q) := by
          exact FiniteKleisliFieldAlg.evalWithTotalCost_result_eq
            domain env budget (finiteRuntimePlanToKleisli runtimeRel q)
    _ = FiniteRuntimeGenerativePlan.evalFinset domain env runtimeRel q :=
          finiteRuntimePlanToKleisli_sound domain env runtimeRel q

/-- THEOREM 4: the compiled total cost of a finite runtime plan is bounded by
the explicit external/oracle budget plus structural Kleisli work bound. -/
theorem finiteRuntimeGenerative_total_cost_le_bound {Row Base RuntimeGen : Type*}
    [DecidableEq Row]
    (domain : Finset Row) (env : Base -> Finset Row)
    (runtimeRel : RuntimeGen -> Row -> Row -> Bool)
    (budget : ExternalOracleBudget Row Base)
    (hEnv : forall b, env b ⊆ domain)
    (q : FiniteRuntimeGenerativePlan Row Base RuntimeGen) :
    (FiniteKleisliFieldAlg.evalWithTotalCost domain env budget
      (finiteRuntimePlanToKleisli runtimeRel q)).2 ≤
        FiniteKleisliFieldAlg.totalWorkBound domain budget
          (finiteRuntimePlanToKleisli runtimeRel q) :=
  FiniteKleisliFieldAlg.evalWithTotalCost_cost_le_totalWorkBound
    domain env budget hEnv (finiteRuntimePlanToKleisli runtimeRel q)

/-!
  Summary:
  - Runtime-shaped finite generative plans compile into the finite Kleisli
    algebra without changing their finite result set.
  - The compiled plan inherits Proposition 39's total-cost bound, so the
    runtime-shaped plan has an explicit executable complexity certificate.
  - The remaining cost boundary is now precise: materialization/model/cache
    work must enter through the external budget; if the runtime cannot supply
    that budget, this theorem deliberately does not apply.
-/

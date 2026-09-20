/-
  Proposition 78: finite stateful executable queries have denotation,
  calculus, and cost certificates.

  Proposition 73 proved mutual expressibility between the Prop-valued stateful
  generative algebra and its matching calculus:

      State -> Row -> State -> Prop.

  Proposition 74 proved finite executable cost bounds for the same operational
  shape, but stopped at finite `Finset (Row × State)` results.

  This file welds those two surfaces.  Every finite executable stateful query
  has:

    * an equivalent Prop-valued `StatefulGenAlg`;
    * an equivalent `StatefulGenCalc`;
    * the P74 finite executable cost bound.

  This is the stateful/reflexive counterpart of the finite runtime
  completeness-and-cost bridge from Proposition 49.
-/

import H0mework.Realization.QueryPlans.P74

/-! ## Finite stateful executable semantics as a Prop-valued relation -/

/-- Turn a finite primitive stateful transition environment into the
Prop-valued primitive relation used by `StatefulGenAlg`. -/
def finiteStatefulEnvProp {State Row Prim : Type*} [DecidableEq State]
    [DecidableEq Row]
    (env : Prim -> State -> Finset (Row × State)) :
    Prim -> State -> Row -> State -> Prop :=
  fun p x row y => (row, y) ∈ env p x

/-- Compile finite executable stateful syntax into the Prop-valued stateful
generative algebra. -/
def finiteStatefulToAlg {State Row Prim : Type*} :
    FiniteStatefulGenAlg State Row Prim ->
      StatefulGenAlg State Row Prim
  | FiniteStatefulGenAlg.empty => StatefulGenAlg.empty
  | FiniteStatefulGenAlg.ret value => StatefulGenAlg.ret value
  | FiniteStatefulGenAlg.primitive p => StatefulGenAlg.primitive p
  | FiniteStatefulGenAlg.union p q =>
      StatefulGenAlg.union (finiteStatefulToAlg p) (finiteStatefulToAlg q)
  | FiniteStatefulGenAlg.inter p q =>
      StatefulGenAlg.inter (finiteStatefulToAlg p) (finiteStatefulToAlg q)
  | FiniteStatefulGenAlg.diff p q =>
      StatefulGenAlg.diff (finiteStatefulToAlg p) (finiteStatefulToAlg q)
  | FiniteStatefulGenAlg.guard predicate q =>
      StatefulGenAlg.guard
        (fun x row y => predicate x row y = true)
        (finiteStatefulToAlg q)
  | FiniteStatefulGenAlg.bind q k =>
      StatefulGenAlg.bind (finiteStatefulToAlg q)
        (fun row => finiteStatefulToAlg (k row))

/-- THEOREM 1: finite executable stateful semantics equals the Prop-valued
stateful algebra denotation. -/
theorem finiteStatefulToAlg_sound {State Row Prim : Type*}
    [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State)) :
    forall q x row y,
      (row, y) ∈
          FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x <->
        StatefulGenAlg.eval (finiteStatefulEnvProp env)
          (finiteStatefulToAlg q) x row y := by
  intro q
  induction q with
  | empty =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval]
  | ret value =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval]
  | primitive p =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, finiteStatefulEnvProp]
  | union p q ihp ihq =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, ihp x row y, ihq x row y]
  | inter p q ihp ihq =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, ihp x row y, ihq x row y]
  | diff p q ihp ihq =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, ihp x row y, ihq x row y]
  | guard predicate q ih =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, ih x row y, and_comm]
  | bind q k ihq ihk =>
      intro x row y
      simp [FiniteStatefulGenAlg.evalFinset, finiteStatefulToAlg,
        StatefulGenAlg.eval, ihq, ihk]

/-! ## Combined completeness-and-cost certificate -/

/-- A finite stateful executable query, its Prop-valued algebra/calculus
translations, and its finite executable cost bound. -/
structure FiniteStatefulCompletenessCostCertificate
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (q : FiniteStatefulGenAlg State Row Prim) where
  alg : StatefulGenAlg State Row Prim
  alg_eval_iff_finite :
    forall x row y,
      StatefulGenAlg.eval (finiteStatefulEnvProp env) alg x row y <->
        (row, y) ∈
          FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x
  calcFormula : StatefulGenCalc State Row Prim
  calc_eval_iff_finite :
    forall x row y,
      StatefulGenCalc.eval (finiteStatefulEnvProp env) calcFormula x row y <->
        (row, y) ∈
          FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x
  result_eq :
    forall x,
      (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env q x).1 =
        FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x
  cost_le_workBound :
    forall x,
      (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env q x).2 ≤
        FiniteStatefulGenAlg.workBound stateDomain rowDomain q

/-- THEOREM 2: every finite executable stateful query has a combined
denotation/calculus/cost certificate, assuming primitives, returned rows, and
current states are covered by the finite domains for the cost/subset part. -/
def finiteStatefulCompletenessCostCertificate
    {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
    (stateDomain : Finset State) (rowDomain : Finset Row)
    (env : Prim -> State -> Finset (Row × State))
    (hEnv :
      forall p x,
        env p x ⊆ FiniteStatefulGenAlg.pairDomain stateDomain rowDomain)
    (hRow : forall row, row ∈ rowDomain)
    (hCurrent : forall x, x ∈ stateDomain)
    (q : FiniteStatefulGenAlg State Row Prim) :
    FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q where
  alg := finiteStatefulToAlg q
  alg_eval_iff_finite := by
    intro x row y
    exact (finiteStatefulToAlg_sound stateDomain rowDomain env q x row y).symm
  calcFormula := statefulAlgToCalc (finiteStatefulToAlg q)
  calc_eval_iff_finite := by
    intro x row y
    exact
      (statefulAlgToCalc_sound (finiteStatefulEnvProp env)
        (finiteStatefulToAlg q) x row y).trans
        ((finiteStatefulToAlg_sound stateDomain rowDomain env q x row y).symm)
  result_eq :=
    FiniteStatefulGenAlg.evalWithCost_result_eq stateDomain rowDomain env q
  cost_le_workBound :=
    FiniteStatefulGenAlg.evalWithCost_cost_le_workBound stateDomain rowDomain
      env hEnv hRow hCurrent q

namespace FiniteStatefulCompletenessCostCertificate

variable {State Row Prim : Type*} [DecidableEq State] [DecidableEq Row]
variable {stateDomain : Finset State} {rowDomain : Finset Row}
variable {env : Prim -> State -> Finset (Row × State)}
variable {q : FiniteStatefulGenAlg State Row Prim}

/-- THEOREM 3: the certificate's algebra query is extensionally the original
finite executable stateful query. -/
theorem alg_complete
    (C : FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q)
    (x : State) (row : Row) (y : State) :
    StatefulGenAlg.eval (finiteStatefulEnvProp env) C.alg x row y <->
      (row, y) ∈
        FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x :=
  C.alg_eval_iff_finite x row y

/-- THEOREM 4: the certificate's calculus formula is extensionally the original
finite executable stateful query. -/
theorem calc_complete
    (C : FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q)
    (x : State) (row : Row) (y : State) :
    StatefulGenCalc.eval (finiteStatefulEnvProp env) C.calcFormula x row y <->
      (row, y) ∈
        FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x :=
  C.calc_eval_iff_finite x row y

/-- THEOREM 5: the instrumented evaluator inside the certificate returns the
original finite result set. -/
theorem instrumented_result_eq
    (C : FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q)
    (x : State) :
    (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env q x).1 =
      FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env q x :=
  C.result_eq x

/-- THEOREM 6: the instrumented evaluator inside the certificate satisfies the
P74 structural worst-case work bound. -/
theorem instrumented_cost_le_workBound
    (C : FiniteStatefulCompletenessCostCertificate stateDomain rowDomain env q)
    (x : State) :
    (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env q x).2 ≤
      FiniteStatefulGenAlg.workBound stateDomain rowDomain q :=
  C.cost_le_workBound x

end FiniteStatefulCompletenessCostCertificate

/-!
  Summary:
  - Finite executable stateful query semantics is denotationally equivalent to
    the P73 Prop-valued stateful algebra.
  - The corresponding P73 calculus formula is equivalent as well.
  - The same certificate carries P74's finite executable result equality and
    structural cost bound.

  Remaining boundary:
  - This is still finite-domain, worst-case structural accounting.
  - It does not price source reopen, external model generation, cache policy, or
    materializing the finite state/row domains.
  - It does not prove arbitrary uncovered primitives are source-backed or
    mechanism-faithful; they remain declared finite primitive transitions.
-/

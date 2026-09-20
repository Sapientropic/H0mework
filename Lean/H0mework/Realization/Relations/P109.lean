/-
  Proposition 109: projection-visible obligation queries have an explicit
  finite read-guard cost.

  Propositions 105-107 closed the structure-relative completeness boundary:
  in a P94/P105 system, generated Boolean query expressibility is exactly
  projection visibility.  Proposition 106 embedded those predicates into the
  Prop-valued stateful query algebra as read-only guards.

  This file adds the missing small complexity bridge.  A read guard has two
  costs:

    * the stateful wrapper cost: produce one unit row and filter it;
    * the obligation-query cost: evaluate the Boolean atom query itself.

  The existing finite stateful cost model counts the wrapper.  Here we add a
  node-count cost for Boolean obligation queries and prove the executable
  Boolean evaluator costs exactly that many nodes.  A projection-visible
  predicate therefore receives a finite read-guard witness whose wrapper cost
  is exactly 1 and whose guard cost is exactly the chosen Boolean query's AST
  size.

  Boundary: this still does not price source reopen, external generation,
  finite-domain materialization, or the cost of implementing the primitive
  atom oracle itself.  Those remain explicit external/mechanism costs rather
  than being hidden inside "query expressibility."
-/

import H0mework.Realization.CyclicMemory.P108
import H0mework.Realization.QueryPlans.P78

/-! ## Boolean obligation oracle and query cost -/

/-- A Boolean oracle faithfully implementing an `ObligationSemantics`.  This
is the executable boundary for primitive atom checks. -/
structure BoolObligationOracle {State Atom : Type*}
    (S : ObligationSemantics State Atom) where
  holdsBool : Atom -> State -> Bool
  holdsBool_iff : forall a x, holdsBool a x = true <-> S.holds a x

namespace BoolQuery

variable {State Atom : Type*}

/-- Structural AST node count for Boolean queries. -/
def nodeCount : BoolQuery Atom -> Nat
  | top => 1
  | bottom => 1
  | atom _ => 1
  | neg q => 1 + nodeCount q
  | meet p q => 1 + nodeCount p + nodeCount q
  | join p q => 1 + nodeCount p + nodeCount q

/-- Executable Boolean evaluation using a primitive atom oracle. -/
def evalBool (oracle : Atom -> State -> Bool) :
    BoolQuery Atom -> State -> Bool
  | top, _x => true
  | bottom, _x => false
  | atom a, x => oracle a x
  | neg q, x => !(evalBool oracle q x)
  | meet p q, x => evalBool oracle p x && evalBool oracle q x
  | join p q, x => evalBool oracle p x || evalBool oracle q x

/-- Executable Boolean evaluation with an explicit node counter.  The evaluator
does not short-circuit; it charges the full AST shape. -/
def evalBoolWithCost (oracle : Atom -> State -> Bool) :
    BoolQuery Atom -> State -> Bool × Nat
  | top, _x => (true, 1)
  | bottom, _x => (false, 1)
  | atom a, x => (oracle a x, 1)
  | neg q, x =>
      let eq := evalBoolWithCost oracle q x
      (!(eq.1), 1 + eq.2)
  | meet p q, x =>
      let ep := evalBoolWithCost oracle p x
      let eq := evalBoolWithCost oracle q x
      (ep.1 && eq.1, 1 + ep.2 + eq.2)
  | join p q, x =>
      let ep := evalBoolWithCost oracle p x
      let eq := evalBoolWithCost oracle q x
      (ep.1 || eq.1, 1 + ep.2 + eq.2)

/-- THEOREM 1: the instrumented Boolean evaluator returns the ordinary
executable Boolean result. -/
theorem evalBoolWithCost_result_eq
    (oracle : Atom -> State -> Bool) :
    forall q x,
      (evalBoolWithCost oracle q x).1 = evalBool oracle q x := by
  intro q
  induction q with
  | top =>
      intro x
      rfl
  | bottom =>
      intro x
      rfl
  | atom a =>
      intro x
      rfl
  | neg q ih =>
      intro x
      simp [evalBoolWithCost, evalBool, ih x]
  | meet p q ihp ihq =>
      intro x
      simp [evalBoolWithCost, evalBool, ihp x, ihq x]
  | join p q ihp ihq =>
      intro x
      simp [evalBoolWithCost, evalBool, ihp x, ihq x]

/-- THEOREM 2: the instrumented Boolean evaluator costs exactly the AST node
count. -/
theorem evalBoolWithCost_cost_eq_nodeCount
    (oracle : Atom -> State -> Bool) :
    forall q x,
      (evalBoolWithCost oracle q x).2 = nodeCount q := by
  intro q
  induction q with
  | top =>
      intro x
      rfl
  | bottom =>
      intro x
      rfl
  | atom a =>
      intro x
      rfl
  | neg q ih =>
      intro x
      simp [evalBoolWithCost, nodeCount, ih x]
  | meet p q ihp ihq =>
      intro x
      simp [evalBoolWithCost, nodeCount, ihp x, ihq x]
  | join p q ihp ihq =>
      intro x
      simp [evalBoolWithCost, nodeCount, ihp x, ihq x]

/-- THEOREM 3: a faithful Boolean oracle agrees with the Prop-valued Boolean
query semantics. -/
theorem evalBool_iff_eval
    {S : ObligationSemantics State Atom}
    (O : BoolObligationOracle S) :
    forall q x,
      evalBool O.holdsBool q x = true <-> BoolQuery.eval S q x := by
  intro q
  induction q with
  | top =>
      intro x
      simp [evalBool, BoolQuery.eval]
  | bottom =>
      intro x
      simp [evalBool, BoolQuery.eval]
  | atom a =>
      intro x
      exact O.holdsBool_iff a x
  | neg q ih =>
      intro x
      have hbool :
          evalBool O.holdsBool (BoolQuery.neg q) x = true <->
            ¬ (evalBool O.holdsBool q x = true) := by
        cases h : evalBool O.holdsBool q x <;> simp [evalBool, h]
      calc
        evalBool O.holdsBool (BoolQuery.neg q) x = true <->
            ¬ (evalBool O.holdsBool q x = true) :=
          hbool
        _ <-> ¬ BoolQuery.eval S q x :=
          not_congr (ih x)
  | meet p q ihp ihq =>
      intro x
      simp [evalBool, BoolQuery.eval, ihp x, ihq x]
  | join p q ihp ihq =>
      intro x
      simp [evalBool, BoolQuery.eval, ihp x, ihq x]

end BoolQuery

namespace StructureDeterminedSevenFacetSystem

variable {State Prim : Type*}

/-! ## Finite read guards for projection-visible predicates -/

/-- A finite executable read guard for a Boolean obligation query.  It produces
one unit row and preserves the current state exactly when the Boolean query
holds. -/
def boolQueryFiniteStatefulPlan
    (S : StructureDeterminedSevenFacetSystem State)
    (O : BoolObligationOracle S.obligations)
    (q : BoolQuery SemanticAtom) :
    FiniteStatefulGenAlg State Unit Prim :=
  FiniteStatefulGenAlg.guard
    (fun x _row _y => BoolQuery.evalBool O.holdsBool q x)
    (FiniteStatefulGenAlg.ret ())

/-- THEOREM 4: the finite read guard has the expected source Prop semantics. -/
theorem boolQueryFiniteStatefulPlan_evalFinset
    [DecidableEq State]
    (S : StructureDeterminedSevenFacetSystem State)
    (O : BoolObligationOracle S.obligations)
    (q : BoolQuery SemanticAtom)
    (stateDomain : Finset State) (rowDomain : Finset Unit)
    (env : Prim -> State -> Finset (Unit × State))
    (x : State) (row : Unit) (y : State) :
    (row, y) ∈
        FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env
          (boolQueryFiniteStatefulPlan S O q) x <->
      BoolQuery.eval S.obligations q x /\ row = () /\ y = x := by
  cases row
  cases hb : BoolQuery.evalBool O.holdsBool q x
  · have hnot : ¬ BoolQuery.eval S.obligations q x := by
      intro hq
      have htrue :
          BoolQuery.evalBool O.holdsBool q x = true :=
        (BoolQuery.evalBool_iff_eval O q x).mpr hq
      simp [hb] at htrue
    simp [boolQueryFiniteStatefulPlan, FiniteStatefulGenAlg.evalFinset,
      hb, hnot]
  · have hq : BoolQuery.eval S.obligations q x :=
      (BoolQuery.evalBool_iff_eval O q x).mp hb
    simp [boolQueryFiniteStatefulPlan, FiniteStatefulGenAlg.evalFinset,
      hb, hq]

/-- THEOREM 5: the finite read guard's stateful wrapper cost is exactly one
filter check.  The Boolean guard's internal AST cost is accounted separately by
`BoolQuery.evalBoolWithCost_cost_eq_nodeCount`. -/
theorem boolQueryFiniteStatefulPlan_evalWithCost_cost_eq_one
    [DecidableEq State]
    (S : StructureDeterminedSevenFacetSystem State)
    (O : BoolObligationOracle S.obligations)
    (q : BoolQuery SemanticAtom)
    (stateDomain : Finset State) (rowDomain : Finset Unit)
    (env : Prim -> State -> Finset (Unit × State))
    (x : State) :
    (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env
        (boolQueryFiniteStatefulPlan S O q) x).2 = 1 := by
  simp [boolQueryFiniteStatefulPlan, FiniteStatefulGenAlg.evalWithCost]

/-- THEOREM 6: every projection-visible predicate has a finite read-guard
witness with explicit wrapper and Boolean-guard costs. -/
theorem projectionVisible_finiteReadGuardCostWitness
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    (hvisible : ProjectionVisible S target)
    (O : BoolObligationOracle S.obligations) :
    exists q : BoolQuery SemanticAtom,
      exists plan : FiniteStatefulGenAlg State Unit Prim,
        (forall x, BoolQuery.eval S.obligations q x <-> target x) /\
        (forall [DecidableEq State]
          (stateDomain : Finset State) (rowDomain : Finset Unit)
          (env : Prim -> State -> Finset (Unit × State))
          (x : State) (row : Unit) (y : State),
          (row, y) ∈
              FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env
                plan x <->
            target x /\ row = () /\ y = x) /\
        (forall [DecidableEq State]
          (stateDomain : Finset State) (rowDomain : Finset Unit)
          (env : Prim -> State -> Finset (Unit × State))
          (x : State),
          (FiniteStatefulGenAlg.evalWithCost stateDomain rowDomain env
              plan x).2 = 1) /\
        (forall x,
          (BoolQuery.evalBoolWithCost O.holdsBool q x).2 =
            BoolQuery.nodeCount q) := by
  rcases S.projectionVisible_queryExpressible target hvisible with ⟨q, hq⟩
  refine ⟨q, boolQueryFiniteStatefulPlan S O q, hq, ?_, ?_, ?_⟩
  · intro _inst stateDomain rowDomain env x row y
    calc
      (row, y) ∈
          FiniteStatefulGenAlg.evalFinset stateDomain rowDomain env
            (boolQueryFiniteStatefulPlan S O q) x <->
        BoolQuery.eval S.obligations q x /\ row = () /\ y = x :=
          boolQueryFiniteStatefulPlan_evalFinset S O q stateDomain
            rowDomain env x row y
      _ <-> target x /\ row = () /\ y = x := by
          rw [hq x]
  · intro _inst stateDomain rowDomain env x
    exact boolQueryFiniteStatefulPlan_evalWithCost_cost_eq_one
      S O q stateDomain rowDomain env x
  · intro x
    exact BoolQuery.evalBoolWithCost_cost_eq_nodeCount O.holdsBool q x

/-!
  Summary:
  - Projection-visible predicates are not only expressible as read-only
    stateful queries; they have a finite read-guard cost witness.
  - The wrapper cost is exactly one stateful filter check.
  - The obligation predicate's internal executable cost is exactly the Boolean
    query AST node count.

  Remaining boundary:
  - The primitive atom oracle is still a mechanism boundary: its own cost and
    source/mechanism faithfulness are not hidden in this theorem.
  - The witness chooses the Boolean query supplied by P105/P42; minimizing that
    query is an optimizer problem, not part of this completeness theorem.
-/


end StructureDeterminedSevenFacetSystem

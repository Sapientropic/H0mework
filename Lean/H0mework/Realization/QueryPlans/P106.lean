/-
  Proposition 106: structure-determined obligations compile into the stateful
  query algebra.

  Proposition 105 proved that, once a system is formalized as a
  structure-determined seven-facet system, every projection-visible predicate is
  expressible by the Boolean query algebra over the seven semantic atoms.  That
  closes the "obligation vocabulary" side.

  Proposition 73 supplied the stateful generative query algebra:

      State -> Row -> State -> Prop

  This file connects the two.  A projection-visible obligation predicate
  compiles into a mutation-free stateful query: it emits the unit row exactly
  when the Boolean obligation query holds, and its output state is the input
  state.  The same predicate also compiles into the matching stateful calculus.

  Boundary: this is still relative to the P94/P105 system structure.  It does
  not prove that the informal slogan `reflexive + source-backed +
  navigation-only` uniquely generates that projection.  It proves the next
  formal bridge: once the projection is given, its visible obligation language
  has a denotation-preserving, read-only embedding into the stateful query
  layer.
-/

import H0mework.Realization.Reflexive.GenerativeAlgebra
import H0mework.Realization.QuerySupport.P105

namespace StructureDeterminedSevenFacetSystem

variable {State Prim : Type*}

/-! ## Boolean obligation queries as read-only stateful plans -/

/-- A Boolean obligation query embedded as a read-only stateful plan.  It emits
the unit row when the Boolean query holds and leaves the state unchanged. -/
def boolQueryStatefulPlan
    (S : StructureDeterminedSevenFacetSystem State)
    (q : BoolQuery SemanticAtom) :
    StatefulGenAlg State Unit Prim :=
  StatefulGenAlg.guard
    (fun x _row _y => BoolQuery.eval S.obligations q x)
    (StatefulGenAlg.ret ())

/-- THEOREM 1: the stateful embedding of a Boolean obligation query is exactly
a read-only guard. -/
theorem boolQueryStatefulPlan_eval
    (S : StructureDeterminedSevenFacetSystem State)
    (q : BoolQuery SemanticAtom)
    (env : Prim -> State -> Unit -> State -> Prop)
    (x : State) (row : Unit) (y : State) :
    StatefulGenAlg.eval env (boolQueryStatefulPlan S q) x row y <->
      BoolQuery.eval S.obligations q x /\ row = () /\ y = x := by
  simp [boolQueryStatefulPlan, StatefulGenAlg.eval]

/-- THEOREM 2: the stateful embedding never writes a different next state. -/
theorem boolQueryStatefulPlan_state_preserving
    (S : StructureDeterminedSevenFacetSystem State)
    (q : BoolQuery SemanticAtom)
    (env : Prim -> State -> Unit -> State -> Prop)
    {x : State} {row : Unit} {y : State}
    (h :
      StatefulGenAlg.eval env (boolQueryStatefulPlan S q) x row y) :
    y = x :=
  (boolQueryStatefulPlan_eval S q env x row y).mp h |>.2.2

/-! ## Projection-visible predicates inherit the stateful query bridge -/

/-- THEOREM 3: every projection-visible predicate is expressible as a
mutation-free stateful algebra query. -/
theorem projectionVisible_statefulAlgExpressible
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    (hvisible : ProjectionVisible S target)
    (env : Prim -> State -> Unit -> State -> Prop) :
    exists q : StatefulGenAlg State Unit Prim,
      forall x row y,
        StatefulGenAlg.eval env q x row y <->
          target x /\ row = () /\ y = x := by
  rcases S.projectionVisible_queryExpressible target hvisible with
    ⟨bq, hbq⟩
  refine ⟨boolQueryStatefulPlan S bq, ?_⟩
  intro x row y
  calc
    StatefulGenAlg.eval env (boolQueryStatefulPlan S bq) x row y <->
        BoolQuery.eval S.obligations bq x /\ row = () /\ y = x :=
      boolQueryStatefulPlan_eval S bq env x row y
    _ <-> target x /\ row = () /\ y = x := by
      rw [hbq x]

/-- THEOREM 4: every projection-visible predicate is expressible in the
matching stateful calculus as the same mutation-free guard. -/
theorem projectionVisible_statefulCalcExpressible
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    (hvisible : ProjectionVisible S target)
    (env : Prim -> State -> Unit -> State -> Prop) :
    exists f : StatefulGenCalc State Unit Prim,
      forall x row y,
        StatefulGenCalc.eval env f x row y <->
          target x /\ row = () /\ y = x := by
  rcases S.projectionVisible_statefulAlgExpressible
      target hvisible env with
    ⟨q, hq⟩
  refine ⟨statefulAlgToCalc q, ?_⟩
  intro x row y
  calc
    StatefulGenCalc.eval env (statefulAlgToCalc q) x row y <->
        StatefulGenAlg.eval env q x row y :=
      statefulAlgToCalc_sound env q x row y
    _ <-> target x /\ row = () /\ y = x :=
      hq x row y

/-!
  Summary:
  - Projection-visible obligations from P105 compile into P73's stateful
    generative algebra as pure read guards.
  - They also compile into the matching stateful calculus.
  - Therefore, under the P94/P105 structure boundary, `system structure ->
    obligation vocabulary -> stateful query` is a well-defined mathematical
    pipeline rather than a Python/runtime convention.

  Remaining boundary:
  - This does not by itself prove that the informal AIppocampus primitives
    uniquely generate the P94 projection.  It says that after that projection
    is supplied, no extra interpretive choice is introduced by the stateful
    query layer.
-/


end StructureDeterminedSevenFacetSystem

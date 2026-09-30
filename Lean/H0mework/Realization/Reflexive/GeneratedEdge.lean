/-
  Proposition 81: stateful query output is the canonical recollection time edge.

  Proposition 73 proved that a reflexive read/write query embeds into the
  stateful generative query algebra as a one-primitive plan:

      input state -> produced observation row -> next state.

  Proposition 80 proved that the same reflexive query generates a two-point
  memory time-field progression:

      now section -> observed by read
      next section -> written by write.

  This file proves those are not merely analogous descriptions.  For the
  generated/canonical case, the stateful query's `(row, nextState)` result is
  exactly the time-field edge's `(observe-now, next-section)` pair.  This is a
  local bridge from "query = retrieval/generation/state mutation" to
  "recollection = time-field activation".

  Boundary: this is still the reflexive/canonical edge.  It does not claim
  that arbitrary runtime generators or arbitrary independent memory fields are
  faithful; those still need the coverage/mechanism certificates proved in the
  surrounding modules.
-/

import H0mework.Realization.Reflexive.GenerativeAlgebra
import H0mework.Realization.Reflexive.FieldProgression

/-! ## The generated edge as a stateful query result -/

/-- The observation produced at the current point of the generated time edge. -/
def generatedEdgeCurrentObservation
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Observation :=
  (reflexiveQueryGeneratedTimeStep q x).field.observe
    ((reflexiveQueryGeneratedTimeStep q x).field.stateAt
      (reflexiveQueryGeneratedTimeStep q x).now)

/-- The next state section of the generated time edge. -/
def generatedEdgeNextState
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : State :=
  (reflexiveQueryGeneratedTimeStep q x).field.stateAt
    (reflexiveQueryGeneratedTimeStep q x).next

/-- THEOREM 1: the stateful-generative embedding of a reflexive query returns
exactly the generated time edge's current observation and next section. -/
theorem reflexiveStatefulPlan_eval_iff_generated_edge
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (x : State) (obs : Observation) (y : State) :
    StatefulGenAlg.eval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q) x obs y <->
      obs = generatedEdgeCurrentObservation q x /\
        y = generatedEdgeNextState q x := by
  rfl

/-- THEOREM 2: the calculus formula obtained from the reflexive stateful plan
has the same generated-edge denotation. -/
theorem reflexiveStatefulCalc_eval_iff_generated_edge
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (x : State) (obs : Observation) (y : State) :
    StatefulGenCalc.eval (reflexiveQueryPrimitive q)
        (statefulAlgToCalc (reflexiveQueryStatefulPlan q)) x obs y <->
      obs = generatedEdgeCurrentObservation q x /\
        y = generatedEdgeNextState q x := by
  exact
    (statefulAlgToCalc_sound (reflexiveQueryPrimitive q)
      (reflexiveQueryStatefulPlan q) x obs y).trans
      (reflexiveStatefulPlan_eval_iff_generated_edge q x obs y)

/-- THEOREM 3: the generated-edge current observation is definitionally the
query read at the current state. -/
theorem generatedEdgeCurrentObservation_eq_read
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    generatedEdgeCurrentObservation q x = q.read x := by
  rfl

/-- THEOREM 4: the generated-edge next state is definitionally the query write
at the current state. -/
theorem generatedEdgeNextState_eq_write
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    generatedEdgeNextState q x = q.write x := by
  rfl

/-! ## Non-idempotence is the stateful-query face of temporal holonomy -/

/-- THEOREM 5: temporal holonomy on the generated edge is a sufficient reason
why the reflexive stateful plan cannot be idempotent. -/
theorem reflexiveStatefulPlan_not_idempotent_of_temporal_holonomy
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State)
    (hhol : TemporalObservationHolonomy
      (reflexiveQueryGeneratedTimeStep q x)) :
    ¬ StatefulGenAlg.Equivalent (reflexiveQueryPrimitive q)
      (StatefulGenAlg.bind (reflexiveQueryStatefulPlan q)
        (fun _ => reflexiveQueryStatefulPlan q))
      (reflexiveQueryStatefulPlan q) := by
  exact reflexiveQueryStatefulPlan_not_idempotent_of_obstruction q x
    ((reflexiveQueryGenerated_holonomy_iff_obstruction q x).mp hhol)

/-- A compact certificate tying the query-algebra face and the time-field face
of one reflexive query together. -/
structure ReflexiveStatefulTimeEdgeCertificate
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) where
  algPlan : StatefulGenAlg State Observation Unit
  calcFormula : StatefulGenCalc State Observation Unit
  step :
    RecollectionTimeStep CanonicalReflexiveTime State Observation
      RecollectionAtom RecollectionAtom
  alg_eval_iff_edge :
    forall obs y,
      StatefulGenAlg.eval (reflexiveQueryPrimitive q) algPlan x obs y <->
        obs = step.field.observe (step.field.stateAt step.now) /\
          y = step.field.stateAt step.next
  calc_eval_iff_edge :
    forall obs y,
      StatefulGenCalc.eval (reflexiveQueryPrimitive q) calcFormula x obs y <->
        obs = step.field.observe (step.field.stateAt step.now) /\
          y = step.field.stateAt step.next
  holonomy_iff_obstruction :
    TemporalObservationHolonomy step <-> ReflexiveLambdaObstruction q x
  holonomy_iff_recollectable :
    TemporalObservationHolonomy step <->
      RecollectableMemoryPotential (reflexiveRecollectionAct q) x

/-- THEOREM 6: every reflexive query at a current state has a combined
stateful-query/time-field certificate. -/
def reflexiveStatefulTimeEdgeCertificate
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveStatefulTimeEdgeCertificate q x where
  algPlan := reflexiveQueryStatefulPlan q
  calcFormula := statefulAlgToCalc (reflexiveQueryStatefulPlan q)
  step := reflexiveQueryGeneratedTimeStep q x
  alg_eval_iff_edge := by
    intro obs y
    exact reflexiveStatefulPlan_eval_iff_generated_edge q x obs y
  calc_eval_iff_edge := by
    intro obs y
    exact reflexiveStatefulCalc_eval_iff_generated_edge q x obs y
  holonomy_iff_obstruction :=
    reflexiveQueryGenerated_holonomy_iff_obstruction q x
  holonomy_iff_recollectable :=
    reflexiveQueryGenerated_holonomy_iff_recollectable q x

namespace ReflexiveStatefulTimeEdgeCertificate

variable {State Observation : Type*}
variable {q : ReflexiveQuery State Observation} {x : State}

/-- THEOREM 7: the certificate's algebra plan is complete for the time edge. -/
theorem alg_complete
    (C : ReflexiveStatefulTimeEdgeCertificate q x)
    (obs : Observation) (y : State) :
    StatefulGenAlg.eval (reflexiveQueryPrimitive q) C.algPlan x obs y <->
      obs = C.step.field.observe (C.step.field.stateAt C.step.now) /\
        y = C.step.field.stateAt C.step.next :=
  C.alg_eval_iff_edge obs y

/-- THEOREM 8: the certificate's calculus formula is complete for the time
edge. -/
theorem calc_complete
    (C : ReflexiveStatefulTimeEdgeCertificate q x)
    (obs : Observation) (y : State) :
    StatefulGenCalc.eval (reflexiveQueryPrimitive q) C.calcFormula x obs y <->
      obs = C.step.field.observe (C.step.field.stateAt C.step.now) /\
        y = C.step.field.stateAt C.step.next :=
  C.calc_eval_iff_edge obs y

/-- THEOREM 9: the certificate's temporal holonomy is exactly local reflexive
obstruction. -/
theorem holonomy_obstruction
    (C : ReflexiveStatefulTimeEdgeCertificate q x) :
    TemporalObservationHolonomy C.step <-> ReflexiveLambdaObstruction q x :=
  C.holonomy_iff_obstruction

/-- THEOREM 10: the certificate's temporal holonomy is exactly recollectable
potential for the canonical recollection act. -/
theorem holonomy_recollectable
    (C : ReflexiveStatefulTimeEdgeCertificate q x) :
    TemporalObservationHolonomy C.step <->
      RecollectableMemoryPotential (reflexiveRecollectionAct q) x :=
  C.holonomy_iff_recollectable

end ReflexiveStatefulTimeEdgeCertificate

/-!
  Summary:
  - The stateful-generative query output of a reflexive query is exactly the
    canonical time-field edge generated by the same query.
  - Algebra and calculus both denote that edge.
  - Temporal holonomy on that edge is the reason the corresponding stateful
    query is not an idempotent SELECT-like query.

  This is a local structural bridge, not a global mechanism-faithfulness
  theorem for arbitrary runtime generators or independent memory fields.
-/

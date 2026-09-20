/-
  Proposition 73: stateful generative query algebra.

  Proposition 61 closed relative completeness for covered *generative* runtime
  queries.  Propositions 33, 35, 71, and 72 closed the reflexive read/write
  side.  This file puts those two halves into one query object.

  A stateful generative query denotes a relation

      State -> Row -> State -> Prop

  meaning: from an input state, produce a row and a next state.  This is the
  powerset/state transducer shape behind an agent-native query:

      retrieval/generation + state mutation.

  The algebra has a `bind` constructor, so generated rows can seed the next
  query while the written state is threaded forward.  A matching calculus has
  the same range-restricted stateful existential binder.  The module proves:

    * the bind unit/associativity laws extensionally;
    * algebra/calculus mutual expressibility for this stateful-generative
      fragment;
    * ordinary `ReflexiveQuery` embeds as a stateful generative primitive;
    * an observation-changing reflexive query is non-idempotent in this
      algebra.

  Boundary: this is still relative to declared primitive stateful relations.
  It is not a completeness theorem for arbitrary source schemas, unrestricted
  first-order logic, aggregation, recursion, or uncovered external-model
  candidate creation.
-/

import H0mework.Realization.Reflexive.CanonicalLoop

/-! ## Stateful generative algebra -/

/-- Stateful generative query algebra.  A query reads/generates rows and may
write the state. -/
inductive StatefulGenAlg (State Row Prim : Type*) where
  | empty
  | ret : Row -> StatefulGenAlg State Row Prim
  | primitive : Prim -> StatefulGenAlg State Row Prim
  | union : StatefulGenAlg State Row Prim ->
      StatefulGenAlg State Row Prim -> StatefulGenAlg State Row Prim
  | inter : StatefulGenAlg State Row Prim ->
      StatefulGenAlg State Row Prim -> StatefulGenAlg State Row Prim
  | diff : StatefulGenAlg State Row Prim ->
      StatefulGenAlg State Row Prim -> StatefulGenAlg State Row Prim
  | guard : (State -> Row -> State -> Prop) ->
      StatefulGenAlg State Row Prim -> StatefulGenAlg State Row Prim
  | bind : StatefulGenAlg State Row Prim ->
      (Row -> StatefulGenAlg State Row Prim) -> StatefulGenAlg State Row Prim

namespace StatefulGenAlg

/-- Denotation of stateful generative algebra as a transition relation:
input state -> produced row -> output state -> proposition. -/
def eval {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) :
    StatefulGenAlg State Row Prim -> State -> Row -> State -> Prop
  | empty, _x, _row, _y => False
  | ret value, x, row, y => row = value /\ y = x
  | primitive p, x, row, y => env p x row y
  | union p q, x, row, y => eval env p x row y \/ eval env q x row y
  | inter p q, x, row, y => eval env p x row y /\ eval env q x row y
  | diff p q, x, row, y => eval env p x row y /\ ¬ eval env q x row y
  | guard predicate q, x, row, y => predicate x row y /\ eval env q x row y
  | bind q k, x, row, y =>
      exists source mid,
        eval env q x source mid /\ eval env (k source) mid row y

/-- Extensional equivalence of stateful generative queries. -/
def Equivalent {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (p q : StatefulGenAlg State Row Prim) : Prop :=
  forall x row y, eval env p x row y <-> eval env q x row y

/-- THEOREM 1: `ret` is the left unit of bind. -/
theorem bind_ret_left {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (value : Row) (k : Row -> StatefulGenAlg State Row Prim) :
    Equivalent env (bind (ret value) k) (k value) := by
  intro x row y
  constructor
  · rintro ⟨source, mid, hret, hk⟩
    rcases hret with ⟨hsource, hmid⟩
    subst source
    subst mid
    exact hk
  · intro hk
    exact ⟨value, x, ⟨rfl, rfl⟩, hk⟩

/-- THEOREM 2: `ret` is the right unit of bind. -/
theorem bind_ret_right {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) :
    Equivalent env (bind q ret) q := by
  intro x row y
  constructor
  · rintro ⟨source, mid, hq, hret⟩
    rcases hret with ⟨hrow, hy⟩
    subst row
    subst y
    exact hq
  · intro hq
    exact ⟨row, y, hq, ⟨rfl, rfl⟩⟩

/-- THEOREM 3: bind is associative, extensionally. -/
theorem bind_assoc {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim)
    (k h : Row -> StatefulGenAlg State Row Prim) :
    Equivalent env (bind (bind q k) h)
      (bind q (fun source => bind (k source) h)) := by
  intro x row y
  constructor
  · rintro ⟨midRow, midState, hbind, hh⟩
    rcases hbind with ⟨source, firstState, hq, hk⟩
    exact ⟨source, firstState, hq, ⟨midRow, midState, hk, hh⟩⟩
  · rintro ⟨source, firstState, hq, hkh⟩
    rcases hkh with ⟨midRow, midState, hk, hh⟩
    exact ⟨midRow, midState, ⟨source, firstState, hq, hk⟩, hh⟩

end StatefulGenAlg

/-! ## Matching stateful generative calculus -/

/-- Calculus with the same stateful range-restricted existential binder. -/
inductive StatefulGenCalc (State Row Prim : Type*) where
  | falsity
  | retc : Row -> StatefulGenCalc State Row Prim
  | pred : Prim -> StatefulGenCalc State Row Prim
  | or : StatefulGenCalc State Row Prim ->
      StatefulGenCalc State Row Prim -> StatefulGenCalc State Row Prim
  | and : StatefulGenCalc State Row Prim ->
      StatefulGenCalc State Row Prim -> StatefulGenCalc State Row Prim
  | minus : StatefulGenCalc State Row Prim ->
      StatefulGenCalc State Row Prim -> StatefulGenCalc State Row Prim
  | guard : (State -> Row -> State -> Prop) ->
      StatefulGenCalc State Row Prim -> StatefulGenCalc State Row Prim
  | existsSeq : StatefulGenCalc State Row Prim ->
      (Row -> StatefulGenCalc State Row Prim) ->
        StatefulGenCalc State Row Prim

namespace StatefulGenCalc

/-- Denotation of the stateful generative calculus. -/
def eval {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) :
    StatefulGenCalc State Row Prim -> State -> Row -> State -> Prop
  | falsity, _x, _row, _y => False
  | retc value, x, row, y => row = value /\ y = x
  | pred p, x, row, y => env p x row y
  | or p q, x, row, y => eval env p x row y \/ eval env q x row y
  | and p q, x, row, y => eval env p x row y /\ eval env q x row y
  | minus p q, x, row, y => eval env p x row y /\ ¬ eval env q x row y
  | guard predicate q, x, row, y => predicate x row y /\ eval env q x row y
  | existsSeq q k, x, row, y =>
      exists source mid,
        eval env q x source mid /\ eval env (k source) mid row y

end StatefulGenCalc

/-! ## Denotation-preserving translations -/

/-- Compile stateful algebra to stateful calculus. -/
def statefulAlgToCalc {State Row Prim : Type*} :
    StatefulGenAlg State Row Prim -> StatefulGenCalc State Row Prim
  | StatefulGenAlg.empty => StatefulGenCalc.falsity
  | StatefulGenAlg.ret value => StatefulGenCalc.retc value
  | StatefulGenAlg.primitive p => StatefulGenCalc.pred p
  | StatefulGenAlg.union p q =>
      StatefulGenCalc.or (statefulAlgToCalc p) (statefulAlgToCalc q)
  | StatefulGenAlg.inter p q =>
      StatefulGenCalc.and (statefulAlgToCalc p) (statefulAlgToCalc q)
  | StatefulGenAlg.diff p q =>
      StatefulGenCalc.minus (statefulAlgToCalc p) (statefulAlgToCalc q)
  | StatefulGenAlg.guard predicate q =>
      StatefulGenCalc.guard predicate (statefulAlgToCalc q)
  | StatefulGenAlg.bind q k =>
      StatefulGenCalc.existsSeq (statefulAlgToCalc q)
        (fun source => statefulAlgToCalc (k source))

/-- Compile stateful calculus back to stateful algebra. -/
def statefulCalcToAlg {State Row Prim : Type*} :
    StatefulGenCalc State Row Prim -> StatefulGenAlg State Row Prim
  | StatefulGenCalc.falsity => StatefulGenAlg.empty
  | StatefulGenCalc.retc value => StatefulGenAlg.ret value
  | StatefulGenCalc.pred p => StatefulGenAlg.primitive p
  | StatefulGenCalc.or p q =>
      StatefulGenAlg.union (statefulCalcToAlg p) (statefulCalcToAlg q)
  | StatefulGenCalc.and p q =>
      StatefulGenAlg.inter (statefulCalcToAlg p) (statefulCalcToAlg q)
  | StatefulGenCalc.minus p q =>
      StatefulGenAlg.diff (statefulCalcToAlg p) (statefulCalcToAlg q)
  | StatefulGenCalc.guard predicate q =>
      StatefulGenAlg.guard predicate (statefulCalcToAlg q)
  | StatefulGenCalc.existsSeq q k =>
      StatefulGenAlg.bind (statefulCalcToAlg q)
        (fun source => statefulCalcToAlg (k source))

/-- THEOREM 4: algebra-to-calculus compilation preserves denotation. -/
theorem statefulAlgToCalc_sound {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) :
    forall q x row y,
      StatefulGenCalc.eval env (statefulAlgToCalc q) x row y <->
        StatefulGenAlg.eval env q x row y := by
  intro q
  induction q with
  | empty =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | ret value =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | primitive p =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | union p q ihp ihq =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | inter p q ihp ihq =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | diff p q ihp ihq =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | guard predicate q ih =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ih x row y]
  | bind q k ihq ihk =>
      intro x row y
      simp [statefulAlgToCalc, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihq, ihk]

/-- THEOREM 5: calculus-to-algebra compilation preserves denotation. -/
theorem statefulCalcToAlg_sound {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) :
    forall f x row y,
      StatefulGenAlg.eval env (statefulCalcToAlg f) x row y <->
        StatefulGenCalc.eval env f x row y := by
  intro f
  induction f with
  | falsity =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | retc value =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | pred p =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval]
  | or p q ihp ihq =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | and p q ihp ihq =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | minus p q ihp ihq =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihp x row y, ihq x row y]
  | guard predicate q ih =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ih x row y]
  | existsSeq q k ihq ihk =>
      intro x row y
      simp [statefulCalcToAlg, StatefulGenAlg.eval, StatefulGenCalc.eval,
        ihq, ihk]

/-- THEOREM 6: every stateful generative algebra query has an equivalent
stateful generative calculus formula. -/
theorem statefulAlg_expressible_by_calc {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) :
    exists f : StatefulGenCalc State Row Prim,
      forall x row y,
        StatefulGenCalc.eval env f x row y <->
          StatefulGenAlg.eval env q x row y := by
  exact ⟨statefulAlgToCalc q, statefulAlgToCalc_sound env q⟩

/-- THEOREM 7: every stateful generative calculus formula has an equivalent
stateful generative algebra query. -/
theorem statefulCalc_expressible_by_alg {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (f : StatefulGenCalc State Row Prim) :
    exists q : StatefulGenAlg State Row Prim,
      forall x row y,
        StatefulGenAlg.eval env q x row y <->
          StatefulGenCalc.eval env f x row y := by
  exact ⟨statefulCalcToAlg f, statefulCalcToAlg_sound env f⟩

/-! ## Embedding ordinary reflexive queries -/

/-- A reflexive read/write query as a primitive stateful-generative relation.
It produces the read observation and writes the next state. -/
def reflexiveQueryPrimitive
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    Unit -> State -> Observation -> State -> Prop :=
  fun _ x obs y => obs = q.read x /\ y = q.write x

/-- The one-node stateful-generative plan corresponding to a reflexive query.
-/
def reflexiveQueryStatefulPlan
    {State Observation : Type*}
    (_q : ReflexiveQuery State Observation) :
    StatefulGenAlg State Observation Unit :=
  StatefulGenAlg.primitive ()

/-- THEOREM 8: the stateful-generative embedding of a reflexive query has the
expected read/write semantics. -/
theorem reflexiveQueryStatefulPlan_eval
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (x : State) (obs : Observation) (y : State) :
    StatefulGenAlg.eval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q) x obs y <->
      obs = q.read x /\ y = q.write x := by
  rfl

/-- THEOREM 9: observation-changing reflexive queries are not idempotent in the
stateful-generative algebra.  Running the plan twice can produce a different
next observation than running it once. -/
theorem reflexiveQueryStatefulPlan_not_idempotent_of_obstruction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (x : State)
    (hobs : ReflexiveLambdaObstruction q x) :
    ¬ StatefulGenAlg.Equivalent (reflexiveQueryPrimitive q)
      (StatefulGenAlg.bind (reflexiveQueryStatefulPlan q)
        (fun _ => reflexiveQueryStatefulPlan q))
      (reflexiveQueryStatefulPlan q) := by
  intro heq
  have hseq :
      StatefulGenAlg.eval (reflexiveQueryPrimitive q)
        (StatefulGenAlg.bind (reflexiveQueryStatefulPlan q)
          (fun _ => reflexiveQueryStatefulPlan q))
        x (q.read (q.write x)) (q.write (q.write x)) := by
    exact ⟨q.read x, q.write x, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  have hone :
      StatefulGenAlg.eval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q)
        x (q.read (q.write x)) (q.write (q.write x)) :=
    (heq x (q.read (q.write x)) (q.write (q.write x))).mp hseq
  exact hobs hone.1

/-!
  Summary:
  - `StatefulGenAlg` is the combined retrieval/generation/state-mutation query
    algebra.
  - It has extensional bind unit and associativity laws.
  - `StatefulGenCalc` is mutually expressive with it.
  - Ordinary `ReflexiveQuery` embeds as a primitive stateful-generative query,
    and any observation-changing reflexive query is non-idempotent in this
    algebra.

  Remaining boundary:
  - This is still relative completeness over declared primitive transition
    relations.  It does not make arbitrary runtime/model generators faithful,
    cheap, or source-backed by itself.
-/

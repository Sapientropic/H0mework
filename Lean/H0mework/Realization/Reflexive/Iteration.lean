/-
  Proposition 99: repeated stateful queries are the iterated time-field section.

  Proposition 81 proved the one-step bridge:

      stateful query output = generated recollection time edge.

  Proposition 98 then lifted the generated edge to a `Nat`-indexed temporal
  section.  This file welds those together at the execution level.  Repeating
  the stateful-generative plan for a reflexive query `n` times produces exactly
  the observation trace along the generated time field and ends at exactly the
  `n`th section of that field.

  This is the query-algebra face of recollection as temporal activation:
  repeated non-idempotent queries are not repeated SELECTs; they are a fold over
  the generated memory time section.
-/

import H0mework.Realization.Reflexive.GeneratedEdge
import H0mework.Realization.Reflexive.NaturalTime

namespace StatefulGenAlg

/-! ## Repeating a stateful-generative query -/

/-- Execute the same stateful-generative query `n` times, collecting the rows
emitted at each step and threading the state forward. -/
def repeatEval {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (plan : StatefulGenAlg State Row Prim) :
    Nat -> State -> List Row -> State -> Prop
  | 0, x, rows, y => rows = [] /\ y = x
  | Nat.succ n, x, rows, y =>
      exists row mid tail,
        StatefulGenAlg.eval env plan x row mid /\
          repeatEval env plan n mid tail y /\
          rows = row :: tail

end StatefulGenAlg

/-! ## The canonical observation trace along a generated time field -/

/-- The list of observations read along the first `n` edges of the generated
temporal section. -/
def reflexiveQueryIteratedObservationTrace
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    State -> Nat -> List Observation
  | _x, 0 => []
  | x, Nat.succ n =>
      q.read x :: reflexiveQueryIteratedObservationTrace q (q.write x) n

/-- THEOREM 1: the generated observation trace has exactly one row per
executed edge. -/
theorem reflexiveQueryIteratedObservationTrace_length
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    forall n,
      (reflexiveQueryIteratedObservationTrace q x n).length = n := by
  intro n
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simp [reflexiveQueryIteratedObservationTrace, ih (q.write x)]

/-- Shifting the initial state by one write is the same as shifting the
generated time index by one. -/
theorem reflexiveQueryIterated_stateAt_shift
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) (n : Nat) :
    (reflexiveQueryIteratedTimeField q (q.write x)).stateAt n =
      (reflexiveQueryIteratedTimeField q x).stateAt (Nat.succ n) := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simpa [reflexiveQueryIteratedTimeField,
        Function.iterate_succ_apply'] using congrArg q.write (ih x)

/-! ## Repeated reflexive plans equal the iterated time field -/

/-- THEOREM 2: executing the stateful-generative embedding of a reflexive query
`n` times is exactly the generated observation trace plus the `n`th generated
time-field section. -/
theorem reflexiveStatefulPlan_repeatEval_iff_iteratedTimeField
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    forall n x rows y,
      StatefulGenAlg.repeatEval (reflexiveQueryPrimitive q)
          (reflexiveQueryStatefulPlan q) n x rows y <->
        rows = reflexiveQueryIteratedObservationTrace q x n /\
          y = (reflexiveQueryIteratedTimeField q x).stateAt n := by
  intro n
  induction n with
  | zero =>
      intro x rows y
      simp [StatefulGenAlg.repeatEval, reflexiveQueryIteratedObservationTrace,
        reflexiveQueryIteratedTimeField]
  | succ n ih =>
      intro x rows y
      constructor
      · rintro ⟨row, mid, tail, hstep, htail, hrows⟩
        rcases (reflexiveQueryStatefulPlan_eval q x row mid).mp hstep with
          ⟨hrow, hmid⟩
        subst row
        subst mid
        rcases (ih (q.write x) tail y).mp htail with ⟨htailRows, hy⟩
        constructor
        · simpa [reflexiveQueryIteratedObservationTrace, htailRows] using hrows
        · calc
            y = (reflexiveQueryIteratedTimeField q (q.write x)).stateAt n := hy
            _ = (reflexiveQueryIteratedTimeField q x).stateAt (Nat.succ n) :=
              reflexiveQueryIterated_stateAt_shift q x n
      · rintro ⟨hrows, hy⟩
        refine ⟨q.read x, q.write x,
          reflexiveQueryIteratedObservationTrace q (q.write x) n, ?_, ?_, ?_⟩
        · exact (reflexiveQueryStatefulPlan_eval q x (q.read x)
            (q.write x)).mpr ⟨rfl, rfl⟩
        · exact (ih (q.write x)
            (reflexiveQueryIteratedObservationTrace q (q.write x) n)
            y).mpr ⟨rfl, by
              calc
                y = (reflexiveQueryIteratedTimeField q x).stateAt
                    (Nat.succ n) := hy
                _ = (reflexiveQueryIteratedTimeField q (q.write x)).stateAt n :=
                    (reflexiveQueryIterated_stateAt_shift q x n).symm⟩
        · simpa [reflexiveQueryIteratedObservationTrace] using hrows

/-- THEOREM 3: the repeated reflexive stateful plan always has the canonical
generated execution trace. -/
theorem reflexiveStatefulPlan_repeatEval_canonical
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) (n : Nat) :
    StatefulGenAlg.repeatEval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q) n x
        (reflexiveQueryIteratedObservationTrace q x n)
        ((reflexiveQueryIteratedTimeField q x).stateAt n) := by
  exact (reflexiveStatefulPlan_repeatEval_iff_iteratedTimeField q n x
    (reflexiveQueryIteratedObservationTrace q x n)
    ((reflexiveQueryIteratedTimeField q x).stateAt n)).mpr ⟨rfl, rfl⟩

/-- THEOREM 4: any repeated execution of the reflexive stateful plan has the
canonical generated observation trace. -/
theorem reflexiveStatefulPlan_repeatEval_rows_eq_trace
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) {n : Nat} {x y : State}
    {rows : List Observation}
    (h :
      StatefulGenAlg.repeatEval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q) n x rows y) :
    rows = reflexiveQueryIteratedObservationTrace q x n :=
  (reflexiveStatefulPlan_repeatEval_iff_iteratedTimeField q n x rows y).mp h |>.1

/-- THEOREM 5: any repeated execution of the reflexive stateful plan ends at
the generated time-field section. -/
theorem reflexiveStatefulPlan_repeatEval_final_state
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) {n : Nat} {x y : State}
    {rows : List Observation}
    (h :
      StatefulGenAlg.repeatEval (reflexiveQueryPrimitive q)
        (reflexiveQueryStatefulPlan q) n x rows y) :
    y = (reflexiveQueryIteratedTimeField q x).stateAt n :=
  (reflexiveStatefulPlan_repeatEval_iff_iteratedTimeField q n x rows y).mp h |>.2

/-!
  Summary:
  - `StatefulGenAlg.repeatEval` is the fold/execution semantics for repeated
    stateful-generative queries.
  - For a reflexive query primitive, that fold is deterministic and equals the
    P98 generated temporal section.
  - The row trace is exactly the sequence of reads along the section; the final
    state is exactly the section at time `n`.
  - This upgrades P81's one-edge bridge to an n-step bridge between
    non-idempotent query execution and memory time geometry.
-/

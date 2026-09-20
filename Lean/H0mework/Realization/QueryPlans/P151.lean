/-
  Proposition 151: F-only closure for the stateful/Kleisli query algebra.

  P150 proved the pointwise ReflexiveQuery theorem:

      write = id  ==>  no reflexive obstruction / no memory production.

  The remaining seam was the P73 stateful-generative query syntax.  P73 already
  supplies the database-shaped algebra:

      State -> Row -> State -> Prop

  with `bind` threading the written state forward.  This file proves the
  F-only closure theorem directly on that syntax:

    * if every primitive transition is state-preserving, every
      `StatefulGenAlg` query is state-preserving;
    * `bind` is explicitly closed under state preservation;
    * the matching `StatefulGenCalc.existsSeq` calculus is also closed;
    * therefore no stateful query tree built from F-only primitives can produce
      a read-after-write observation change.

  Boundary: this closes the structural P73/Kleisli bind seam.  It still does
  not prove topological understanding regions, nor does it say every concrete
  runtime primitive has been certified as F-only/non-F-only.
-/

import H0mework.Realization.Reflexive.P150
import H0mework.Realization.Reflexive.GenerativeAlgebra

/-! ## F-only stateful query semantics -/

/-- Primitive transitions are F-only when each primitive leaves the state
unchanged on every emitted row. -/
def StatefulPrimitiveFOnly {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) : Prop :=
  forall p x row y, env p x row y -> y = x

/-- A stateful algebra query is F-only when every successful transition leaves
the state unchanged. -/
def StatefulAlgFOnly {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) : Prop :=
  forall x row y, StatefulGenAlg.eval env q x row y -> y = x

/-- A stateful calculus query is F-only when every successful transition leaves
the state unchanged. -/
def StatefulCalcFOnly {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (f : StatefulGenCalc State Row Prim) : Prop :=
  forall x row y, StatefulGenCalc.eval env f x row y -> y = x

/-! ## Algebra closure, with bind explicit -/

/-- THEOREM 1: `ret` is F-only. -/
theorem statefulGenAlg_ret_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop) (value : Row) :
    StatefulAlgFOnly env (StatefulGenAlg.ret value) := by
  intro x row y h
  exact h.2

/-- THEOREM 2: primitive queries are F-only when the primitive environment is.
-/
theorem statefulGenAlg_primitive_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env) (p : Prim) :
    StatefulAlgFOnly env (StatefulGenAlg.primitive p) := by
  intro x row y h
  exact hPrim p x row y h

/-- THEOREM 3: the stateful/Kleisli `bind` constructor preserves F-only. -/
theorem statefulGenAlg_bind_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim)
    (k : Row -> StatefulGenAlg State Row Prim)
    (hq : StatefulAlgFOnly env q)
    (hk : forall source, StatefulAlgFOnly env (k source)) :
    StatefulAlgFOnly env (StatefulGenAlg.bind q k) := by
  intro x row y h
  rcases h with ⟨source, mid, hqEval, hkEval⟩
  have hmid : mid = x := hq x source mid hqEval
  have hy : y = mid := hk source mid row y hkEval
  exact hy.trans hmid

/-- THEOREM 4: if all primitives are F-only, every stateful-generative algebra
query is F-only. -/
theorem statefulGenAlg_fOnly_of_primitive_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env) :
    forall q : StatefulGenAlg State Row Prim, StatefulAlgFOnly env q := by
  intro q
  induction q with
  | empty =>
      intro x row y h
      cases h
  | ret value =>
      exact statefulGenAlg_ret_fOnly env value
  | primitive p =>
      exact statefulGenAlg_primitive_fOnly env hPrim p
  | union p q ihp ihq =>
      intro x row y h
      rcases h with hp | hq
      · exact ihp x row y hp
      · exact ihq x row y hq
  | inter p q ihp _ihq =>
      intro x row y h
      exact ihp x row y h.1
  | diff p q ihp _ihq =>
      intro x row y h
      exact ihp x row y h.1
  | guard predicate q ih =>
      intro x row y h
      exact ih x row y h.2
  | bind q k ihq ihk =>
      exact statefulGenAlg_bind_fOnly env q k ihq ihk

/-! ## Calculus closure -/

/-- THEOREM 5: stateful calculus `existsSeq` preserves F-only. -/
theorem statefulGenCalc_existsSeq_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (f : StatefulGenCalc State Row Prim)
    (k : Row -> StatefulGenCalc State Row Prim)
    (hf : StatefulCalcFOnly env f)
    (hk : forall source, StatefulCalcFOnly env (k source)) :
    StatefulCalcFOnly env (StatefulGenCalc.existsSeq f k) := by
  intro x row y h
  rcases h with ⟨source, mid, hfEval, hkEval⟩
  have hmid : mid = x := hf x source mid hfEval
  have hy : y = mid := hk source mid row y hkEval
  exact hy.trans hmid

/-- THEOREM 6: if all primitives are F-only, every stateful-generative
calculus formula is F-only. -/
theorem statefulGenCalc_fOnly_of_primitive_fOnly
    {State Row Prim : Type*}
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env) :
    forall f : StatefulGenCalc State Row Prim, StatefulCalcFOnly env f := by
  intro f
  induction f with
  | falsity =>
      intro x row y h
      cases h
  | retc value =>
      intro x row y h
      exact h.2
  | pred p =>
      intro x row y h
      exact hPrim p x row y h
  | or p q ihp ihq =>
      intro x row y h
      rcases h with hp | hq
      · exact ihp x row y hp
      · exact ihq x row y hq
  | and p q ihp _ihq =>
      intro x row y h
      exact ihp x row y h.1
  | minus p q ihp _ihq =>
      intro x row y h
      exact ihp x row y h.1
  | guard predicate q ih =>
      intro x row y h
      exact ih x row y h.2
  | existsSeq f k ihf ihk =>
      exact statefulGenCalc_existsSeq_fOnly env f k ihf ihk

/-! ## No read-after-write obstruction for F-only query trees -/

/-- A stateful query creates a read obstruction at `x` when it can transition to
some output state whose observation differs from the input observation. -/
def StatefulReadObstruction {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim)
    (x : State) : Prop :=
  exists row y, StatefulGenAlg.eval env q x row y /\ read y ≠ read x

/-- THEOREM 7: an F-only stateful query has no read-after-write obstruction.
-/
theorem statefulGenAlg_no_readObstruction_of_fOnly
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim)
    (hF : StatefulAlgFOnly env q) (x : State) :
    ¬ StatefulReadObstruction read env q x := by
  rintro ⟨row, y, hEval, hChanged⟩
  have hy : y = x := hF x row y hEval
  exact hChanged (by rw [hy])

/-- THEOREM 8: if primitives are F-only, no stateful-generative algebra query
tree can create a read-after-write obstruction. -/
theorem statefulGenAlg_no_readObstruction_of_primitive_fOnly
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env)
    (q : StatefulGenAlg State Row Prim) (x : State) :
    ¬ StatefulReadObstruction read env q x := by
  exact statefulGenAlg_no_readObstruction_of_fOnly read env q
    (statefulGenAlg_fOnly_of_primitive_fOnly env hPrim q) x

/-!
  Summary:
  - F-only is stated at the stateful query layer as "every successful
    transition returns the same state".
  - `statefulGenAlg_bind_fOnly` closes the P73/Kleisli bind seam explicitly.
  - If primitives are F-only, every algebra query and every matching calculus
    formula is F-only by structural induction.
  - Therefore no stateful query tree built only from F-only primitives can
    create read-after-write obstruction.
-/

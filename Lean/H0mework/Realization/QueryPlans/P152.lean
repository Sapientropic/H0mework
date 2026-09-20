/-
  Proposition 152: storage-only no-go for the stateful query algebra.

  P151 proved that a `StatefulGenAlg` tree built from F-only primitives cannot
  create read-after-write obstruction.  This file lifts that theorem into the
  corrected P51 ontology:

      memory is recollectable potential, not passive storage.

  A stateful query induces a recollection act whose single atom fires exactly
  when some generated transition changes the downstream read.  Therefore a
  query tree whose primitives are F-only has no recollectable memory potential
  at any state.  This is the P73/Kleisli form of the storage no-go theorem:
  finite F-only query composition cannot bootstrap memory from stored data.

  Boundary: this is still the canonical read-obstruction/recollection act for
  the formal stateful query algebra.  It does not classify concrete runtime
  primitives or prove topological understanding regions.
-/

import H0mework.Realization.QueryPlans.P151

/-! ## Stateful recollection act induced by a query tree -/

/-- The canonical atom for stateful-generative recollection: a query tree has
made a downstream observation/read change possible. -/
inductive StatefulRecollectionAtom where
  | readChanged
  deriving DecidableEq, Repr

/-- A stateful query tree induces a recollection act.  It fires at `x` exactly
when the query can produce some transition whose output state is read
differently from the input state. -/
def statefulRecollectionAct {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) :
    RecollectionAct State StatefulRecollectionAtom where
  fires := fun x atom =>
    match atom with
    | StatefulRecollectionAtom.readChanged =>
        StatefulReadObstruction read env q x

/-- THEOREM 1: stateful read obstruction is exactly the canonical stateful
recollection act firing. -/
theorem statefulReadObstruction_iff_recollectionActFires
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) (x : State) :
    StatefulReadObstruction read env q x <->
      (statefulRecollectionAct read env q).fires x
        StatefulRecollectionAtom.readChanged := by
  rfl

/-- THEOREM 2: stateful read obstruction is exactly recollectable potential for
the canonical stateful recollection act. -/
theorem statefulReadObstruction_iff_recollectablePotential
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim) (x : State) :
    StatefulReadObstruction read env q x <->
      RecollectableMemoryPotential (statefulRecollectionAct read env q) x := by
  constructor
  · intro h
    exact ⟨StatefulRecollectionAtom.readChanged, h⟩
  · rintro ⟨atom, hfire⟩
    cases atom
    exact hfire

/-! ## F-only query trees cannot bootstrap recollectable potential -/

/-- THEOREM 3: an F-only stateful query tree has no recollectable memory
potential for its canonical stateful recollection act. -/
theorem statefulGenAlg_fOnly_no_recollectablePotential
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (q : StatefulGenAlg State Row Prim)
    (hF : StatefulAlgFOnly env q) (x : State) :
    ¬ RecollectableMemoryPotential (statefulRecollectionAct read env q) x := by
  exact (statefulReadObstruction_iff_recollectablePotential read env q x).not.mp
    (statefulGenAlg_no_readObstruction_of_fOnly read env q hF x)

/-- THEOREM 4: if all primitives are F-only, no stateful-generative algebra
query tree can bootstrap recollectable memory potential. -/
theorem statefulGenAlg_primitive_fOnly_no_recollectablePotential
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env)
    (q : StatefulGenAlg State Row Prim) (x : State) :
    ¬ RecollectableMemoryPotential (statefulRecollectionAct read env q) x := by
  exact statefulGenAlg_fOnly_no_recollectablePotential read env q
    (statefulGenAlg_fOnly_of_primitive_fOnly env hPrim q) x

/-! ## Calculus form -/

/-- A stateful calculus formula induces the same kind of recollection act. -/
def statefulCalcRecollectionAct {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (f : StatefulGenCalc State Row Prim) :
    RecollectionAct State StatefulRecollectionAtom where
  fires := fun x atom =>
    match atom with
    | StatefulRecollectionAtom.readChanged =>
        exists row y, StatefulGenCalc.eval env f x row y /\ read y ≠ read x

/-- THEOREM 5: an F-only stateful calculus formula has no recollectable memory
potential for its canonical stateful recollection act. -/
theorem statefulGenCalc_fOnly_no_recollectablePotential
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (f : StatefulGenCalc State Row Prim)
    (hF : StatefulCalcFOnly env f) (x : State) :
    ¬ RecollectableMemoryPotential (statefulCalcRecollectionAct read env f) x := by
  rintro ⟨atom, hfire⟩
  cases atom
  rcases hfire with ⟨row, y, hEval, hChanged⟩
  have hy : y = x := hF x row y hEval
  exact hChanged (by rw [hy])

/-- THEOREM 6: if all primitives are F-only, no stateful-generative calculus
formula can bootstrap recollectable memory potential. -/
theorem statefulGenCalc_primitive_fOnly_no_recollectablePotential
    {State Row Prim Observation : Type*}
    (read : State -> Observation)
    (env : Prim -> State -> Row -> State -> Prop)
    (hPrim : StatefulPrimitiveFOnly env)
    (f : StatefulGenCalc State Row Prim) (x : State) :
    ¬ RecollectableMemoryPotential (statefulCalcRecollectionAct read env f) x := by
  exact statefulGenCalc_fOnly_no_recollectablePotential read env f
    (statefulGenCalc_fOnly_of_primitive_fOnly env hPrim f) x

/-!
  Summary:
  - `statefulRecollectionAct` is the P51-style activation layer induced by a
    stateful query tree.
  - Its recollectable potential is equivalent to stateful read-after-write
    obstruction.
  - Because P151 proves F-only query trees have no such obstruction, finite
    F-only stateful algebra/calculus trees cannot bootstrap memory from
    storage-only data.
-/

/-
  Proposition 51: memory as recollectability, not stored state.

  Proposition 48 supplied a finite strong-isomorphism witness between
  reflexive algebra and an independently specified memory ontology.  The
  philosophical correction is sharper:

      memory is not stored data;
      memory is recollectable potential;
      recollection is the attention-like activation act.

  This file makes that distinction explicit.  Storage alone can contain data
  while producing no recollectable memory.  The object that matches reflexive
  read/write algebra is a recollection act: a read-triggered write loop that can
  fire and leave a trace available for later recall.

  Boundary: this is still the finite algebraic foundation.  It does not claim
  that the whole AIppocampus runtime has already been represented as this act
  language; that remains the mechanism-faithfulness step.
-/

import H0mework.Realization.Fields.Support

/-! ## Storage is not yet memory -/

/-- Stored data is only a potential substrate.  It may exist without any
recollection act that can activate it. -/
structure StoredData (State Datum : Type*) where
  stored : State -> Datum -> Prop

/-- A recollection act is the activation layer: at a state, one or more
recollection atoms may fire. -/
structure RecollectionAct (State Atom : Type*) where
  fires : State -> Atom -> Prop

/-- Memory, in this corrected ontology, is recollectable potential: some
recollection act can fire at this state. -/
def RecollectableMemoryPotential {State Atom : Type*}
    (act : RecollectionAct State Atom) (x : State) : Prop :=
  exists atom, act.fires x atom

/-- A tiny storage-only substrate: data is present. -/
def inertStoredData : StoredData Unit Unit where
  stored := fun _ _ => True

/-- A tiny inert recollection layer: no act ever fires. -/
def inertRecollectionAct : RecollectionAct Unit Unit where
  fires := fun _ _ => False

/-- THEOREM 1: stored data alone does not force recollectable memory.  This is
the formal version of "without recollection, memory is only data." -/
theorem stored_data_does_not_force_recollectability :
    (exists datum, inertStoredData.stored () datum) /\
      ¬ RecollectableMemoryPotential inertRecollectionAct () := by
  constructor
  · exact ⟨(), trivial⟩
  · rintro ⟨atom, hfire⟩
    exact hfire

/-! ## Reflexive algebra as recollection act -/

/-- The one atom of the recollection act forced by a reflexive read/write loop:
the next observation changed after the write. -/
inductive RecollectionAtom where
  | attentionActivated
  deriving DecidableEq, Repr

/-- The canonical recollection act induced by a reflexive query.  Unlike
`StoredData`, this object is an activation event: it fires exactly when
read-after-write differs from read-before-write. -/
def reflexiveRecollectionAct {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    RecollectionAct State RecollectionAtom where
  fires := fun x atom =>
    match atom with
    | RecollectionAtom.attentionActivated =>
        ReflexiveLambdaObstruction q x

/-- THEOREM 2: local reflexive λ obstruction is exactly the canonical
recollection act firing.  The alignment is with recollection, not with passive
storage. -/
theorem reflexiveObstruction_iff_recollectionActFires
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveLambdaObstruction q x <->
      (reflexiveRecollectionAct q).fires x RecollectionAtom.attentionActivated := by
  rfl

/-- THEOREM 3: local reflexive λ obstruction is exactly recollectable memory
potential for the canonical recollection act. -/
theorem reflexiveObstruction_iff_recollectablePotential
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveLambdaObstruction q x <->
      RecollectableMemoryPotential (reflexiveRecollectionAct q) x := by
  constructor
  · intro h
    exact ⟨RecollectionAtom.attentionActivated, h⟩
  · rintro ⟨atom, hfire⟩
    cases atom
    exact hfire

/-! ## Independent two-point recollection witness -/

/-- An independently named recollection atom.  It is not `RecollectionAtom`;
the bridge below has to prove the atom equivalence. -/
inductive IndependentRecollectionAtom where
  | recollectionCommitted
  deriving DecidableEq, Repr

/-- Independent recollection-act semantics for the two-point trace algebra.
The silent state has a recollection act available; the already changed state
does not.  This definition does not mention `ReflexiveLambdaObstruction`. -/
def independentTwoPointRecollectionAct :
    RecollectionAct TwoPointTraceState IndependentRecollectionAtom where
  fires
    | TwoPointTraceState.silent,
      IndependentRecollectionAtom.recollectionCommitted => True
    | TwoPointTraceState.changed,
      IndependentRecollectionAtom.recollectionCommitted => False

/-- THEOREM 4: the independent recollection act realizes every truth
assignment over its single atom. -/
theorem independentTwoPointRecollectionAct_independent :
    SupportIndependent TwoPointTraceState IndependentRecollectionAtom
      independentTwoPointRecollectionAct.fires := by
  intro assignment
  by_cases h : assignment IndependentRecollectionAtom.recollectionCommitted
  · refine ⟨TwoPointTraceState.silent, ?_⟩
    intro atom
    cases atom
    simp [independentTwoPointRecollectionAct, h]
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    intro atom
    cases atom
    simp [independentTwoPointRecollectionAct, h]

/-- THEOREM 5: the independent recollection act is nontrivial. -/
theorem independentTwoPointRecollectionAct_nontrivial :
    SupportNontrivial TwoPointTraceState IndependentRecollectionAtom
      independentTwoPointRecollectionAct.fires := by
  constructor
  · exact ⟨TwoPointTraceState.silent,
      IndependentRecollectionAtom.recollectionCommitted, trivial⟩
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    intro atom hfire
    cases atom
    exact hfire

/-- THEOREM 6: the reflexive recollection act in the two-point trace algebra
also realizes every truth assignment over its atom. -/
theorem twoPoint_reflexiveRecollectionAct_independent :
    SupportIndependent TwoPointTraceState RecollectionAtom
      (reflexiveRecollectionAct twoPointReflexiveQuery).fires := by
  intro assignment
  by_cases h : assignment RecollectionAtom.attentionActivated
  · refine ⟨TwoPointTraceState.silent, ?_⟩
    intro atom
    cases atom
    simp [reflexiveRecollectionAct, ReflexiveLambdaObstruction,
      twoPointReflexiveQuery, twoPointRead, twoPointWrite, h]
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    intro atom
    cases atom
    simp [reflexiveRecollectionAct, ReflexiveLambdaObstruction,
      twoPointReflexiveQuery, twoPointRead, twoPointWrite, h]

/-- THEOREM 7: the reflexive recollection act in the two-point trace algebra is
nontrivial. -/
theorem twoPoint_reflexiveRecollectionAct_nontrivial :
    SupportNontrivial TwoPointTraceState RecollectionAtom
      (reflexiveRecollectionAct twoPointReflexiveQuery).fires := by
  constructor
  · refine ⟨TwoPointTraceState.silent, RecollectionAtom.attentionActivated, ?_⟩
    simp [reflexiveRecollectionAct, ReflexiveLambdaObstruction,
      twoPointReflexiveQuery, twoPointRead, twoPointWrite]
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    intro atom hfire
    cases atom
    simp [reflexiveRecollectionAct, ReflexiveLambdaObstruction,
      twoPointReflexiveQuery, twoPointRead, twoPointWrite] at hfire

/-- The atom-level equivalence between the reflexive recollection atom and the
independently named recollection atom. -/
def recollectionAtomEquiv : RecollectionAtom ≃ IndependentRecollectionAtom where
  toFun
    | RecollectionAtom.attentionActivated =>
        IndependentRecollectionAtom.recollectionCommitted
  invFun
    | IndependentRecollectionAtom.recollectionCommitted =>
        RecollectionAtom.attentionActivated
  left_inv := by
    intro atom
    cases atom
    rfl
  right_inv := by
    intro atom
    cases atom
    rfl

/-- THEOREM 8: the two independently specified recollection acts fire on
exactly the same states. -/
theorem twoPoint_reflexiveRecollection_iff_independentAct
    (x : TwoPointTraceState) :
    (reflexiveRecollectionAct twoPointReflexiveQuery).fires x
        RecollectionAtom.attentionActivated <->
      independentTwoPointRecollectionAct.fires x
        IndependentRecollectionAtom.recollectionCommitted := by
  cases x <;>
    simp [reflexiveRecollectionAct, ReflexiveLambdaObstruction,
      twoPointReflexiveQuery, twoPointRead, twoPointWrite,
      independentTwoPointRecollectionAct]

/-- THEOREM 9: the corrected strong isomorphism: reflexive algebra is strongly
isomorphic to an independently specified recollection act, not to passive
stored data. -/
def twoPointStrongReflexiveRecollectionIso :
    StrongSupportIsomorphism TwoPointTraceState RecollectionAtom
      IndependentRecollectionAtom
      (reflexiveRecollectionAct twoPointReflexiveQuery).fires
      independentTwoPointRecollectionAct.fires where
  leftIndependent := twoPoint_reflexiveRecollectionAct_independent
  rightIndependent := independentTwoPointRecollectionAct_independent
  leftNontrivial := twoPoint_reflexiveRecollectionAct_nontrivial
  rightNontrivial := independentTwoPointRecollectionAct_nontrivial
  atomEquiv := recollectionAtomEquiv
  support_iff := by
    intro x atom
    cases atom
    exact twoPoint_reflexiveRecollection_iff_independentAct x

/-- THEOREM 10: in the two-point witness, reflexivity is exactly independent
recollectable memory potential.  This is the calibrated target statement:
not `reflexivity <-> stored state`, but
`reflexivity <-> recollection act can fire`. -/
theorem twoPoint_reflexivity_iff_independentRecollectablePotential
    (x : TwoPointTraceState) :
    ReflexiveLambdaObstruction twoPointReflexiveQuery x <->
      RecollectableMemoryPotential independentTwoPointRecollectionAct x := by
  calc
    ReflexiveLambdaObstruction twoPointReflexiveQuery x <->
        (reflexiveRecollectionAct twoPointReflexiveQuery).fires x
          RecollectionAtom.attentionActivated := by
      rfl
    _ <-> RecollectableMemoryPotential independentTwoPointRecollectionAct x := by
      constructor
      · intro h
        exact ⟨IndependentRecollectionAtom.recollectionCommitted,
          (twoPointStrongReflexiveRecollectionIso.support_iff x
            RecollectionAtom.attentionActivated).mp h⟩
      · rintro ⟨atom, hfire⟩
        cases atom
        exact (twoPointStrongReflexiveRecollectionIso.support_iff x
          RecollectionAtom.attentionActivated).mpr hfire

/-!
  Summary:
  - `stored_data_does_not_force_recollectability` separates passive storage
    from memory ontology: storage may contain data while no recollection act can
    fire.
  - `reflexiveObstruction_iff_recollectablePotential` puts the canonical
    reflexive-memory theorem at the right layer: reflexivity corresponds to
    recollection activation, and memory is recollectable potential.
  - `twoPointStrongReflexiveRecollectionIso` supplies the finite strong
    isomorphism with both sides independently specified and nontrivial.
-/

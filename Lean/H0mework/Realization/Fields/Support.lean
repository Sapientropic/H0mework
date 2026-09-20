/-
  Proposition 48: strong reflexivity-memory isomorphism needs all three
  corners.

  Proposition 45 proves an adapter-free support theorem for the one atom forced
  by reflexive read/write algebra, but that theorem is definition-close: the
  memory atom is introduced precisely as "observation changed".  Propositions
  34/40/41 go the other way: memory production is specified independently, but
  the reflexive-memory bridge is an adapter/certificate.

  This file separates the missing triangle explicitly:

    * independent support on both sides does not force a pointwise equivalence;
    * nontriviality on both sides still does not force it;
    * a strong isomorphism is a stronger object: independent supports,
      nontrivial witnesses, an atom equivalence, and support preservation.

  It then constructs a small two-point trace algebra whose reflexive read/write
  side and memory ontology side are independently defined, nontrivial, and
  unconditionally isomorphic by proof.  This is not a claim about the whole
  seven-case AIppocampus ontology; it is the finite canonical witness showing
  what the foundation has to look like when it is not an `rfl` definition and
  not an external adapter.
-/

import H0mework.Realization.Memory.SingleAtomIndependence

/-! ## Generic support-side notions -/

/-- A support predicate is independent when every truth assignment over atoms
can be realized by some state. -/
def SupportIndependent (State Atom : Type*) (produces : State -> Atom -> Prop) :
    Prop :=
  forall assignment : Atom -> Prop, exists x, forall a, produces x a <-> assignment a

/-- A support predicate is nontrivial when it has at least one producing state
and at least one silent state. -/
def SupportNontrivial (State Atom : Type*) (produces : State -> Atom -> Prop) :
    Prop :=
  (exists x a, produces x a) /\ (exists x, forall a, produces x a -> False)

/-- Pointwise nonempty support equivalence.  This is the weakest observable
shape of "both sides produce memory at exactly the same states". -/
def PointwiseNonemptyEquivalent {State Atom₁ Atom₂ : Type*}
    (left : State -> Atom₁ -> Prop) (right : State -> Atom₂ -> Prop) : Prop :=
  forall x, (exists a, left x a) <-> (exists b, right x b)

/-- THEOREM 1: independent, nontrivial support on both sides still does not
force pointwise equivalence.  The two one-atom supports over `Bool` can realize
all assignments, both have producing and silent states, and yet they fire on
opposite states. -/
theorem independent_nontrivial_supports_do_not_force_equivalence :
    exists left right : Bool -> Unit -> Prop,
      SupportIndependent Bool Unit left /\
      SupportIndependent Bool Unit right /\
      SupportNontrivial Bool Unit left /\
      SupportNontrivial Bool Unit right /\
      ¬ PointwiseNonemptyEquivalent left right := by
  let left : Bool -> Unit -> Prop := fun x _ => x = true
  let right : Bool -> Unit -> Prop := fun x _ => x = false
  refine ⟨left, right, ?_, ?_, ?_, ?_, ?_⟩
  · intro assignment
    by_cases h : assignment ()
    · refine ⟨true, ?_⟩
      intro a
      cases a
      simp [left, h]
    · refine ⟨false, ?_⟩
      intro a
      cases a
      simp [left, h]
  · intro assignment
    by_cases h : assignment ()
    · refine ⟨false, ?_⟩
      intro a
      cases a
      simp [right, h]
    · refine ⟨true, ?_⟩
      intro a
      cases a
      simp [right, h]
  · constructor
    · exact ⟨true, (), rfl⟩
    · refine ⟨false, ?_⟩
      intro a
      cases a
      simp [left]
  · constructor
    · exact ⟨false, (), rfl⟩
    · refine ⟨true, ?_⟩
      intro a
      cases a
      simp [right]
  · intro hequiv
    have hleft : exists a, left true a := ⟨(), rfl⟩
    rcases (hequiv true).mp hleft with ⟨a, ha⟩
    cases a
    simp [right] at ha

/-! ## Strong support isomorphism, not merely an adapter -/

/-- A strong support isomorphism packages the three corners required for a
nontrivial identification:

* both support languages are independently realizable;
* both are nontrivial;
* atom names are equivalent and support is preserved by that equivalence.

Unlike `ReflexiveMemoryAdapter`, this is not a state classifier.  It is an
atom-level isomorphism between two independently specified support languages. -/
structure StrongSupportIsomorphism
    (State LeftAtom RightAtom : Type*)
    (left : State -> LeftAtom -> Prop)
    (right : State -> RightAtom -> Prop) where
  leftIndependent : SupportIndependent State LeftAtom left
  rightIndependent : SupportIndependent State RightAtom right
  leftNontrivial : SupportNontrivial State LeftAtom left
  rightNontrivial : SupportNontrivial State RightAtom right
  atomEquiv : LeftAtom ≃ RightAtom
  support_iff : forall x a, left x a <-> right x (atomEquiv a)

namespace StrongSupportIsomorphism

variable {State LeftAtom RightAtom : Type*}
variable {left : State -> LeftAtom -> Prop}
variable {right : State -> RightAtom -> Prop}

/-- THEOREM 2: a strong atom-level support isomorphism gives pointwise nonempty
support equivalence. -/
theorem pointwiseNonemptyEquivalent
    (I : StrongSupportIsomorphism State LeftAtom RightAtom left right) :
    PointwiseNonemptyEquivalent left right := by
  intro x
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨I.atomEquiv a, (I.support_iff x a).mp ha⟩
  · rintro ⟨b, hb⟩
    let a := I.atomEquiv.symm b
    have hb' : right x (I.atomEquiv a) := by
      simpa [a] using hb
    exact ⟨a, (I.support_iff x a).mpr hb'⟩

/-- THEOREM 3: strong support isomorphism preserves silence. -/
theorem silent_iff
    (I : StrongSupportIsomorphism State LeftAtom RightAtom left right)
    (x : State) :
    (forall a, left x a -> False) <->
      (forall b, right x b -> False) := by
  constructor
  · intro hleft b hb
    let a := I.atomEquiv.symm b
    have hb' : right x (I.atomEquiv a) := by
      simpa [a] using hb
    exact hleft a ((I.support_iff x a).mpr hb')
  · intro hright a ha
    exact hright (I.atomEquiv a) ((I.support_iff x a).mp ha)

end StrongSupportIsomorphism

/-! ## A concrete two-point reflexive algebra with independent memory ontology -/

/-- The smallest trace-state space with one changing point and one silent
point. -/
inductive TwoPointTraceState where
  | silent
  | changed
  deriving DecidableEq, Repr

/-- The observation alphabet for the two-point trace algebra. -/
inductive TwoPointObservation where
  | quiet
  | marked
  deriving DecidableEq, Repr

/-- Read the current trace mark. -/
def twoPointRead : TwoPointTraceState -> TwoPointObservation
  | TwoPointTraceState.silent => TwoPointObservation.quiet
  | TwoPointTraceState.changed => TwoPointObservation.marked

/-- Write the trace mark.  The `changed` state is absorbing, so the algebra has
both one observation-changing state and one silent state. -/
def twoPointWrite : TwoPointTraceState -> TwoPointTraceState
  | TwoPointTraceState.silent => TwoPointTraceState.changed
  | TwoPointTraceState.changed => TwoPointTraceState.changed

/-- The concrete reflexive query for the two-point trace algebra. -/
def twoPointReflexiveQuery :
    ReflexiveQuery TwoPointTraceState TwoPointObservation where
  read := twoPointRead
  write := twoPointWrite

/-- A memory atom introduced independently of `ReflexiveMemoryAtom`. -/
inductive IndependentTraceMemoryAtom where
  | traceCommitted
  deriving DecidableEq, Repr

/-- Independent memory production: the memory side says that the silent state
needs a trace-commit memory event.  This definition does not mention
`ReflexiveLambdaObstruction` or `ReflexiveMemoryProduction`. -/
def independentTraceMemoryProduces :
    TwoPointTraceState -> IndependentTraceMemoryAtom -> Prop
  | TwoPointTraceState.silent, IndependentTraceMemoryAtom.traceCommitted => True
  | TwoPointTraceState.changed, IndependentTraceMemoryAtom.traceCommitted => False

/-- Independent memory silence: the already changed state produces no new
trace memory. -/
def independentTraceMemorySilent : TwoPointTraceState -> Prop
  | TwoPointTraceState.silent => False
  | TwoPointTraceState.changed => True

/-- The independent one-atom memory contract for the two-point algebra. -/
def independentTraceMemoryContract :
    MemoryProductionContract TwoPointTraceState IndependentTraceMemoryAtom where
  produces := independentTraceMemoryProduces
  memorySilent := independentTraceMemorySilent
  product_shape := by
    intro x
    cases x <;> constructor
    · intro h
      cases h
    · intro h
      exact h IndependentTraceMemoryAtom.traceCommitted trivial
    · intro _ atom hprod
      cases atom
      exact hprod
    · intro _
      trivial
  independent := by
    intro assignment
    by_cases h : assignment IndependentTraceMemoryAtom.traceCommitted
    · refine ⟨TwoPointTraceState.silent, ?_⟩
      intro atom
      cases atom
      simp [independentTraceMemoryProduces, h]
    · refine ⟨TwoPointTraceState.changed, ?_⟩
      intro atom
      cases atom
      simp [independentTraceMemoryProduces, h]

/-- THEOREM 4: the independent memory contract is nontrivial. -/
theorem independentTraceMemory_nontrivial :
    SupportNontrivial TwoPointTraceState IndependentTraceMemoryAtom
      independentTraceMemoryContract.produces := by
  constructor
  · exact ⟨TwoPointTraceState.silent, IndependentTraceMemoryAtom.traceCommitted,
      trivial⟩
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    intro atom hprod
    cases atom
    exact hprod

/-- THEOREM 5: the two-point reflexive algebra is nontrivial: one state changes
the next read observation and one state does not. -/
theorem twoPoint_reflexive_nontrivial :
    (exists x, ReflexiveLambdaObstruction twoPointReflexiveQuery x) /\
      (exists x, ¬ ReflexiveLambdaObstruction twoPointReflexiveQuery x) := by
  constructor
  · refine ⟨TwoPointTraceState.silent, ?_⟩
    simp [ReflexiveLambdaObstruction, twoPointReflexiveQuery, twoPointRead,
      twoPointWrite]
  · refine ⟨TwoPointTraceState.changed, ?_⟩
    simp [ReflexiveLambdaObstruction, twoPointReflexiveQuery, twoPointRead,
      twoPointWrite]

/-- THEOREM 6: the reflexive side also realizes both one-atom truth
assignments.  This is the one-atom independence condition, proved from the
two concrete states rather than assumed as an adapter. -/
theorem twoPoint_reflexiveMemoryAtomIndependent :
    ReflexiveMemoryAtomIndependent twoPointReflexiveQuery := by
  apply (reflexiveMemoryAtomIndependent_iff_change_and_silence
    twoPointReflexiveQuery).mpr
  constructor
  · exact twoPoint_reflexive_nontrivial.1
  · rcases twoPoint_reflexive_nontrivial.2 with ⟨x, hx⟩
    exact ⟨x, (reflexiveMemorySilent_iff_no_obstruction
      twoPointReflexiveQuery x).mpr hx⟩

/-- The atom-level equivalence between the algebraic reflexive atom and the
independent memory-ontology atom. -/
def reflexiveTraceAtomEquiv : ReflexiveMemoryAtom ≃ IndependentTraceMemoryAtom where
  toFun
    | ReflexiveMemoryAtom.observationChanged =>
        IndependentTraceMemoryAtom.traceCommitted
  invFun
    | IndependentTraceMemoryAtom.traceCommitted =>
        ReflexiveMemoryAtom.observationChanged
  left_inv := by
    intro a
    cases a
    rfl
  right_inv := by
    intro a
    cases a
    rfl

/-- THEOREM 7: local reflexive obstruction is exactly independent memory
production in the two-point algebra.  This is proved from the independently
defined read/write and memory tables; it is not `rfl` and uses no adapter. -/
theorem twoPoint_reflexiveObstruction_iff_independentMemory
    (x : TwoPointTraceState) :
    ReflexiveLambdaObstruction twoPointReflexiveQuery x <->
      independentTraceMemoryContract.produces x
        IndependentTraceMemoryAtom.traceCommitted := by
  cases x <;>
    simp [ReflexiveLambdaObstruction, twoPointReflexiveQuery, twoPointRead,
      twoPointWrite, independentTraceMemoryContract,
      independentTraceMemoryProduces]

/-- THEOREM 8: the full atom-level strong support isomorphism for the two-point
trace algebra.  Both languages are independent, both are nontrivial, atom names
are equivalent, and support preservation is a theorem. -/
def twoPointStrongReflexiveMemoryIso :
    StrongSupportIsomorphism TwoPointTraceState ReflexiveMemoryAtom
      IndependentTraceMemoryAtom
      (ReflexiveMemoryProduction twoPointReflexiveQuery)
      independentTraceMemoryContract.produces where
  leftIndependent := by
    exact twoPoint_reflexiveMemoryAtomIndependent
  rightIndependent := independentTraceMemoryContract.independent
  leftNontrivial := by
    constructor
    · rcases twoPoint_reflexive_nontrivial.1 with ⟨x, hx⟩
      exact ⟨x, ReflexiveMemoryAtom.observationChanged, hx⟩
    · rcases twoPoint_reflexive_nontrivial.2 with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      intro atom hprod
      cases atom
      exact hx hprod
  rightNontrivial := independentTraceMemory_nontrivial
  atomEquiv := reflexiveTraceAtomEquiv
  support_iff := by
    intro x atom
    cases atom
    exact twoPoint_reflexiveObstruction_iff_independentMemory x

/-- THEOREM 9: as a consequence of the strong isomorphism, the reflexive
algebra and the independent memory ontology have the same producing states. -/
theorem twoPoint_reflexivity_iff_memoryOntology
    (x : TwoPointTraceState) :
    ReflexiveLambdaObstruction twoPointReflexiveQuery x <->
      exists m, independentTraceMemoryContract.produces x m := by
  calc
    ReflexiveLambdaObstruction twoPointReflexiveQuery x <->
        ReflexiveMemoryProduction twoPointReflexiveQuery x
          ReflexiveMemoryAtom.observationChanged := by
      rfl
    _ <-> exists m, independentTraceMemoryContract.produces x m := by
      constructor
      · intro h
        exact ⟨IndependentTraceMemoryAtom.traceCommitted,
          (twoPointStrongReflexiveMemoryIso.support_iff x
            ReflexiveMemoryAtom.observationChanged).mp h⟩
      · rintro ⟨m, hm⟩
        cases m
        exact (twoPointStrongReflexiveMemoryIso.support_iff x
          ReflexiveMemoryAtom.observationChanged).mpr hm

/-!
  Summary:
  - `independent_nontrivial_supports_do_not_force_equivalence` proves the
    missing negative boundary: independence plus nontriviality is still not a
    bridge.
  - `twoPointStrongReflexiveMemoryIso` is the first closed triangle: an
    independent reflexive algebra, an independent memory ontology, nontrivial
    witnesses on both sides, and an unconditional atom-level support
    isomorphism constructed by proof.
  - This is a finite foundational witness, not a full runtime theorem.  A real
    AIppocampus trace surface still needs a representation theorem showing it
    maps faithfully into this or a richer strong-isomorphism object.
-/

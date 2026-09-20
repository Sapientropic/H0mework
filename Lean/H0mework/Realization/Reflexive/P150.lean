/-
  Proposition 150: F-only memory flatness and strict reflexive witness.

  The structural condition for F-only is not "memory production is zero".
  It is the query-algebra condition:

      write = id

  From that condition Lean proves that read-after-write never changes, hence
  reflexive λ obstruction is false and canonical reflexive memory production is
  empty at every state.

  The file also proves the finite-composition closure of F-only writes and
  records the strict contrast: the existing two-point reflexive trace algebra
  has genuine nonzero memory production.

  Boundary: this proves the structural write/id version of F-only flatness and
  finite write-chain closure.  It does not yet connect this closure to P30's
  full Kleisli `bind` syntax, nor does it prove the topological "understanding
  region" conjecture.
-/

import H0mework.Realization.Reflexive.P149

/-! ## F-only as `write = id` -/

/-- F-only/reflection-free query: the write-back component is exactly the
identity on state. -/
def FOnlyReflexiveQuery {State Observation : Type*}
    (q : ReflexiveQuery State Observation) : Prop :=
  forall x, q.write x = x

/-- THEOREM 1: F-only queries have no local reflexive λ obstruction. -/
theorem fOnly_no_reflexiveLambdaObstruction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (hF : FOnlyReflexiveQuery q) (x : State) :
    ¬ ReflexiveLambdaObstruction q x := by
  intro hobs
  have hread : q.read (q.write x) = q.read x := by
    rw [hF x]
  exact hobs hread

/-- THEOREM 2: F-only queries produce no canonical reflexive memory atom. -/
theorem fOnly_no_reflexiveMemoryProduction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (hF : FOnlyReflexiveQuery q) (x : State)
    (atom : ReflexiveMemoryAtom) :
    ¬ ReflexiveMemoryProduction q x atom := by
  cases atom with
  | observationChanged =>
      exact fOnly_no_reflexiveLambdaObstruction q hF x

/-- THEOREM 3: every state is silent for canonical reflexive memory under an
F-only query. -/
theorem fOnly_reflexiveMemorySilentAt
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (hF : FOnlyReflexiveQuery q) (x : State) :
    ReflexiveMemorySilentAt q x := by
  intro atom hprod
  exact fOnly_no_reflexiveMemoryProduction q hF x atom hprod

/-- THEOREM 4: F-only queries have no recollectable memory potential for the
canonical P51 recollection act. -/
theorem fOnly_no_canonicalRecollectablePotential
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (hF : FOnlyReflexiveQuery q) (x : State) :
    ¬ RecollectableMemoryPotential (reflexiveRecollectionAct q) x := by
  exact (reflexiveObstruction_iff_recollectablePotential q x).not.mp
    (fOnly_no_reflexiveLambdaObstruction q hF x)

/-! ## Finite composition closure -/

/-- Sequentially compose two reflexive queries at the write layer.  The read
component is paired only to keep a concrete `ReflexiveQuery`; the F-only
closure theorem below depends solely on the write component. -/
def composeReflexiveQuery
    {State Observation₁ Observation₂ : Type*}
    (q₁ : ReflexiveQuery State Observation₁)
    (q₂ : ReflexiveQuery State Observation₂) :
    ReflexiveQuery State (Observation₁ × Observation₂) where
  read := fun x => (q₁.read x, q₂.read x)
  write := fun x => q₂.write (q₁.write x)

/-- THEOREM 5: F-only queries are closed under sequential composition. -/
theorem fOnly_composeReflexiveQuery
    {State Observation₁ Observation₂ : Type*}
    (q₁ : ReflexiveQuery State Observation₁)
    (q₂ : ReflexiveQuery State Observation₂)
    (h₁ : FOnlyReflexiveQuery q₁)
    (h₂ : FOnlyReflexiveQuery q₂) :
    FOnlyReflexiveQuery (composeReflexiveQuery q₁ q₂) := by
  intro x
  unfold composeReflexiveQuery
  dsimp
  rw [h₁ x]
  exact h₂ x

/-- A finite write chain. -/
def writeChain {State : Type*} : List (State -> State) -> State -> State
  | [] => fun x => x
  | write :: rest => fun x => writeChain rest (write x)

/-- THEOREM 6: a finite chain of identity writes is identity. -/
theorem writeChain_eq_id_of_all_fOnly
    {State : Type*} (writes : List (State -> State))
    (hF : forall write, write ∈ writes -> forall x, write x = x) :
    forall x, writeChain writes x = x := by
  induction writes with
  | nil =>
      intro x
      rfl
  | cons write rest ih =>
      intro x
      have hwrite : write x = x := hF write (by simp) x
      have hrest : forall write', write' ∈ rest -> forall x, write' x = x := by
        intro write' hmem x'
        exact hF write' (by simp [hmem]) x'
      simp [writeChain, hwrite, ih hrest x]

/-- Build a reflexive query from a read and a finite write chain. -/
def writeChainReflexiveQuery
    {State Observation : Type*}
    (read : State -> Observation) (writes : List (State -> State)) :
    ReflexiveQuery State Observation where
  read := read
  write := writeChain writes

/-- THEOREM 7: a finite chain of F-only writes is an F-only reflexive query. -/
theorem writeChainReflexiveQuery_fOnly
    {State Observation : Type*}
    (read : State -> Observation) (writes : List (State -> State))
    (hF : forall write, write ∈ writes -> forall x, write x = x) :
    FOnlyReflexiveQuery (writeChainReflexiveQuery read writes) := by
  intro x
  exact writeChain_eq_id_of_all_fOnly writes hF x

/-- THEOREM 8: finite F-only write chains produce no canonical reflexive memory.
This is the finite no-go form: more F-only reasoning still cannot bootstrap
memory production. -/
theorem writeChain_fOnly_no_reflexiveMemoryProduction
    {State Observation : Type*}
    (read : State -> Observation) (writes : List (State -> State))
    (hF : forall write, write ∈ writes -> forall x, write x = x)
    (x : State) (atom : ReflexiveMemoryAtom) :
    ¬ ReflexiveMemoryProduction (writeChainReflexiveQuery read writes) x atom := by
  exact fOnly_no_reflexiveMemoryProduction
    (writeChainReflexiveQuery read writes)
    (writeChainReflexiveQuery_fOnly read writes hF)
    x atom

/-! ## Strict reflexive witness -/

/-- THEOREM 9: the two-point reflexive trace algebra has genuine nonzero
canonical reflexive memory production. -/
theorem twoPoint_reflexiveMemoryProduction_nonzero :
    ReflexiveMemoryProduction twoPointReflexiveQuery
      TwoPointTraceState.silent ReflexiveMemoryAtom.observationChanged := by
  simp [ReflexiveMemoryProduction, ReflexiveLambdaObstruction,
    twoPointReflexiveQuery, twoPointRead, twoPointWrite]

/-- THEOREM 10: the same witness has recollectable memory potential. -/
theorem twoPoint_recollectablePotential_nonzero :
    RecollectableMemoryPotential
      (reflexiveRecollectionAct twoPointReflexiveQuery)
      TwoPointTraceState.silent := by
  exact (reflexiveObstruction_iff_recollectablePotential
    twoPointReflexiveQuery TwoPointTraceState.silent).mp
    twoPoint_reflexiveMemoryProduction_nonzero

/-!
  Summary:
  - `FOnlyReflexiveQuery` is the structural condition `write = id`, not a
    disguised zero-memory predicate.
  - `fOnly_no_reflexiveMemoryProduction` proves F-only flatness.
  - `writeChain_fOnly_no_reflexiveMemoryProduction` proves the finite no-go:
    finite composition of F-only writes cannot bootstrap canonical reflexive
    memory.
  - `twoPoint_reflexiveMemoryProduction_nonzero` proves strictness: reflexive
    write-back can produce memory where F-only cannot.
-/

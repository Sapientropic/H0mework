/-
  Proposition 35: reflexive query algebra.

  Proposition 33 introduced a single reflexive query as a read paired with a
  trace/state write.  Proposition 34 connected observation-changing reflexivity
  to memory production under a certified adapter.  This file makes the query
  side algebraic:

    * reflexive queries compose sequentially;
    * the no-op query is a two-sided unit;
    * composition is associative when observations form a monoid;
    * traditional read-only queries embed as mutation-free reflexive queries;
    * the global λ no-go reason is exactly non-observation-idempotence;
    * a concrete query can be non-idempotent under sequential composition.

  Boundary: this is the algebra of state-transforming reads.  It is not a
  runtime mechanism-faithfulness proof that AIppocampus trace/retrieval code
  instantiates a particular query.
-/

import H0mework.Realization.Memory.ReflexiveSupport

namespace ReflexiveQuery

variable {State Observation : Type*}

/-- Extensional equality for reflexive queries. -/
theorem ext {q r : ReflexiveQuery State Observation}
    (hread : forall x, q.read x = r.read x)
    (hwrite : forall x, q.write x = r.write x) :
    q = r := by
  cases q with
  | mk qread qwrite =>
      cases r with
      | mk rread rwrite =>
          have hreadFun : qread = rread := funext hread
          have hwriteFun : qwrite = rwrite := funext hwrite
          cases hreadFun
          cases hwriteFun
          rfl

/-- Sequential composition.  The second query reads the state written by the
    first query; observations are accumulated by the observation monoid. -/
def seq [Mul Observation]
    (q r : ReflexiveQuery State Observation) :
    ReflexiveQuery State Observation where
  read := fun x => q.read x * r.read (q.write x)
  write := fun x => r.write (q.write x)

/-- The no-op reflexive query: emits the neutral observation and leaves state
    unchanged. -/
def skip [One Observation] : ReflexiveQuery State Observation where
  read := fun _ => 1
  write := id

/-- Traditional read-only queries embed as reflexive queries with identity
    write. -/
def pureRead (read : State -> Observation) : ReflexiveQuery State Observation where
  read := read
  write := id

/-- Sequential composition has `skip` as a left unit. -/
theorem seq_skip_left [Monoid Observation]
    (q : ReflexiveQuery State Observation) :
    seq (skip : ReflexiveQuery State Observation) q = q := by
  apply ext
  · intro x
    simp [seq, skip]
  · intro x
    rfl

/-- Sequential composition has `skip` as a right unit. -/
theorem seq_skip_right [Monoid Observation]
    (q : ReflexiveQuery State Observation) :
    seq q (skip : ReflexiveQuery State Observation) = q := by
  apply ext
  · intro x
    simp [seq, skip]
  · intro x
    rfl

/-- Sequential composition is associative. -/
theorem seq_assoc [Monoid Observation]
    (p q r : ReflexiveQuery State Observation) :
    seq (seq p q) r = seq p (seq q r) := by
  apply ext
  · intro x
    simp [seq, mul_assoc]
  · intro x
    rfl

/-- Pure read-only queries are state-idempotent. -/
theorem pureRead_state_idempotent (read : State -> Observation) :
    StateIdempotent (pureRead read) := by
  intro x
  rfl

/-- Pure read-only queries are observation-idempotent. -/
theorem pureRead_observation_idempotent (read : State -> Observation) :
    ObservationIdempotent (pureRead read) := by
  intro x
  rfl

/-- Sequential composition of pure reads is still a pure read. -/
theorem pureRead_seq_pureRead [Monoid Observation]
    (left right : State -> Observation) :
    seq (pureRead left) (pureRead right) =
      pureRead (fun x => left x * right x) := by
  apply ext
  · intro x
    simp [seq, pureRead]
  · intro x
    rfl

/-- The Proposition 34 no-global-λ reason is exactly failure of observation
    idempotence. -/
theorem noGlobalReason_iff_not_observationIdempotent
    (q : ReflexiveQuery State Observation) :
    NoGlobalLambdaReason q <-> (ObservationIdempotent q -> False) := by
  classical
  constructor
  · intro h hidem
    rcases h with ⟨x, hx⟩
    exact hx (hidem x)
  · intro h
    by_contra hno
    apply h
    intro x
    by_contra hx
    exact hno ⟨x, hx⟩

/-! ## A concrete non-idempotent algebra witness -/

/-- A reflexive query that logs the current counter and increments it. -/
def counterProduct : ReflexiveQuery Nat Nat where
  read := fun n => n + 1
  write := Nat.succ

/-- Running the counter query twice accumulates two multiplicative observations. -/
theorem counterProduct_seq_read_zero :
    (seq counterProduct counterProduct).read 0 = 2 := by
  norm_num [seq, counterProduct]

/-- Sequentially composing a reflexive query with itself can change the query:
    reflexive query algebra is not an idempotent SELECT algebra. -/
theorem counterProduct_seq_not_idempotent :
    seq counterProduct counterProduct ≠ counterProduct := by
  intro h
  have hread := congrArg (fun q : ReflexiveQuery Nat Nat => q.read 0) h
  norm_num [seq, counterProduct] at hread

end ReflexiveQuery

/-!
  Summary:
  - Reflexive queries form a sequential algebra whose state component is
    ordered by writes, not a traditional idempotent read algebra.
  - Pure reads embed as the mutation-free/idempotent subalgebra.
  - The obstruction tested by Proposition 34 is exactly the negation of
    observation idempotence.
-/

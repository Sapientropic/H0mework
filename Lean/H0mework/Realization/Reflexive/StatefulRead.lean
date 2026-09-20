/-
  Proposition 33: reflexive query algebra and non-existence of unguarded λ.

  A reflexive query is not a traditional idempotent read: it returns an
  observation and writes a trace/update back to state.  This file proves the
  small negative core:

    * reflexive queries can be non-idempotent;
    * an unguarded/global λ would require read-after-write and read-before-write
      observations to commute everywhere;
    * if a write changes the read observation anywhere, no global λ certificate
      exists.

  Boundary: this is the abstract algebraic obstruction.  It does not yet prove
  that a specific runtime trace reducer has exactly this `read/write` pair.
-/

import H0mework.Realization.Memory.EpistemicTypes

/-! ## Reflexive queries as state-transforming reads -/

/-- A reflexive query reads an observation and writes a new state. -/
structure ReflexiveQuery (State Observation : Type*) where
  read : State -> Observation
  write : State -> State

namespace ReflexiveQuery

/-- Running a reflexive query returns the current observation and the written
    state. -/
def run {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Observation × State :=
  (q.read x, q.write x)

/-- The state reached after running a reflexive query once. -/
def next {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : State :=
  q.write x

/-- A reflexive query is state-idempotent when writing twice is the same as
    writing once.  Traditional read-only queries satisfy this trivially; trace
    writes need not. -/
def StateIdempotent {State Observation : Type*}
    (q : ReflexiveQuery State Observation) : Prop :=
  forall x, q.write (q.write x) = q.write x

/-- A reflexive query is observation-idempotent when the second run observes the
    same value as the first. -/
def ObservationIdempotent {State Observation : Type*}
    (q : ReflexiveQuery State Observation) : Prop :=
  forall x, q.read (q.write x) = q.read x

/-- A concrete non-idempotent reflexive query: read the counter, then increment
    it. -/
def natCounter : ReflexiveQuery Nat Nat where
  read := fun n => n
  write := Nat.succ

/-- THEOREM 1: reflexive query writes need not be state-idempotent. -/
theorem natCounter_not_state_idempotent : ¬ StateIdempotent natCounter := by
  intro h
  have h0 := h 0
  norm_num [natCounter] at h0

/-- THEOREM 2: reflexive query observations need not be idempotent. -/
theorem natCounter_not_observation_idempotent :
    ¬ ObservationIdempotent natCounter := by
  intro h
  have h0 := h 0
  norm_num [natCounter] at h0

end ReflexiveQuery

/-! ## Unguarded/global λ non-existence -/

/-- The two routes whose equality an unguarded reflexive λ would need:
    `readAfterWrite` observes after the trace write; `readBeforeWrite` observes
    before the trace write. -/
def readAfterWrite {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Observation :=
  q.read (q.write x)

def readBeforeWrite {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Observation :=
  q.read x

/-- A global λ is unguarded when its certified domain is all states and its two
    routes are read-after-write and read-before-write. -/
structure UnguardedLambdaCertificate
    (State Observation Obstruction : Type*)
    (q : ReflexiveQuery State Observation) where
  cert : CertifiedPartialLambda State Observation Obstruction
  domain_all : forall x, cert.O x
  fg_eq : cert.FG = readAfterWrite q
  gf_eq : cert.GF = readBeforeWrite q

/-- THEOREM 3: any unguarded λ certificate forces observation idempotence. -/
theorem unguarded_lambda_implies_observation_idempotent
    {State Observation Obstruction : Type*}
    (q : ReflexiveQuery State Observation)
    (cert : UnguardedLambdaCertificate State Observation Obstruction q) :
    ReflexiveQuery.ObservationIdempotent q := by
  intro x
  have hcomm := cert.cert.commute_on_O x (cert.domain_all x)
  have hfg : cert.cert.FG x = readAfterWrite q x := by
    rw [cert.fg_eq]
  have hgf : cert.cert.GF x = readBeforeWrite q x := by
    rw [cert.gf_eq]
  exact hfg.symm.trans (hcomm.trans hgf)

/-- THEOREM 4: if a write changes the read observation anywhere, no unguarded
    λ certificate exists. -/
theorem no_unguarded_lambda_of_observation_change
    {State Observation Obstruction : Type*}
    (q : ReflexiveQuery State Observation)
    (hchange : exists x, q.read (q.write x) ≠ q.read x) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  intro cert
  rcases hchange with ⟨x, hx⟩
  exact hx (unguarded_lambda_implies_observation_idempotent q cert x)

/-- THEOREM 5: the counter reflexive query has no unguarded λ. -/
theorem natCounter_no_unguarded_lambda (Obstruction : Type*) :
    UnguardedLambdaCertificate Nat Nat Obstruction ReflexiveQuery.natCounter -> False := by
  exact no_unguarded_lambda_of_observation_change
    ReflexiveQuery.natCounter
    ⟨0, by norm_num [ReflexiveQuery.natCounter]⟩

/-!
  Summary:
  - Reflexive queries are state-transforming reads, not idempotent SELECTs.
  - A global unguarded λ exists only when read-before-write and read-after-write
    observations are equal everywhere.
  - Observation-changing trace writes force λ failure.  Proposition 9's partial
    fail-closed λ is therefore not merely cautious; it is the only honest shape
    for such a reflexive loop.
-/

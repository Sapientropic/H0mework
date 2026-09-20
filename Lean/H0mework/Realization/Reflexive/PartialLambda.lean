/-
  Proposition 9: certified partial distributive law.

  The global, unconditional λ is intentionally NOT claimed here.  This file
  proves the small algebraic core that is safe to state:

    * Oλ names the certified domain where the two routes FG and GF commute.
    * Inside Oλ, the certified partial λ returns the GF observation and carries
      the proof that FG = GF.
    * Outside Oλ, the total runtime attempt is fail-closed: it returns only an
      obstruction, returns no observation, and preserves the original state.

  Runtime membership in Oλ is a separate mechanism-faithfulness obligation.
-/

import Mathlib

/-! ## Certified partial λ -/

/-- A certified partial distributive law.

`O` is the certified domain.  `FG` and `GF` are the two routes whose equality is
available only on `O`.  Outside `O`, the runtime may expose only an obstruction.
-/
structure CertifiedPartialLambda (State Observation Obstruction : Type*) where
  O : State → Prop
  FG : State → Observation
  GF : State → Observation
  obstruction : State → Obstruction
  commute_on_O : ∀ x, O x → FG x = GF x

/-- Runtime result of trying to apply a certified partial λ.

The obstructed branch deliberately keeps the original state and exposes no
observation value.  This is the Lean-level shape of the fail-closed gate.
-/
inductive LambdaAttempt (State Observation Obstruction : Type*) where
  | commuted (state : State) (value : Observation) :
      LambdaAttempt State Observation Obstruction
  | obstructed (state : State) (diagnostic : Obstruction) :
      LambdaAttempt State Observation Obstruction

namespace LambdaAttempt

/-- The attempt keeps a state handle in either branch. -/
def state {State Observation Obstruction : Type*} :
    LambdaAttempt State Observation Obstruction → State
  | commuted state _ => state
  | obstructed state _ => state

/-- Only the certified branch exposes an observation. -/
def observation? {State Observation Obstruction : Type*} :
    LambdaAttempt State Observation Obstruction → Option Observation
  | commuted _ value => some value
  | obstructed _ _ => none

end LambdaAttempt

/-- Total runtime gate for a certified partial λ.

The `Decidable` argument is the explicit check for membership in `Oλ`.  If it
fails, the gate returns an obstruction instead of fabricating a commuting value.
-/
def tryLambda {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction) (x : State)
    [Decidable (Λ.O x)] : LambdaAttempt State Observation Obstruction :=
  if _h : Λ.O x then
    LambdaAttempt.commuted x (Λ.GF x)
  else
    LambdaAttempt.obstructed x (Λ.obstruction x)

/-! ## Acceptance theorems -/

/-- THEOREM 1: on the certified domain, FG and GF commute. -/
theorem certified_lambda_commutes_on_domain {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) (h : Λ.O x) : Λ.FG x = Λ.GF x :=
  Λ.commute_on_O x h

/-- THEOREM 2: on the certified domain, the runtime gate returns the commuting
GF observation and the route equality proof is available. -/
theorem tryLambda_commutes_on_domain {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) [Decidable (Λ.O x)] (h : Λ.O x) :
    tryLambda Λ x = LambdaAttempt.commuted x (Λ.GF x) ∧ Λ.FG x = Λ.GF x := by
  constructor
  · simp [tryLambda, h]
  · exact Λ.commute_on_O x h

/-- THEOREM 3: outside the certified domain, the runtime gate returns only the
obstruction branch. -/
theorem tryLambda_obstructs_off_domain {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) [Decidable (Λ.O x)] (h : ¬ Λ.O x) :
    tryLambda Λ x = LambdaAttempt.obstructed x (Λ.obstruction x) := by
  simp [tryLambda, h]

/-- THEOREM 4: applying the gate never changes the state handle. -/
theorem tryLambda_preserves_state {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) [Decidable (Λ.O x)] :
    (tryLambda Λ x).state = x := by
  by_cases h : Λ.O x
  · simp [tryLambda, h, LambdaAttempt.state]
  · simp [tryLambda, h, LambdaAttempt.state]

/-- THEOREM 5: fail-closed means no observation is exposed outside `Oλ`. -/
theorem tryLambda_no_observation_off_domain {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) [Decidable (Λ.O x)] (h : ¬ Λ.O x) :
    (tryLambda Λ x).observation? = none := by
  simp [tryLambda, h, LambdaAttempt.observation?]

/-- THEOREM 6: the off-domain branch is state-preserving, diagnostic-only, and
observation-free. -/
theorem tryLambda_fail_closed_off_domain {State Observation Obstruction : Type*}
    (Λ : CertifiedPartialLambda State Observation Obstruction)
    (x : State) [Decidable (Λ.O x)] (h : ¬ Λ.O x) :
    (tryLambda Λ x).state = x ∧
      tryLambda Λ x = LambdaAttempt.obstructed x (Λ.obstruction x) ∧
      (tryLambda Λ x).observation? = none := by
  constructor
  · exact tryLambda_preserves_state Λ x
  · constructor
    · exact tryLambda_obstructs_off_domain Λ x h
    · exact tryLambda_no_observation_off_domain Λ x h

/-!
  Summary:
  - certified_lambda_commutes_on_domain: Oλ ⟹ FG = GF.
  - tryLambda_commutes_on_domain: the gate returns a commuting value on Oλ.
  - tryLambda_obstructs_off_domain: outside Oλ, only obstruction is returned.
  - tryLambda_preserves_state: the gate does not mutate the state handle.
  - tryLambda_no_observation_off_domain: outside Oλ, no observation leaks.
  - tryLambda_fail_closed_off_domain: bundled fail-closed theorem.

  This proves the abstract shape of a certified partial λ.  It does not prove
  that a concrete runtime reducer belongs to Oλ; that remains a separate
  mechanism-faithfulness / certificate-generation obligation.
-/

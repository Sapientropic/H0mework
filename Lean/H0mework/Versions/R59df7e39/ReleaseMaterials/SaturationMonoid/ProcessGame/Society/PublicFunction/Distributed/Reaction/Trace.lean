import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

def traceFrom (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) : Nat → Events code → code.Frame → Events code
  | 0, _, _ => []
  | remaining + 1, past, frame => match opponent history past frame with
      | none => []
      | some event => event.val :: traceFrom policy initial history opponent remaining
          (past ++ [event.val]) (code.step policy initial frame event.val)

def trace (policy : code.Policy)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) : Events code :=
  traceFrom code policy (code.historyCurrent history) history opponent code.eventLimit [] code.start

def execution (policy : code.Policy)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) : code.Frame :=
  code.replay policy (code.historyCurrent history) (trace code policy history opponent)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem traceFrom_is_supported (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) (remaining : Nat) (past : Events code) (frame : code.Frame) :
    (traceFrom code policy initial history opponent remaining past frame).length ≤ remaining ∧
      ∀ event ∈ traceFrom code policy initial history opponent remaining past frame, event ∈ code.eventAlphabet := by
  induction remaining generalizing past frame with
  | zero => exact ⟨Nat.le_refl _, by simp [traceFrom]⟩
  | succ remaining ih =>
    simp only [traceFrom]
    split
    next => exact ⟨Nat.zero_le _, by simp⟩
    next event _ =>
      obtain ⟨bounded, supported⟩ := ih (past ++ [event.val]) (code.step policy initial frame event.val)
      exact ⟨Nat.succ_le_succ bounded, fun request inside =>
        (List.mem_cons.mp inside).elim (fun same => same ▸ event.property) (supported request)⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem replay_append_one (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)
    (events : Events code) (event : Event Party Good Port Technology Instrument code.sites) :
    code.replay policy initial (events ++ [event]) = code.step policy initial (code.replay policy initial events) event := by
  simp only [Code.replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem one_restriction_preserves_every_continuation
    (policy : code.Policy) (generated : policy ∈ code.policies)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories) (opponent : Opponent code)
    (remaining : Nat) (past : Events code) (bounded : past.length + remaining ≤ code.eventLimit)
    (supported : ∀ event ∈ past, event ∈ code.eventAlphabet) :
    traceFrom code policy (code.historyCurrent history) history (respond code (restrict code opponent)) remaining
        past (code.replay policy (code.historyCurrent history) past) =
      traceFrom code policy (code.historyCurrent history) history opponent remaining
        past (code.replay policy (code.historyCurrent history) past) := by
  induction remaining generalizing past with
  | zero => rfl
  | succ remaining ih =>
    have inside := every_reachable_decision_is_a_key code policy generated history original past (by omega) supported
    have same := restriction_agrees_on_every_reachable_decision code opponent
      (history, past, code.replay policy (code.historyCurrent history) past) inside
    simp only [traceFrom, same]
    split
    next => rfl
    next event _ =>
      congr 1
      rw [← replay_append_one]
      apply ih (past ++ [event.val])
      · simp only [List.length_append, List.length_singleton]; omega
      · intro request member
        rcases List.mem_append.mp member with before | last
        · exact supported request before
        · have same := List.mem_singleton.mp last
          exact same ▸ event.property

/-- One table represents the opponent simultaneously on every candidate and
every original history. It is not chosen separately for the two arms. -/
theorem every_history_adaptive_opponent_has_one_joint_table (opponent : Opponent code) :
    ∃ table ∈ tables code, ∀ policy ∈ code.policies, ∀ history ∈ code.histories,
      trace code policy history (respond code table) = trace code policy history opponent := by
  refine ⟨restrict code opponent, restriction_is_generated code opponent, ?_⟩
  intro policy generated history original
  exact one_restriction_preserves_every_continuation code policy generated history original opponent
    code.eventLimit [] (by simp) (by simp)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem actual_reactive_script_is_enumerated (policy : code.Policy)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (original : history ∈ code.histories) (opponent : Opponent code)
    (eligible : code.eligible (trace code policy history opponent) = true) :
    (history, trace code policy history opponent) ∈ code.scenarios := by
  obtain ⟨bounded, supported⟩ := traceFrom_is_supported code policy (code.historyCurrent history)
    history opponent code.eventLimit [] code.start
  exact List.mem_product.mpr ⟨original, List.mem_filter.mpr
    ⟨(mem_sequences_iff _ _ _).mpr ⟨bounded, supported⟩, eligible⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

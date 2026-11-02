import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure Input where
  opponent : Opponent code
  budget : Nat

structure State where
  current : RawCurrent Party Good Technology Instrument
  history : History (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  past : Events code
  frame : code.Frame
  remaining : Nat

def decision (input : Input code) (state : State code) : Move code :=
  if state.remaining = 0 then none else input.opponent state.history state.past state.frame

/-- A cut executes only its new word. Mailboxes and packet addresses survive;
new packet timestamps use the full submitted-word coordinate. -/
def stepLocal (policy : code.Policy) (state : State code) (event : Event Party Good Port Technology Instrument code.sites) :=
  code.step policy state.current {state.frame with word := []} event

def word (policy : Option code.Policy) (input : Input code) (state : State code) :
    RawEvent Party Good Port Technology Instrument :=
  match policy, decision code input state with
  | some policy, some event => (stepLocal code policy state event.val).word
  | _, _ => []

def advance (policy : Option code.Policy) (input : Input code) (state : State code) : State code :=
  let submitted := word code policy input state
  let frame := match policy, decision code input state with
    | some policy, some event =>
        let next := stepLocal code policy state event.val
        {next with word := state.frame.word ++ submitted
                   sent := state.frame.sent ++ (next.sent.drop state.frame.sent.length).map
                     (fun packet => {packet with sentAfter := state.frame.word.length + packet.sentAfter})}
    | _, _ => state.frame
  ⟨code.law.next state.current submitted, state.history ++ [submitted],
    match policy, decision code input state with
    | some _, some event => state.past ++ [event.val]
    | _, _ => state.past,
    frame, state.remaining - 1⟩

def run (policy : Option code.Policy) (input : Input code) (initial : State code) : Nat → State code
  | 0 => initial
  | n + 1 => advance code policy input (run policy input initial n)

theorem next_current (policy : Option code.Policy) (input : Input code) (state : State code) :
    (advance code policy input state).current = code.law.next state.current (word code policy input state) := rfl

theorem history_keeps_every_actual_word (policy : Option code.Policy) (input : Input code) (state : State code) :
    (advance code policy input state).history = state.history ++ [word code policy input state] := rfl

theorem remaining_is_the_original_cut_budget (policy : Option code.Policy) (input : Input code) (initial : State code) (n : Nat) :
    (run code policy input initial n).remaining = initial.remaining - n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, advance, ih, Nat.sub_sub]

theorem stopped_emits_no_request (policy : Option code.Policy) (input : Input code) (state : State code)
    (stopped : state.remaining = 0) : word code policy input state = [] := by
  simp only [word, decision, stopped]
  cases policy <;> rfl

theorem event_memory_is_extended (policy : code.Policy) (input : Input code) (state : State code)
    (event : Choice code) (chosen : decision code input state = some event) :
    (advance code (some policy) input state).past = state.past ++ [event.val] := by
  simp only [advance, chosen]

theorem packets_keep_their_original_addresses (policy : code.Policy) (input : Input code) (state : State code)
    (event : Choice code) (chosen : decision code input state = some event) :
    state.frame.sent <+: (advance code (some policy) input state).frame.sent := by
  simp only [advance, chosen]
  exact List.prefix_append _ _

theorem frame_records_only_the_new_word (policy : code.Policy) (input : Input code) (state : State code)
    (event : Choice code) (chosen : decision code input state = some event) :
    (advance code (some policy) input state).frame.word =
      state.frame.word ++ word code (some policy) input state := by
  simp only [advance, chosen]

theorem activation_uses_only_the_delivered_signal (policy : code.Policy) (state : State code)
    (site : Fin code.sites) :
    (stepLocal code policy state (.activate site)).word = code.action policy site (state.frame.inbox site) := rfl

theorem past_grows_by_at_most_one (policy : Option code.Policy) (input : Input code) (state : State code) :
    (advance code policy input state).past.length ≤ state.past.length + 1 := by
  unfold advance
  cases policy <;> cases decision code input state <;> simp

theorem all_future_events_fit_the_cut_budget (policy : Option code.Policy) (input : Input code)
    (initial : State code) (n : Nat) :
    (run code policy input initial n).past.length ≤ initial.past.length + n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      exact le_trans (past_grows_by_at_most_one code policy input (run code policy input initial n)) (by omega)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback

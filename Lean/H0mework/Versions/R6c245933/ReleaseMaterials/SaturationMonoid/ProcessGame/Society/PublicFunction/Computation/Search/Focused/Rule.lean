import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Complete

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

/-- Retain all possible local readings of the source clock's sole owner. -/
def focus (active : List (Fin code.sites)) (rule : Rule code) : Rule code where
  work := ⟨fun key listed => if key.1 ∈ active then rule.work.val key listed else [],by
    apply code.every_local_policy_is_enumerated
    intro key listed
    split
    · exact (List.mem_pi _ _).mp rule.work.property key listed
    · exact (mem_words_iff _ _ _).mpr ⟨by simp,by simp⟩⟩
  events := fun key listed => if key.1 ∈ active then rule.events key listed
    else ⟨none,List.mem_cons_self⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_owned_local_row_is_retained (active : List (Fin code.sites)) (site : Fin code.sites) (signal : Fin code.signals)
    (rule : Rule code) (owned : site ∈ active) :
    (focus code active rule).work.val (site,signal) (code.key_mem _) = rule.work.val (site,signal) (code.key_mem _) ∧
    localEvent code (focus code active rule) site signal = localEvent code rule site signal := by
  simp [focus,localEvent,owned]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_focused_driver_makes_the_same_actual_decision
    (start : Nat) (active : List (Fin code.sites)) (rule : Rule code) (rival : Opponent code)
    (history : History) (past : Events code) (frame : code.Frame)
    (available : ∀ site, Distributed.Recall.Information.Agency.ownerAt code start history.length = some site → site ∈ active) :
    driver code start (focus code active rule) rival history past frame =
      driver code start rule rival history past frame := by
  cases owner : Distributed.Recall.Information.Agency.ownerAt code start history.length with
  | none => simp only [driver,owner]
  | some site =>
      simp only [driver,owner]
      exact (every_owned_local_row_is_retained code active site (frame.inbox site) rule (available site owner)).2

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_focused_row_has_the_same_whole_frame_effect
    (start : Nat) (active : List (Fin code.sites)) (rule : Rule code) (rival : Opponent code)
    (history : History) (past : Events code) (observed frame : code.Frame)
    (initial : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (event : Reaction.Choice code)
    (chosen : driver code start rule rival history past observed = some event)
    (available : ∀ site, Distributed.Recall.Information.Agency.ownerAt code start history.length = some site → site ∈ active) :
    code.step (focus code active rule).work.val initial frame event.val =
      code.step rule.work.val initial frame event.val := by
  cases owner : Distributed.Recall.Information.Agency.ownerAt code start history.length with
  | none =>
      have external := Distributed.Recall.Information.Agency.external_input_cannot_impersonate_a_workers_event code _ event
        (by simpa only [driver,owner] using chosen)
      rcases event with ⟨event,supported⟩
      cases event with
      | adversary => rfl
      | send => cases external
      | deliver => rfl
      | activate => cases external
  | some site =>
      have localChoice : localEvent code rule site (observed.inbox site) = some event := by simpa only [driver,owner] using chosen
      have owned := every_local_event_has_its_own_worker code rule site (observed.inbox site) event localChoice
      rcases event with ⟨event,supported⟩
      cases event with
      | adversary => cases owned
      | send sender recipient => rfl
      | deliver => cases owned
      | activate worker =>
          change worker = site at owned
          subst worker
          have action : code.action (focus code active rule).work.val site (frame.inbox site) = code.action rule.work.val site (frame.inbox site) := by
            unfold Code.action
            rw [(every_owned_local_row_is_retained code active site (frame.inbox site) rule (available site owner)).1]
          simp only [Code.step,action]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_focused_rule_generates_the_same_actual_next
    (start : Nat) (active : List (Fin code.sites)) (rule : Rule code) (rival : Opponent code)
    (state : State code) (budget : Nat)
    (available : ∀ site, Distributed.Recall.Information.Agency.ownerAt code start state.history.length = some site → site ∈ active) :
    Feedback.advance code
      (some (focus code active rule).work.val)
      ⟨driver code start (focus code active rule) rival,budget⟩ state =
    Feedback.advance code (some rule.work.val) ⟨driver code start rule rival,budget⟩ state := by
  have same := the_focused_driver_makes_the_same_actual_decision code start active rule rival state.history state.past state.frame available
  by_cases stopped : state.remaining = 0
  · simp [Feedback.advance,Feedback.word,Feedback.decision,stopped]
  · cases chosen : driver code start rule rival state.history state.past state.frame with
    | none => simp [Feedback.advance,Feedback.word,Feedback.decision,stopped,same,chosen]
    | some event =>
        have effect := the_focused_row_has_the_same_whole_frame_effect code start active rule rival state.history state.past state.frame
          {state.frame with word := []} state.current event chosen available
        simp [Feedback.advance,Feedback.word,Feedback.decision,stopped,same,chosen,Feedback.stepLocal,effect]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused

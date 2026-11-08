import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueSource
open Institutions.Capitalism.Universal.Source.Program
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State queued prepared delay)
open InletOmissionSource (Controller Command)
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Code" => Active old instructions

-- A fixed baseline remembers attempts made before the production continuation.
structure Preserves (first last : Cursor Code) : Prop where
  sent : (EventStep.seed last).frame.sent = (EventStep.seed first).frame.sent
  inbox : (EventStep.seed last).frame.inbox = (EventStep.seed first).frame.inbox
  attempts : ∀ baseline, QueueScheduler.attempted Code baseline (EventStep.seed last).past =
    QueueScheduler.attempted Code baseline (EventStep.seed first).past

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem append_adversary (baseline : Nat) (past : Events Code)
    (request : Request Party Good Port (Mandate.State Party Technology) Instrument) :
    QueueScheduler.attempted Code baseline (past ++ [.adversary request]) =
      QueueScheduler.attempted Code baseline past := by
  unfold QueueScheduler.attempted
  rw [List.drop_append,List.filterMap_append]
  have empty : (([Event.adversary request] : Events Code).drop (baseline - past.length)).filterMap
      (QueueScheduler.address Code) = [] := by
    cases baseline - past.length <;> simp [QueueScheduler.address]
  rw [empty,List.append_nil]

private theorem adversary_step (cursor : Cursor Code) (rival : Opponent Code)
    (only : ∀ history past frame event, rival history past frame = some event →
      ∃ request, event.val = .adversary request) :
    Preserves old instructions cursor (cursor.after SilentWindow.quiet rival) := by
  have actual := EventStep.actual_next_state cursor SilentWindow.quiet rival
  have shape : decision Code (EventStep.applied cursor SilentWindow.quiet rival) (EventStep.seed cursor) = none ∨
      ∃ event, decision Code (EventStep.applied cursor SilentWindow.quiet rival) (EventStep.seed cursor) = some event ∧
        ∃ request, event.val = .adversary request := by
    unfold decision EventStep.applied Cursor.controller driver
    split
    · exact Or.inl rfl
    · dsimp only
      split
      · exact Or.inl rfl
      · cases found : rival (EventStep.seed cursor).history (EventStep.seed cursor).past (EventStep.seed cursor).frame with
        | none => exact Or.inl rfl
        | some event =>
          obtain ⟨request,same⟩ := only _ _ _ event found
          refine Or.inr ⟨event,?_,request,same⟩
          simp only [Distributed.Recall.Information.Agency.externalChoice,same]
  rcases shape with none | ⟨event,chosen,request,same⟩
  · refine ⟨?_,?_,?_⟩ <;> simp [actual,Feedback.advance,word,none]
  · refine ⟨?_,?_,?_⟩
    · simp only [actual,Feedback.advance,word,chosen,stepLocal,same,Distributed.Code.step,
        List.drop_length,List.map_nil,List.append_nil]
    · simp only [actual,Feedback.advance,word,chosen,stepLocal,same,Distributed.Code.step]
    · intro baseline
      simp only [actual,Feedback.advance,chosen]
      rw [same]
      exact append_adversary old instructions baseline _ request

private theorem block (state : State old instructions) (command : Command
    (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    Preserves old instructions state.cursor (InletOmissionSource.after old instructions state command).cursor := by
  have quiet := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
  have only : ∀ history past frame event,
      (InletOmissionSource.stage old instructions state command).2 history past frame = some event →
      ∃ request, event.val = .adversary request := by
    intro history past frame event found
    simp only [InletOmissionSource.stage,LiveProductionInletSource.stage,
      queued,List.append_nil] at found
    cases queue : state.pending ++ command.incoming with
    | nil => simp only [queue,EventStep.fixed] at found;contradiction
    | cons head tail =>
      simp only [queue,LiveProductionInletSource.rival,EventStep.fixed] at found
      split at found
      · exact ⟨head,LiveProductionInletSource.admitted_request_is_the_source_instruction old instructions head event found⟩
      · contradiction
  have step := adversary_step old instructions (prepared old instructions state)
    (InletOmissionSource.stage old instructions state command).2 only
  refine ⟨step.sent.trans (congrArg (fun frame => frame.sent) quiet.frame),
    step.inbox.trans (congrArg (fun frame => frame.inbox) quiet.frame),?_⟩
  intro baseline
  exact (step.attempts baseline).trans (congrArg (QueueScheduler.attempted Code baseline) quiet.past)

theorem production_and_omission_preserve_the_original_live_communication
    (control : Controller old instructions) (count remaining : Nat) (state : State old instructions) :
    Preserves old instructions state.cursor (InletOmissionSource.run old instructions control count remaining state).state.cursor := by
  induction count generalizing remaining state with
  | zero => exact ⟨rfl,rfl,fun _ => rfl⟩
  | succ count ih =>
    by_cases empty : remaining = 0
    · subst remaining;rw [InletOmissionSource.stopped];exact ⟨rfl,rfl,fun _ => rfl⟩
    · rw [InletOmissionSource.active old instructions state control count remaining empty]
      have first := block old instructions state (control state)
      have later := ih (remaining - if InletOmissionSource.observe old instructions state (control state) = some .executed then 1 else 0)
        (InletOmissionSource.after old instructions state (control state))
      exact ⟨later.sent.trans first.sent,later.inbox.trans first.inbox,
        fun baseline => (later.attempts baseline).trans (first.attempts baseline)⟩

theorem every_original_stage_pays_its_opportunity (cursor : Cursor Code)
    (stages : List (EventHistory.Stage (code := Code))) :
    (EventStep.seed (EventHistory.execute cursor stages)).history.length =
        (EventStep.seed cursor).history.length + stages.length ∧
      (EventStep.seed (EventHistory.execute cursor stages)).remaining =
        (EventStep.seed cursor).remaining - stages.length ∧
      (EventHistory.execute cursor stages).ownerStart = cursor.ownerStart := by
  induction stages generalizing cursor with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons stage tail ih =>
    have later := ih (cursor.after stage.1 stage.2)
    have actual := EventStep.actual_next_state cursor stage.1 stage.2
    refine ⟨?_,?_,later.2.2⟩
    · change (EventStep.seed (EventHistory.execute (cursor.after stage.1 stage.2) tail)).history.length = _
      rw [later.1,actual]
      change ((EventStep.seed cursor).history ++ [_]).length + tail.length = _
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
    · change (EventStep.seed (EventHistory.execute (cursor.after stage.1 stage.2) tail)).remaining = _
      rw [later.2.1,actual]
      change (EventStep.seed cursor).remaining - 1 - tail.length = _
      simp only [List.length_cons];omega

variable (origin : Cursor (Active old instructions)) (state : State old instructions) (control : Controller old instructions)
  (count : Nat) (protocols : Nat → Rule (Active old instructions))
abbrev produced := InletOmissionSource.produce old instructions state control count
abbrev terminal := (produced old instructions state control count).state.cursor
abbrev horizon := OriginQueue.horizon (code := Code) origin (terminal old instructions state control count)
abbrev recoveryStages := OriginQueue.stages (code := Code) origin protocols (horizon old instructions origin state control count)
def stages := (produced old instructions state control count).stages ++
  recoveryStages old instructions origin state control count protocols
abbrev final := EventHistory.execute state.cursor (stages old instructions origin state control count protocols)
abbrev locate := QueueMemoryDeadline.locate (code := Code) origin (terminal old instructions state control count) protocols
abbrev deliveryRow := QueueMemoryDeadline.row (code := Code) origin (terminal old instructions state control count) protocols
-- This gate is computed from the actual terminal and never replenishes a spent budget.
def hasTime : Bool := decide (horizon old instructions origin state control count ≤
  (EventStep.seed (terminal old instructions state control count)).remaining)

theorem the_recovery_continues_the_complete_generated_cursor :
    final old instructions origin state control count protocols =
      EventHistory.execute (terminal old instructions state control count)
        (recoveryStages old instructions origin state control count protocols) := by
  rw [final,stages,OriginQueue.execute_append,← InletOmissionSource.every_run_is_the_original_execution]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletQueueSource

import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PersistentDutyEntry

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReadyMemory
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

structure Closed (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Prop where
  action : ∀ site old word, word ∈ words code.actions code.actionLimit → code.memoryReady old = true →
    code.memoryReady (code.afterAction site old word) = true
  send : ∀ sender recipient old reading, code.memoryReady old = true →
    code.memoryReady (code.afterSend sender recipient old reading) = true
  delivery : ∀ recipient sender old reading, code.memoryReady old = true →
    code.memoryReady (code.afterDelivery recipient sender old reading) = true

def inspect (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Bool :=
  (code.keys.all fun key => (words code.actions code.actionLimit).all fun word => decide
    (code.memoryReady key.2 = true → code.memoryReady (code.afterAction key.1 key.2 word) = true)) &&
  (code.keys.all fun key => (List.finRange code.sites).all fun recipient => (List.finRange code.signals).all fun reading => decide
    (code.memoryReady key.2 = true → code.memoryReady (code.afterSend key.1 recipient key.2 reading) = true)) &&
  (code.keys.all fun key => (List.finRange code.sites).all fun sender => (List.finRange code.signals).all fun reading => decide
    (code.memoryReady key.2 = true → code.memoryReady (code.afterDelivery key.1 sender key.2 reading) = true))

omit [DecidableEq Port] [DecidableEq Technology] in
theorem the_finite_source_interface_generates_ready_memory_closure (accepted : inspect code = true) : Closed code := by
  simp only [inspect, Bool.and_eq_true] at accepted
  have checks := and_assoc.mp accepted
  refine ⟨?_, ?_, ?_⟩
  · intro site old word supported ready
    exact (of_decide_eq_true ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.1) (site, old) (code.key_mem _))) word supported)) ready
  · intro sender recipient old reading ready
    exact (of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.2.1) (sender, old) (code.key_mem _))) recipient (List.mem_finRange _)))
        reading (List.mem_finRange _))) ready
  · intro recipient sender old reading ready
    exact (of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp
      ((List.all_eq_true.mp checks.2.2) (recipient, old) (code.key_mem _))) sender (List.mem_finRange _)))
        reading (List.mem_finRange _))) ready

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_actual_event_preserves_ready_memory (source : Closed code)
    (policy : code.Policy) (generated : policy ∈ code.policies)
    (initial : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (frame : code.Frame) (event : Event Party Good Port (Mandate.State Party Technology) Instrument code.sites)
    (site : Fin code.sites) (ready : code.memoryReady (frame.inbox site) = true) :
    code.memoryReady ((code.step policy initial frame event).inbox site) = true := by
  cases event with
  | adversary request => exact ready
  | send sender recipient =>
    simp only [Code.step]
    split
    · dsimp only
      split
      · rename_i same; subst site; exact source.send _ _ _ _ ready
      · exact ready
    · exact ready
  | deliver address =>
    simp only [Code.step]
    split
    · exact ready
    · split
      · dsimp only
        split
        · exact source.delivery _ _ _ _ ready
        · exact ready
      · exact ready
  | activate worker =>
    simp only [Code.step]
    split
    · rename_i same
      subst site
      exact source.action _ _ _ (ResponseCapacity.generated_action_is_in_the_source_alphabet policy generated _ _) ready
    · exact ready

theorem every_actual_cut_preserves_ready_memory (source : Closed code)
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (site : Fin code.sites) (ready : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = true) :
    code.memoryReady ((EventStep.seed (cursor.after protocol rival)).frame.inbox site) = true := by
  rw [EventStep.actual_next_state]
  cases chosen : decision code (EventStep.applied cursor protocol rival) (EventStep.seed cursor) with
  | none => simpa only [Reaction.Feedback.advance, chosen] using ready
  | some event =>
    simpa only [Reaction.Feedback.advance, chosen, stepLocal] using
      every_actual_event_preserves_ready_memory source protocol.work.val protocol.work.property
        (EventStep.seed cursor).current {(EventStep.seed cursor).frame with word := []} event.val site ready

theorem the_actual_history_preserves_ready_memory (source : Closed code)
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (site : Fin code.sites) (ready : code.memoryReady ((EventStep.seed cursor).frame.inbox site) = true) :
    code.memoryReady ((EventStep.seed (EventHistory.execute cursor stages)).frame.inbox site) = true := by
  induction stages generalizing cursor with
  | nil => exact ready
  | cons stage tail ih =>
    exact ih (cursor.after stage.1 stage.2)
      (every_actual_cut_preserves_ready_memory source cursor stage.1 stage.2 site ready)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReadyMemory

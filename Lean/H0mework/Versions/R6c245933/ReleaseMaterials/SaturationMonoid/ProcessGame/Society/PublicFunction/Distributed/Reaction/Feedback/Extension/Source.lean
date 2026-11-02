import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

structure Active where
  private mk ::
  sourceInput : Input source.code
  installed : source.feedback? = some sourceInput
  direct : source.continuation = []

inductive Block where
  | noFeedback (absent : source.feedback? = none)
  | explicitContinuation (present : source.continuation ≠ [])

inductive Result where
  | blocked (reason : Block source)
  | active (continuation : Active source)

/-- Recover the installed source input itself. A foreign input cannot be
silently substituted for the source's actual future. -/
def produce : Result source :=
  if direct : source.continuation = [] then
    match installed : source.feedback? with
    | none => .blocked (.noFeedback installed)
    | some sourceInput => .active ⟨sourceInput, installed, direct⟩
  else .blocked (.explicitContinuation direct)

namespace Active

variable {source} (active : Active source) (supply : Supply source.code) (cut count : Nat)

def after : State (code source.code supply) := resume source supply active.sourceInput cut count

def native := Runtime.generate source active.sourceInput active.installed active.direct (cut + count)

theorem the_target_generates_its_own_next :
    (after active supply cut (count + 1)).current =
      (code source.code supply).law.next (after active supply cut count).current
        (word (code source.code supply) (source.feedbackPolicy (cut + count))
          (input source.code supply active.sourceInput) (after active supply cut count)) := rfl

theorem all_actual_state_and_native_responsibility_are_together :
    after active supply cut count = state source.code supply (native active cut count).state :=
  resume_keeps_every_actual_source_step source supply active.sourceInput cut count

theorem every_future_request_is_the_original_actual_execution :
    word (code source.code supply) (source.feedbackPolicy (cut + count))
        (input source.code supply active.sourceInput) (after active supply cut count) =
      (source.actualExecution (source.history.length + 1 + (cut + count))).submitted := by
  rw [after, resume_keeps_every_actual_source_step, word_preserves_the_actual_request]
  exact (source.feedback_word_is_actual active.sourceInput active.installed active.direct _).symm

theorem the_target_keeps_actual_current_complete_history_ledger_and_next :
    (after active supply cut count).current =
        source.currentAt (source.history.length + 2 + (cut + count)) ∧
    (after active supply cut count).history = source.history ++ [source.responseFrame.word] ++
        source.feedbackWords (cut + count) ∧
    let runtime := (Runtime.facade source active.sourceInput active.installed active.direct).seed.advance
      (source.history.length + 2 + (cut + count))
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (Runtime.facade source active.sourceInput active.installed active.direct).process.stateAt
        ((Runtime.facade source active.sourceInput active.installed active.direct).process.successor runtime.state) := by
  have exactState := resume_keeps_every_actual_source_step source supply active.sourceInput cut count
  have rooted := (Runtime.facade source active.sourceInput active.installed active.direct).readoutAt_factorizes
    ((Runtime.facade source active.sourceInput active.installed active.direct).seed.advance
      (source.history.length + 2 + (cut + count))) .feedback
  refine ⟨?_, ?_, rooted.2.2.1, rooted.2.2.2.2⟩
  · change (resume source supply active.sourceInput cut count).current = _
    rw [exactState]
    exact (source.feedback_current_is_actual active.sourceInput active.installed active.direct _).symm
  · change (resume source supply active.sourceInput cut count).history = _
    rw [exactState]
    exact source.feedback_keeps_the_complete_actual_history active.sourceInput active.installed active.direct _

end Active

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Extension

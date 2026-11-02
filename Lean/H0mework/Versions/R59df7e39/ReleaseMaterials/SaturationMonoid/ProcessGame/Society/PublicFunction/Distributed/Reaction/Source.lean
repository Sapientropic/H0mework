import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Quantified
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

/-! Original and replacement machines run the same opponent on their own
actual currents. Shared law/history do not identify their root occurrences. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

inductive Side where | original | replacement

structure Machine (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument] where
  code : Code Party Good Port Technology Instrument
  reference : code.Policy
  reference_generated : reference ∈ code.policies
  history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  original : history ∈ code.histories
  opponent : Opponent code
  side : Side
  /-- Submitted later requests are interpreted when their actual visit arrives. -/
  continuation : List (RawEvent Party Good Port Technology Instrument) := []
  feedback? : Option (Feedback.Input code) := none
  /-- Last matching optional control wins. Explicit none suppresses that cut;
  later cuts and the initial response keep their own policies. -/
  feedbackOverrides : List (Nat × Option code.Policy) := []

namespace Machine

variable (source : Machine Party Good Port Technology Instrument)

def answer := compile source.code source.reference source.reference_generated

def policyForSide (code : Code Party Good Port Technology Instrument) (reference : code.Policy)
    (generated : reference ∈ code.policies) (side : Side) : Option code.Policy := match side with
  | .original => some reference
  | .replacement => match compile code reference generated with
      | .selected choice => some choice.policy.policy
      | .blocked _ => none

def policy? : Option source.code.Policy :=
  policyForSide source.code source.reference source.reference_generated source.side

def eventsFor (code : Code Party Good Port Technology Instrument) (policy : Option code.Policy)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) (current : RawCurrent Party Good Technology Instrument) : Events code :=
  match policy with
  | none => []
  | some policy => traceFrom code policy current history opponent code.eventLimit [] code.start

def emissionEvents (current : RawCurrent Party Good Technology Instrument) : Events source.code :=
  eventsFor source.code source.policy? source.history source.opponent current

def frameFor (code : Code Party Good Port Technology Instrument) (policy : Option code.Policy)
    (history : History (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (opponent : Opponent code) (current : RawCurrent Party Good Technology Instrument) : code.Frame :=
  match policy with
  | none => code.start
  | some active => code.replay active current (eventsFor code policy history opponent current)

def response (current : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  (frameFor source.code source.policy? source.history source.opponent current).word

def responseFrame : source.code.Frame :=
  frameFor source.code source.policy? source.history source.opponent (source.code.historyCurrent source.history)

def feedbackInitial (input : Feedback.Input source.code) : Feedback.State source.code :=
  ⟨source.code.law.next (source.code.historyCurrent source.history) source.responseFrame.word,
    source.history ++ [source.responseFrame.word],
    source.emissionEvents (source.code.historyCurrent source.history), source.responseFrame, input.budget⟩

def feedbackPolicy (index : Nat) : Option source.code.Policy :=
  source.feedbackOverrides.foldl (fun prior entry => if entry.1 = index then entry.2 else prior) source.policy?

def feedbackState (input : Feedback.Input source.code) : Nat → Feedback.State source.code
  | 0 => source.feedbackInitial input
  | index + 1 => Feedback.advance source.code (source.feedbackPolicy index) input (feedbackState input index)

def laterResponse (current : RawCurrent Party Good Technology Instrument) (index : Nat) :
    RawEvent Party Good Port Technology Instrument := match source.feedback? with
  | none => source.response current
  | some input => Feedback.word source.code (source.feedbackPolicy index) input (source.feedbackState input index)

def body (current : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  match source.history[current.round - source.code.initial.round - 1]? with
  | some word => word
  | none =>
      let index := current.round - source.code.initial.round - 1
      if source.history.length < index then
        match source.continuation[index - source.history.length - 1]? with
        | some word => word
        | none => source.laterResponse current (index - source.history.length - 1)
      else source.response current

def report (current : RawCurrent Party Good Technology Instrument) :
    ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument := .original current (source.body current)

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := source.code.law
  initial := source.code.initial
  instructions := []
  emission? := some source.body
  localAttempts := fun _ => source.code.actions
  observedEmission? := some { generate := source.report, word := ProgrammeSource.ProgrammeReport.word }

def currentAt (ordinal : Nat) := ProgrammeSource.rawCurrent source.input
  (ProgrammeHistory.visitAt source.input ordinal).current

def actualExecution (depth : Nat) := (ProgrammeLiving.projectionLaw source.input).project .execution
  (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input (depth + 1)).current) ()

theorem actual_word (depth : Nat) : (source.actualExecution depth).submitted =
    source.body (source.currentAt (depth + 1)) := by
  change ProgrammeSource.rawEvent source.input
    (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current) =
    source.body (ProgrammeSource.rawCurrent source.input
      (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current))
  cases (ProgrammeHistory.visitAt source.input depth).current <;> rfl

theorem current_round (ordinal : Nat) :
    (source.currentAt ordinal).round = source.code.initial.round + ordinal :=
  ProgrammeHistory.visit_round source.input ordinal

theorem next_is_actual (depth : Nat) : source.currentAt (depth + 2) =
    source.code.law.next (source.currentAt (depth + 1)) (source.actualExecution depth).submitted :=
  (source.actualExecution depth).root_next_exact.symm

theorem history_word_is_actual (index : Nat) (inside : index < source.history.length) :
    (source.actualExecution index).submitted = source.history[index] := by
  rw [source.actual_word]
  unfold body
  rw [source.current_round]
  have address : source.code.initial.round + (index + 1) - source.code.initial.round - 1 = index := by omega
  rw [address, List.getElem?_eq_getElem inside]

theorem history_prefix_is_actual (count : Nat) (bounded : count ≤ source.history.length) :
    source.currentAt (count + 1) =
      (source.history.take count).foldl source.code.law.next (source.code.law.next source.code.initial []) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have inside : count < source.history.length := by omega
    rw [show count + 1 + 1 = count + 2 by omega, source.next_is_actual,
      source.history_word_is_actual count inside, ih (by omega),
      List.take_succ_eq_append_getElem inside, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem original_history_current_is_actual : source.currentAt (source.history.length + 1) =
    source.code.historyCurrent source.history := by
  simpa only [List.take_length, Code.historyCurrent] using
    source.history_prefix_is_actual source.history.length (Nat.le_refl _)

theorem response_is_actual : (source.actualExecution source.history.length).submitted =
    source.response (source.code.historyCurrent source.history) := by
  rw [source.actual_word]
  unfold body
  rw [source.current_round]
  have address : source.code.initial.round + (source.history.length + 1) - source.code.initial.round - 1 =
      source.history.length := by omega
  rw [address, List.getElem?_eq_none (Nat.le_refl _), if_neg (Nat.lt_irrefl _),
    source.original_history_current_is_actual]

theorem actual_reaction_word_and_next (policy : source.code.Policy)
    (chosen : source.policy? = some policy) :
    (source.actualExecution source.history.length).submitted =
        (execution source.code policy source.history source.opponent).word ∧
      (source.actualExecution source.history.length).before = source.code.historyCurrent source.history ∧
      (source.actualExecution source.history.length).after = source.code.law.next
        (source.code.historyCurrent source.history) (execution source.code policy source.history source.opponent).word ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history) (execution source.code policy source.history source.opponent).word := by
  have word : (source.actualExecution source.history.length).submitted =
      (execution source.code policy source.history source.opponent).word := by
    rw [source.response_is_actual]
    simp only [response, chosen]
    rfl
  have before : (source.actualExecution source.history.length).before = source.code.historyCurrent source.history :=
    source.original_history_current_is_actual
  exact ⟨word, before, (source.actualExecution source.history.length).after_exact.trans
    (by rw [before, word]; rfl), by rw [source.next_is_actual, source.original_history_current_is_actual, word]⟩

theorem actual_reaction_pays_the_original_task (policy : source.code.Policy)
    (chosen : source.policy? = some policy) (feasible : source.code.feasible policy)
    (eligible : source.code.eligible (trace source.code policy source.history source.opponent) = true) :
    ServiceAdequate source.code.law (source.actualExecution source.history.length).before source.code.task
      (source.actualExecution source.history.length).submitted := by
  have actual := source.actual_reaction_word_and_next policy chosen
  rw [actual.2.1, actual.1]
  exact (feasible _ (actual_reactive_script_is_enumerated source.code policy source.history source.original
    source.opponent eligible)).2


def withContinuation (words : List (RawEvent Party Good Port Technology Instrument)) :
    Machine Party Good Port Technology Instrument := {source with continuation := words, feedback? := none}

theorem continuation_word_is_actual (index : Nat) (inside : index < source.continuation.length) :
    (source.actualExecution (source.history.length + 1 + index)).submitted = source.continuation[index] := by
  rw [source.actual_word]
  unfold body
  rw [source.current_round]
  have address : source.code.initial.round + (source.history.length + 1 + index + 1) -
      source.code.initial.round - 1 = source.history.length + 1 + index := by omega
  rw [address, List.getElem?_eq_none (by omega), if_pos (by omega)]
  have coordinate : source.history.length + 1 + index - source.history.length - 1 = index := by omega
  rw [coordinate, List.getElem?_eq_getElem inside]

theorem continuation_prefix_is_actual (count : Nat) (bounded : count ≤ source.continuation.length) :
    source.currentAt (source.history.length + 2 + count) =
      (source.continuation.take count).foldl source.code.law.next (source.currentAt (source.history.length + 2)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have inside : count < source.continuation.length := by omega
      rw [show source.history.length + 2 + (count + 1) = (source.history.length + 1 + count) + 2 by omega,
        source.next_is_actual, source.continuation_word_is_actual count inside]
      rw [show source.history.length + 1 + count + 1 = source.history.length + 2 + count by omega,
        ih (by omega), List.take_succ_eq_append_getElem inside, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem no_continuation_keeps_the_original_response (current : RawCurrent Party Good Technology Instrument)
    (empty : source.continuation = []) (legacy : source.feedback? = none) : source.body current =
      match source.history[current.round - source.code.initial.round - 1]? with
      | some word => word | none => source.response current := by
  unfold body
  split
  next => rfl
  next => simp only [empty, List.getElem?_nil]; split <;> simp only [laterResponse, legacy]

def withSide (side : Side) : Machine Party Good Port Technology Instrument := { source with side := side }

theorem both_arms_use_the_same_original_history_and_opponent :
    (source.withSide .original).history = (source.withSide .replacement).history ∧
      (source.withSide .original).opponent = (source.withSide .replacement).opponent := ⟨rfl, rfl⟩

end Machine
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction

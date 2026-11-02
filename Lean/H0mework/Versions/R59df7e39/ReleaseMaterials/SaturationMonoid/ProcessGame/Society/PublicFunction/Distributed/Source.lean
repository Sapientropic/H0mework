import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

/-! A selected distributed program executes on its own original source.
The primitive history is submitted before the asynchronous event script.
Synthesis is independent of which history is actual; only sent local reads
can influence later activations. A finite refusal emits no fictitious work. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure Source (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  code : Code Party Good Port Technology Instrument
  reference : code.Policy
  history : List (RawEvent Party Good Port Technology Instrument)
  events : List (Event Party Good Port Technology Instrument code.sites)
  admitted : (history, events) ∈ code.scenarios

namespace Source

variable (source : Source Party Good Port Technology Instrument)

def answer := source.code.compile source.reference

def response (current : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  match source.answer with
  | .selected choice => (source.code.replay choice.policy.policy current source.events).word
  | .blocked _ => []

def body (current : RawCurrent Party Good Technology Instrument) : RawEvent Party Good Port Technology Instrument :=
  match source.history[current.round - source.code.initial.round - 1]? with
  | some word => word
  | none => source.response current

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
  rw [address, List.getElem?_eq_none (Nat.le_refl _), source.original_history_current_is_actual]

theorem selected_plan_is_paid_on_its_own_root (choice : source.code.Selection source.reference)
    (generated : source.answer = .selected choice) :
    (source.actualExecution source.history.length).submitted =
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      ServiceAdequate source.code.law (source.actualExecution source.history.length).before source.code.task
        (source.actualExecution source.history.length).submitted ∧
      source.currentAt (source.history.length + 2) = source.code.law.next
        (source.code.historyCurrent source.history)
        (source.code.executed choice.policy.policy (source.history, source.events)).word ∧
      source.code.verify source.reference choice.policy.policy = true := by
  have word : (source.actualExecution source.history.length).submitted =
      (source.code.executed choice.policy.policy (source.history, source.events)).word := by
    rw [source.response_is_actual]
    unfold response
    rw [generated]
    rfl
  refine ⟨word, ?_, ?_, source.code.selection_passes_independent_replay source.reference choice⟩
  · change ServiceAdequate source.code.law (source.currentAt (source.history.length + 1)) _ _
    rw [source.original_history_current_is_actual, word]
    exact (choice.policy.feasible _ source.admitted).2
  · rw [source.next_is_actual, source.original_history_current_is_actual, word]

/-- Extending the primitive input creates another actual history, rather
than deleting the old one or granting this planner an approval gate. -/
def withHistory (history : List (RawEvent Party Good Port Technology Instrument))
    (admitted : (history, source.events) ∈ source.code.scenarios) :
    Source Party Good Port Technology Instrument := { source with history := history, admitted := admitted }

theorem planner_does_not_select_using_the_hidden_actual_history
    (history : List (RawEvent Party Good Port Technology Instrument))
    (admitted : (history, source.events) ∈ source.code.scenarios) :
    (source.withHistory history admitted).answer = source.answer := rfl

end Source
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed

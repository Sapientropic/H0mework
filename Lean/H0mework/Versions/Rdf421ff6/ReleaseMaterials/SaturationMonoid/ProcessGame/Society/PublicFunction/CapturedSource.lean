import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Source

/-!
# An actual captured visit followed by source-generated service planning

The old request is executed in the first running visit, including rejection.
Planning begins from its actual successor, not a replay of the initial stock.
Both histories belong to this one registered source and retain its old rows.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure CapturedSource (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  code : SourceCode Party Good Port Technology Instrument
  original : RawEvent Party Good Port Technology Instrument
  refused : ∃ item ∈ code.law.rawItems (code.law.next code.initial []) original,
    ¬ code.law.Valid item.before item.request

namespace CapturedSource

variable (source : CapturedSource Party Good Port Technology Instrument)

inductive Report where
  | original (current : RawCurrent Party Good Technology Instrument)
  | planning (report : source.code.Report)

def reportAt (current : RawCurrent Party Good Technology Instrument) : source.Report :=
  if current.round = source.code.initial.round + 1 then .original current
  else .planning ⟨current, source.code.compileAt current⟩

def reportWord : source.Report → RawEvent Party Good Port Technology Instrument
  | .original _ => source.original
  | .planning report => report.2.word

def encodeReport : source.Report → ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument
  | .original current => .original current source.original
  | .planning ⟨current, outcome⟩ => .planning source.code.law current
      (source.code.taskAt current) (source.code.actionsAt current) source.code.budget outcome

theorem encoded_word (report : source.Report) :
    (source.encodeReport report).word = source.reportWord report := by
  cases report <;> rfl

def observedEmission : ProgrammeSource.ObservedEmission
    (RawCurrent Party Good Technology Instrument) (RawEvent Party Good Port Technology Instrument)
    (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument) where
  generate := fun current => source.encodeReport (source.reportAt current)
  word := ProgrammeSource.ProgrammeReport.word

def body (current : RawCurrent Party Good Technology Instrument) :=
  source.reportWord (source.reportAt current)

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := source.code.law
  initial := source.code.initial
  instructions := source.original
  emission? := some source.body
  localAttempts := source.code.actionsAt
  observedEmission? := some source.observedEmission

def currentAt (depth : Nat) :=
  ProgrammeSource.rawCurrent source.input
    (ProgrammeHistory.visitAt source.input depth).current

def actualExecution (depth : Nat) :=
  (ProgrammeLiving.projectionLaw source.input).project .execution
    (ProgrammeSource.emitted source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current) ()

theorem source_word_exact (depth : Nat) :
    (source.actualExecution depth).submitted = source.body (source.currentAt (depth + 1)) := by
  change ProgrammeSource.rawEvent source.input
    (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current) =
      source.body (ProgrammeSource.rawCurrent source.input
        (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current))
  cases (ProgrammeHistory.visitAt source.input depth).current <;>
    exact source.encoded_word _

theorem current_round (depth : Nat) :
    (source.currentAt depth).round = source.code.initial.round + depth :=
  ProgrammeHistory.visit_round source.input depth

theorem original_is_actually_executed :
    (source.actualExecution 0).submitted = source.original := by
  rw [source.source_word_exact]
  unfold body reportAt
  rw [source.current_round, if_pos rfl]
  rfl

theorem original_has_actual_rejection :
    ∃ item ∈ (source.actualExecution 0).interpreted.items,
      ¬ source.code.law.Valid item.before item.request := by
  change ∃ item ∈ (source.code.law.execute (source.currentAt 1) 0
    (source.actualExecution 0).submitted).items, _
  rw [source.original_is_actually_executed]
  exact source.refused

theorem planning_is_actually_executed (depth : Nat) :
    (source.actualExecution (depth + 1)).submitted =
      source.code.body (source.currentAt (depth + 2)) := by
  rw [source.source_word_exact]
  unfold body reportAt
  rw [source.current_round, if_neg (by omega)]
  rfl

theorem original_successor_is_planning_input :
    source.currentAt 2 =
      source.code.law.next (source.currentAt 1) source.original := by
  exact (source.actualExecution 0).root_next_exact.symm.trans
    (congrArg (source.code.law.next (source.currentAt 1))
      source.original_is_actually_executed)

theorem paid_plan_reaches_same_root_next (depth : Nat)
    (plan : PaidServicePlan source.code.law (source.currentAt (depth + 2))
      (source.code.taskAt (source.currentAt (depth + 2)))
      (source.code.actionsAt (source.currentAt (depth + 2))) source.code.budget)
    (generated : source.code.compileAt (source.currentAt (depth + 2)) = .paid plan) :
    (source.actualExecution (depth + 1)).submitted = plan.word ∧
    (source.actualExecution (depth + 1)).after = plan.next ∧
    source.currentAt (depth + 3) = plan.next := by
  have word : (source.actualExecution (depth + 1)).submitted = plan.word := by
    rw [source.planning_is_actually_executed]
    unfold SourceCode.body
    rw [generated]
    rfl
  have after : (source.actualExecution (depth + 1)).after = plan.next := by
    exact (source.actualExecution (depth + 1)).after_exact.trans
      (congrArg (source.code.law.next (source.currentAt (depth + 2))) word)
  exact ⟨word, after,
    (source.actualExecution (depth + 1)).root_next_exact.symm.trans after⟩

end CapturedSource

end SaturationMonoid.ProcessGame.Society.PublicFunction

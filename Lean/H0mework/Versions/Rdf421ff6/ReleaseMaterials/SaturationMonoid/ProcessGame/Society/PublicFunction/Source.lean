import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory

/-!
# Source-owned public-service execution

The planner is registered as local emission code before the source emits.
Every running visit recompiles from its actual current. Obstructed visits
retain the typed blocker and every original root row; their empty material
word is not a service completion or a responsibility settlement.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure SourceCode (Party Good Port Technology Instrument : Type) where
  law : RawLaw Party Good Port Technology Instrument
  initial : RawCurrent Party Good Technology Instrument
  taskAt : RawCurrent Party Good Technology Instrument → PublicTaskSpec Party Good
  actionsAt : RawCurrent Party Good Technology Instrument →
    List (Request Party Good Port Technology Instrument)
  budget : Nat

namespace SourceCode

variable (code : SourceCode Party Good Port Technology Instrument)

def compileAt (current : RawCurrent Party Good Technology Instrument) :=
  compile code.law current (code.taskAt current) (code.actionsAt current) code.budget

def body (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument :=
  (code.compileAt current).word

abbrev Report := Σ current : RawCurrent Party Good Technology Instrument,
  PlanningOutcome code.law current (code.taskAt current) (code.actionsAt current) code.budget

def observedEmission : ProgrammeSource.ObservedEmission
    (RawCurrent Party Good Technology Instrument) (RawEvent Party Good Port Technology Instrument)
    (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument) where
  generate := fun current => .planning code.law current (code.taskAt current)
    (code.actionsAt current) code.budget (code.compileAt current)
  word := ProgrammeSource.ProgrammeReport.word

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := code.law
  initial := code.initial
  instructions := []
  emission? := some code.body
  localAttempts := code.actionsAt
  observedEmission? := some code.observedEmission

def currentAt (depth : Nat) :=
  ProgrammeSource.rawCurrent code.input (ProgrammeHistory.visitAt code.input depth).current

def outcomeAt (depth : Nat) := code.compileAt (code.currentAt depth)

theorem source_word_exact (depth : Nat) :
    ProgrammeSource.rawEvent code.input
      (ProgrammeHistory.visitAt code.input (depth + 1)).current =
      code.body (code.currentAt (depth + 1)) := by
  change ProgrammeSource.rawEvent code.input
    (ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input depth).current) =
      code.body (ProgrammeSource.rawCurrent code.input
        (ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input depth).current))
  cases (ProgrammeHistory.visitAt code.input depth).current <;> rfl

theorem source_next_exact (depth : Nat) :
    code.currentAt (depth + 2) =
      code.law.next (code.currentAt (depth + 1)) (code.body (code.currentAt (depth + 1))) := by
  change ProgrammeSource.rawCurrent code.input
    (ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input (depth + 1)).current) = _
  rw [ProgrammeSource.actual_raw_next, code.source_word_exact]
  rfl

def actualExecution (depth : Nat) :=
  (ProgrammeLiving.projectionLaw code.input).project .execution
    (ProgrammeSource.emitted code.input
      (ProgrammeHistory.visitAt code.input (depth + 1)).current) ()

theorem actual_execution_word (depth : Nat) :
    (code.actualExecution depth).submitted = code.body (code.currentAt (depth + 1)) :=
  code.source_word_exact depth

theorem paid_plan_is_actual (depth : Nat)
    (plan : PaidServicePlan code.law (code.currentAt (depth + 1))
      (code.taskAt (code.currentAt (depth + 1)))
      (code.actionsAt (code.currentAt (depth + 1))) code.budget)
    (generated : code.outcomeAt (depth + 1) = .paid plan) :
    (code.actualExecution depth).submitted = plan.word ∧
    (code.actualExecution depth).after = plan.next ∧
    code.currentAt (depth + 2) = plan.next := by
  have word : code.body (code.currentAt (depth + 1)) = plan.word := by
    unfold body
    change code.compileAt (code.currentAt (depth + 1)) = .paid plan at generated
    rw [generated]
    rfl
  refine ⟨(code.actual_execution_word depth).trans word, ?_, ?_⟩
  · change code.law.next _ _ = _
    rw [code.source_word_exact, word]
    rfl
  · rw [code.source_next_exact, word]
    rfl

theorem actual_execution_consumes_service (depth : Nat)
    (plan : PaidServicePlan code.law (code.currentAt (depth + 1))
      (code.taskAt (code.currentAt (depth + 1)))
      (code.actionsAt (code.currentAt (depth + 1))) code.budget)
    (generated : code.outcomeAt (depth + 1) = .paid plan) :
    ServiceAdequate code.law (code.actualExecution depth).before
      (code.taskAt (code.currentAt (depth + 1))) (code.actualExecution depth).submitted ∧
    (∀ item ∈ (code.actualExecution depth).interpreted.items,
      code.law.Valid item.before item.request) := by
  have word := (code.paid_plan_is_actual depth plan generated).1
  change ServiceAdequate code.law (code.currentAt (depth + 1)) _ _ ∧ _
  constructor
  · rw [word]; exact plan.sound.1
  · change ∀ item ∈ (code.law.execute (code.currentAt (depth + 1)) 0
      (code.actualExecution depth).submitted).items, _
    rw [word]
    exact plan.sound.2

/-- The existing facade supplies the same occurrence, whole ledger and next;
the planner adds a dependent calculation, not another authority root. -/
theorem execution_factorizes (depth : Nat) :
    HEq ((ProgrammeHistory.facade code.input).readoutAt
      (ProgrammeHistory.activated code.input (depth + 1)) .execution)
      ((ProgrammeHistory.activated code.input (depth + 1)).tick.generated.projectionOutcome
        .execution) ∧
    HEq (ProgrammeHistory.activated code.input (depth + 1)).tick.generated.wholeLedgerWriteBack
      ((ProgrammeHistory.activated code.input (depth + 1)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (ProgrammeHistory.activated code.input (depth + 1)).current.visit.current) ∧
    (ProgrammeHistory.activated code.input (depth + 1)).tick.nextCurrent =
      (ProgrammeHistory.process code.input).stateAt
        ((ProgrammeHistory.process code.input).successor
          (ProgrammeHistory.activated code.input (depth + 1)).state) := by
  have factor := ProgrammeHistory.execution_face_shares_whole_ledger_and_next
    code.input (depth + 1)
  exact ⟨factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

/-- Every finite continuation executes the same source code afresh; there is
no table of future successful plans. This does not assert fair escape from
a persistent physical or control obstruction. -/
theorem finite_continuation (depth : Nat) :
    (∃ plan, code.outcomeAt (depth + 1) = .paid plan ∧
      code.currentAt (depth + 2) = plan.next) ∨
    (∃ obstruction, code.outcomeAt (depth + 1) = .physical obstruction) ∨
    (∃ blockage, code.outcomeAt (depth + 1) = .capture blockage) := by
  cases generated : code.outcomeAt (depth + 1) with
  | paid plan => exact Or.inl ⟨plan, rfl,
      (code.paid_plan_is_actual depth plan generated).2.2⟩
  | physical obstruction => exact Or.inr (Or.inl ⟨obstruction, rfl⟩)
  | capture blockage => exact Or.inr (Or.inr ⟨blockage, rfl⟩)

end SourceCode

end SaturationMonoid.ProcessGame.Society.PublicFunction

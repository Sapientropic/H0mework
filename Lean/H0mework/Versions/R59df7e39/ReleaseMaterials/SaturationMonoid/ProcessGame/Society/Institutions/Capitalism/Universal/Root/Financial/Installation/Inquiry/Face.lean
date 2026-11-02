import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Inquiry.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

def materialAt (current : Current input start) : RawCurrent Party Good Technology Instrument :=
  ProgrammeSource.rawCurrent input (Cursor.physicalVisit input current.cursor).current

def newlyExecuted (current : Current input start) : Option (ExecutionResult Party Good Port Technology Instrument) :=
  if Cursor.FreshBody input current.cursor then
    some (input.law.execute (materialAt input start current) 0
      (ProgrammeSource.rawEvent input (Cursor.physicalVisit input current.cursor).current))
  else none

structure AccountFaceAt {current : Current input start}
    (_occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) where
  before : (process input).GeneratedState
  after : (process input).GeneratedState
  native : (process input).Run before.current after.current
  before_exact : before = current.cursor.account
  after_exact : after = (next input start current).cursor.account
  pending : Cursor.PendingInventory input current.cursor
  pendingAfter : Cursor.PendingInventory input (next input start current).cursor
  physicalBefore : RawCurrent Party Good Technology Instrument
  physicalAfter : RawCurrent Party Good Technology Instrument
  physicalBefore_exact : physicalBefore = materialAt input start current
  physicalAfter_exact : physicalAfter = materialAt input start (next input start current)
  newlyExecuted : Option (ExecutionResult Party Good Port Technology Instrument)
  newlyExecuted_exact : newlyExecuted = AccountSource.newlyExecuted input start current

def accountFace {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    AccountFaceAt input start startPositive occurrence where
  before := current.cursor.account
  after := (next input start current).cursor.account
  native := Cursor.native input current.cursor
  before_exact := rfl
  after_exact := rfl
  pending := Cursor.pendingInventory input current.cursor
  pendingAfter := Cursor.pendingInventory input (next input start current).cursor
  physicalBefore := materialAt input start current
  physicalAfter := materialAt input start (next input start current)
  physicalBefore_exact := rfl
  physicalAfter_exact := rfl
  newlyExecuted := newlyExecuted input start current
  newlyExecuted_exact := rfl

def IsIssue (current : Current input start) : Prop :=
  match Cursor.action input current.cursor with
  | .issue _ => True
  | _ => False

instance (current : Current input start) : Decidable (IsIssue input start current) := by
  unfold IsIssue
  cases Cursor.action input current.cursor <;> infer_instance

theorem actual_bookkeeping_has_no_second_economic_effect (current : Current input start)
    (old : ¬ Cursor.FreshBody input current.cursor) :
    materialAt input start (next input start current) = materialAt input start current ∧
      newlyExecuted input start current = none := by
  constructor
  · exact congrArg (fun visit => ProgrammeSource.rawCurrent input visit.current)
      (Cursor.physical_next_of_bookkeeping input current.cursor old)
  · simp only [newlyExecuted, if_neg old]

theorem actual_fresh_body_is_the_original_raw_next (current : Current input start)
    (fresh : Cursor.FreshBody input current.cursor) :
    materialAt input start (next input start current) =
      input.law.next (materialAt input start current)
        (ProgrammeSource.rawEvent input (Cursor.physicalVisit input current.cursor).current) := by
  have original := ProgrammeSource.actual_raw_next input (Cursor.physicalVisit input current.cursor).current
  exact (congrArg (ProgrammeSource.rawCurrent input)
    (Cursor.physical_next_of_fresh input current.cursor fresh)).trans original

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

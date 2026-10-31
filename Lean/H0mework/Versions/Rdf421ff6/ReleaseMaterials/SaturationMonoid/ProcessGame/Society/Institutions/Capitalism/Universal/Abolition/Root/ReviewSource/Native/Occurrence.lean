import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Physical

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

def runningCurrent (depth : Nat) : (ProgrammeSource.V code.input).Current :=
  .running (code.currentAt (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt code.input (depth + 1)).current)

theorem runningCurrent_is_the_same_source_visit (depth : Nat) :
    runningCurrent code depth = (ProgrammeHistory.visitAt code.input (depth + 1)).current := by
  unfold runningCurrent SourceCode.currentAt
  change ProgrammeSource.Current.running
    (ProgrammeSource.rawCurrent code.input (ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input depth).current))
    (ProgrammeSource.pastAt (ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input depth).current)) =
      ProgrammeSource.next code.input (ProgrammeHistory.visitAt code.input depth).current
  cases (ProgrammeHistory.visitAt code.input depth).current <;> rfl

def taskEntry (depth : Nat) := ProgrammeSource.sourceEntry code.input (runningCurrent code depth)
  (.instruction (sourceSeat code))
def taskWrite (depth : Nat) := (ProgrammeLedger.evolution code.input (runningCurrent code depth)).destination (taskEntry code depth)
def writtenReceipt (depth : Nat) := ProgrammeLedger.writtenTransferReceipt code.input (code.currentAt (depth + 1))
  (ProgrammeSource.pastAt (ProgrammeHistory.visitAt code.input (depth + 1)).current) (taskEntry code depth)

theorem receipt_is_in_the_original_whole_ledger_write (depth : Nat) :
    ProgrammeLedger.transferReceiptOf code.input (taskWrite code depth).2 = some (writtenReceipt code depth) :=
  (ProgrammeLedger.destination_transfer_receipt code.input _ _ _).trans
    (congrArg some (ProgrammeLedger.writtenTransferReceipt_exact code.input _ _ _).symm)

/-- The fixed birth task determines the window at every later occurrence,
even if the source separately declares another task in a later report. -/
def SlotPaid (depth : Nat) (index : Slot code) : Prop :=
  (originalTask code).earliest ≤ (code.actualExecution depth).before.clock ∧
  (code.actualExecution depth).after.clock ≤ (originalTask code).deadline ∧
  Exit.Necessity.BundlePaid code.law (code.actualExecution depth).before
    (code.actualExecution depth).submitted (serviceSlot code index).bearer
    (serviceSlot code index).goods (serviceSlot code index).purpose

instance (depth : Nat) (index : Slot code) : Decidable (SlotPaid code depth index) := by
  unfold SlotPaid
  infer_instance

structure Event where
  index : Slot code
  ordinal : Nat
  inputOverride : Option (SourceInput (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) := none

def Event.Paid (event : Event code) : Prop :=
  match event.inputOverride with
  | none => 0 < event.ordinal ∧ SlotPaid code (event.ordinal - 1) event.index
  | some actual => actual.Paid (code := code) event.index

instance (event : Event code) : Decidable (event.Paid code) := by
  unfold Event.Paid
  split <;> infer_instance

structure CanonicalReceipt (event : Event code) : Type where
  running : 0 < event.ordinal
  task_write : ProgrammeLedger.transferReceiptOf code.input (taskWrite code (event.ordinal - 1)).2 =
    some (writtenReceipt code (event.ordinal - 1))
  current : runningCurrent code (event.ordinal - 1) =
    (ProgrammeHistory.visitAt code.input event.ordinal).current

inductive VisitReceipt (event : Event code) : Type
  | canonical (original : event.inputOverride = none) (receipt : CanonicalReceipt code event)
  | actual (input : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
      (original : event.inputOverride = some input) (receipt : input.Receipt (code := code))

def visitReceipt (index : Slot code) (depth : Nat) : VisitReceipt code ⟨index, depth + 1, none⟩ :=
  .canonical rfl ⟨Nat.zero_lt_succ depth, receipt_is_in_the_original_whole_ledger_write code depth,
    runningCurrent_is_the_same_source_visit code depth⟩

def inputReceipt (index : Slot code) (depth : Nat)
    (input : Option (SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))) : VisitReceipt code ⟨index, depth + 1, input⟩ :=
  match input with
  | none => visitReceipt code index depth
  | some actual => .actual actual rfl actual.receipt

#print axioms receipt_is_in_the_original_whole_ledger_write
#print axioms visitReceipt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

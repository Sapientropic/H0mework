import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.FixedTask
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.SourceRequest

/-!
# Source-owned outstanding service computation

The original positive service requirements are fixed before emission. A
finite source fold retains the first actual payment of each requirement and
compiles only outstanding requirements. The fold is programme code, not a
second root, a chosen future history, or an external settlement table.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Every listed slot is a positive service requirement. Empty maintenance
requirements are omitted rather than turned into fictitious obligations. -/
structure OutstandingSource (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  seed : FixedTaskSource Party Good Port Technology Instrument
  positive : ∀ slot ∈ seed.task.slots, ∃ item ∈ slot.goods, 0 < item.2
  /-- Other live responsibilities may continue after service payment. The
  same payload supplies the actual word and the original task-row report. -/
  completionReport : RawCurrent Party Good Technology Instrument →
    ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument :=
      fun current => .original current []
  /-- Admitted source requests enter the same payment fold. Service
  completion cannot close admission for other continuing responsibilities. -/
  incoming? : (current : RawCurrent Party Good Technology Instrument) →
    Option (IncomingWord seed.law current) := fun _ => none

namespace OutstandingSource

variable (source : OutstandingSource Party Good Port Technology Instrument)

abbrev Slot := source.seed.Slot
abbrev Payments := source.Slot → Option Nat

def pendingIndices (payments : source.Payments) : List source.Slot :=
  (List.finRange source.seed.task.slots.length).filter (fun index => (payments index).isNone)

def pendingSlots (payments : source.Payments) : List (ServiceSlot Party Good) :=
  (source.pendingIndices payments).map source.seed.slot

theorem pending_mem_original (payments : source.Payments) (slot : ServiceSlot Party Good)
    (inside : slot ∈ source.pendingSlots payments) : slot ∈ source.seed.task.slots := by
  obtain ⟨index, _pending, same⟩ := List.mem_map.mp inside
  rw [← same]
  exact List.mem_iff_getElem.mpr ⟨index.val, index.isLt, rfl⟩

def pendingTask (payments : source.Payments) (nonempty : source.pendingSlots payments ≠ []) :
    PublicTaskSpec Party Good where
  slots := source.pendingSlots payments
  earliest := source.seed.task.earliest
  deadline := source.seed.task.deadline
  demand := by
    cases slots : source.pendingSlots payments with
    | nil => exact False.elim (nonempty slots)
    | cons slot rest =>
      have inside : slot ∈ source.pendingSlots payments := by rw [slots]; exact List.mem_cons_self
      exact ⟨slot, List.mem_cons_self,
        source.positive slot (source.pending_mem_original payments slot inside)⟩

inductive Decision (current : RawCurrent Party Good Technology Instrument)
    (payments : source.Payments) where
  | complete (empty : source.pendingSlots payments = [])
  | received (incoming : IncomingWord source.seed.law current)
  | planning (nonempty : source.pendingSlots payments ≠ [])
      (outcome : PlanningOutcome source.seed.law current (source.pendingTask payments nonempty)
        (source.seed.actionsAt current) source.seed.budget)

def decideAt (current : RawCurrent Party Good Technology Instrument) (payments : source.Payments) :
    source.Decision current payments :=
  match source.incoming? current with
  | some incoming => .received incoming
  | none =>
      if empty : source.pendingSlots payments = [] then .complete empty
      else .planning empty (compile source.seed.law current (source.pendingTask payments empty)
        (source.seed.actionsAt current) source.seed.budget)

def Decision.word {current : RawCurrent Party Good Technology Instrument}
    {payments : source.Payments} : source.Decision current payments →
      RawEvent Party Good Port Technology Instrument
  | .complete _ => (source.completionReport current).word
  | .received incoming => incoming.word
  | .planning _ outcome => outcome.word

def Decision.report {current : RawCurrent Party Good Technology Instrument}
    {payments : source.Payments} : source.Decision current payments →
      ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument
  | .complete _ => source.completionReport current
  | .received incoming => .original current incoming.word
  | .planning nonempty outcome => .planning source.seed.law current
      (source.pendingTask payments nonempty) (source.seed.actionsAt current) source.seed.budget outcome

theorem Decision.report_word {current : RawCurrent Party Good Technology Instrument}
    {payments : source.Payments} (decision : source.Decision current payments) :
    decision.report.word = decision.word := by
  cases decision <;> rfl

def SlotPaid (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot) : Prop :=
  source.seed.task.earliest ≤ current.clock ∧
  (source.seed.law.next current word).clock ≤ source.seed.task.deadline ∧
  Necessity.BundlePaid source.seed.law current word
    (source.seed.slot index).bearer (source.seed.slot index).goods (source.seed.slot index).purpose

instance (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : source.Slot) :
    Decidable (source.SlotPaid current word index) := by
  unfold SlotPaid
  infer_instance

def update (payments : source.Payments) (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (ordinal : Nat) : source.Payments :=
  fun index => match payments index with
    | some paid => some paid
    | none => if source.SlotPaid current word index then some ordinal else none

structure Frame where
  raw : RawCurrent Party Good Technology Instrument
  payments : source.Payments

def frameWord (ordinal : Nat) (frame : source.Frame) : RawEvent Party Good Port Technology Instrument :=
  if ordinal = 0 then []
  else if ordinal = 1 then source.seed.original
  else (source.decideAt frame.raw frame.payments).word

def advance (ordinal : Nat) (frame : source.Frame) : source.Frame where
  raw := source.seed.law.next frame.raw (source.frameWord ordinal frame)
  payments := source.update frame.payments frame.raw (source.frameWord ordinal frame) ordinal

def frameAt : Nat → source.Frame
  | 0 => ⟨source.seed.initial, fun _ => none⟩
  | ordinal + 1 => source.advance ordinal (frameAt ordinal)

def ordinal (current : RawCurrent Party Good Technology Instrument) : Nat :=
  current.round - source.seed.initial.round

def reportAt (current : RawCurrent Party Good Technology Instrument) :
    ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument :=
  let ordinal := source.ordinal current
  if ordinal = 1 then .original current source.seed.original
  else (source.decideAt current (source.frameAt ordinal).payments).report

def input : ProgrammeSource.Input Party Good Port Technology Instrument where
  law := source.seed.law
  initial := source.seed.initial
  instructions := source.seed.original
  emission? := some (fun current => (source.reportAt current).word)
  localAttempts := source.seed.actionsAt
  observedEmission? := some {
    generate := source.reportAt
    word := ProgrammeSource.ProgrammeReport.word }

def currentAt (ordinal : Nat) :=
  ProgrammeSource.rawCurrent source.input (ProgrammeHistory.visitAt source.input ordinal).current

theorem current_round (ordinal : Nat) :
    (source.currentAt ordinal).round = source.seed.initial.round + ordinal :=
  ProgrammeHistory.visit_round source.input ordinal

theorem ordinal_exact (ordinal : Nat) : source.ordinal (source.currentAt ordinal) = ordinal := by
  unfold OutstandingSource.ordinal
  rw [source.current_round]
  omega

end OutstandingSource

end SaturationMonoid.ProcessGame.Society.PublicFunction

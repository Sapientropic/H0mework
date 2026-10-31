import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingExecution

/-! Actual payment provenance, residual feedback and the original task-row
write. A completed service requirement does not settle financial claims or
erase the continuing root responsibility. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

theorem no_payment_from_empty_word (current) (index : source.Slot) :
    ¬ source.SlotPaid current ([] : RawEvent Party Good Port Technology Instrument) index := by
  rintro ⟨_earliest, _deadline, waived | ⟨item, member, _valid, _matches⟩⟩
  · obtain ⟨requirement, inside, _positive⟩ := source.positive (source.seed.slot index)
      (List.mem_iff_getElem.mpr ⟨index.val, index.isLt, rfl⟩)
    rw [waived] at inside
    exact List.not_mem_nil inside
  · exact List.not_mem_nil member

theorem frame_payment_sound (ordinal : Nat) (index : source.Slot) (paid : Nat)
    (generated : (source.frameAt ordinal).payments index = some paid) :
    0 < paid ∧ paid < ordinal ∧ source.SlotPaid (source.currentAt paid)
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input paid).current) index := by
  induction ordinal with
  | zero => cases generated
  | succ ordinal ih =>
      change source.update (source.frameAt ordinal).payments (source.frameAt ordinal).raw
        (source.frameWord ordinal (source.frameAt ordinal)) ordinal index = some paid at generated
      unfold update at generated
      split at generated
      next original previous =>
        obtain ⟨positive, earlier, valid⟩ := ih (previous.trans generated)
        exact ⟨positive, Nat.lt_succ_of_lt earlier, valid⟩
      next =>
        split at generated
        next valid =>
          have same : paid = ordinal := (Option.some.inj generated).symm
          subst paid
          have positive : 0 < ordinal := by
            by_contra absent
            have zero : ordinal = 0 := by omega
            subst ordinal
            exact source.no_payment_from_empty_word _ index valid
          rw [← (source.canonical_frame ordinal).1, ← (source.canonical_frame ordinal).2] at valid
          exact ⟨positive, Nat.lt_succ_self _, valid⟩
        next => cases generated

theorem completion_has_original_receipts (ordinal : Nat)
    (complete : source.pendingSlots (source.frameAt ordinal).payments = []) (index : source.Slot) :
    ∃ paid, 0 < paid ∧ paid < ordinal ∧ source.SlotPaid (source.currentAt paid)
      (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input paid).current) index := by
  cases payment : (source.frameAt ordinal).payments index with
  | none =>
      have pending := source.pending_slot_has_original_identity _ index payment
      rw [complete] at pending
      exact False.elim (List.not_mem_nil pending)
  | some paid => exact ⟨paid, source.frame_payment_sound ordinal index paid payment⟩

theorem empty_execution_carries_unpaid (depth : Nat) (index : source.Slot)
    (unpaid : (source.frameAt (depth + 1)).payments index = none)
    (empty : (source.actualExecution depth).submitted = []) :
    (source.frameAt (depth + 2)).payments index = none := by
  apply (source.unpaid_carried_iff depth index unpaid).mpr
  rw [empty]
  exact source.no_payment_from_empty_word _ index

theorem actual_original_word : (source.actualExecution 0).submitted = source.seed.original := by
  rw [source.actual_execution_word]
  rfl

theorem actual_original_rejected :
    ∃ item ∈ (source.actualExecution 0).interpreted.items,
      ¬ source.seed.law.Valid item.before item.request := by
  change ∃ item ∈ (source.seed.law.execute (source.currentAt 1) 0
    (source.actualExecution 0).submitted).items, _
  rw [source.actual_original_word]
  exact source.seed.refused

theorem next_report_consumes_actual_residual (depth : Nat) :
    source.reportAt (source.currentAt (depth + 2)) =
      (source.decideAt (source.actualExecution depth).after
        (source.update (source.frameAt (depth + 1)).payments
          (source.actualExecution depth).before (source.actualExecution depth).submitted
            (depth + 1))).report := by
  unfold reportAt
  rw [source.ordinal_exact, if_neg (by omega : depth + 2 ≠ 1)]
  rw [← source.next_payments_are_actual_update, source.actual_execution_after,
    (source.canonical_frame (depth + 2)).1]

def runningCurrent (depth : Nat) : (ProgrammeSource.V source.input).Current :=
  .running (source.currentAt (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt source.input (depth + 1)).current)

theorem runningCurrent_is_original_visit (depth : Nat) :
    source.runningCurrent depth = (ProgrammeHistory.visitAt source.input (depth + 1)).current := by
  unfold runningCurrent currentAt
  change ProgrammeSource.Current.running
    (ProgrammeSource.rawCurrent source.input (ProgrammeSource.next source.input
      (ProgrammeHistory.visitAt source.input depth).current))
    (ProgrammeSource.pastAt (ProgrammeSource.next source.input
      (ProgrammeHistory.visitAt source.input depth).current)) =
      ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input depth).current
  cases (ProgrammeHistory.visitAt source.input depth).current <;> rfl

def taskEntry (depth : Nat) :=
  ProgrammeSource.sourceEntry source.input (source.runningCurrent depth)
    (.instruction ⟨0, by change 0 < 1; decide⟩)

def taskWrite (depth : Nat) :=
  (ProgrammeLedger.evolution source.input (source.runningCurrent depth)).destination
    (source.taskEntry depth)

def writtenReceipt (depth : Nat) :=
  ProgrammeLedger.writtenTransferReceipt source.input (source.currentAt (depth + 1))
    (ProgrammeSource.pastAt (ProgrammeHistory.visitAt source.input (depth + 1)).current)
    (source.taskEntry depth)

theorem receipt_is_in_original_task_write (depth : Nat) :
    ProgrammeLedger.transferReceiptOf source.input (source.taskWrite depth).2 =
      some (source.writtenReceipt depth) := by
  exact (ProgrammeLedger.destination_transfer_receipt source.input _ _ (source.taskEntry depth)).trans
    (congrArg some (ProgrammeLedger.writtenTransferReceipt_exact source.input _ _
      (source.taskEntry depth)).symm)

theorem written_report_exact (depth : Nat) :
    (source.writtenReceipt depth).val = source.reportAt (source.currentAt (depth + 1)) :=
  (source.writtenReceipt depth).property

theorem next_written_report_consumes_actual_residual (depth : Nat) :
    (source.writtenReceipt (depth + 1)).val =
      (source.decideAt (source.actualExecution depth).after
        (source.update (source.frameAt (depth + 1)).payments
          (source.actualExecution depth).before (source.actualExecution depth).submitted
            (depth + 1))).report :=
  (source.written_report_exact (depth + 1)).trans
    (source.next_report_consumes_actual_residual depth)

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

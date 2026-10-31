import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding

/-! The finite source computation is coupled to the original root at every
visit. Outstanding requirements choose its emitted word; only that word's
actual interpretation can clear a requirement. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

theorem canonical_frame (ordinal : Nat) :
    source.currentAt ordinal = (source.frameAt ordinal).raw ∧
    ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current =
      source.frameWord ordinal (source.frameAt ordinal) := by
  induction ordinal with
  | zero => exact ⟨rfl, rfl⟩
  | succ ordinal ih =>
      have raw : source.currentAt (ordinal + 1) = (source.frameAt (ordinal + 1)).raw := by
        change ProgrammeSource.rawCurrent source.input
          (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input ordinal).current) = _
        rw [ProgrammeSource.actual_raw_next]
        change source.seed.law.next (source.currentAt ordinal) _ = _
        rw [ih.1, ih.2]
        rfl
      refine ⟨raw, ?_⟩
      have emitted : ProgrammeSource.rawEvent source.input
          (ProgrammeHistory.visitAt source.input (ordinal + 1)).current =
          (source.reportAt (source.currentAt (ordinal + 1))).word := by
        change ProgrammeSource.rawEvent source.input
          (ProgrammeSource.next source.input (ProgrammeHistory.visitAt source.input ordinal).current) =
          (source.reportAt (ProgrammeSource.rawCurrent source.input
            (ProgrammeSource.next source.input
              (ProgrammeHistory.visitAt source.input ordinal).current))).word
        cases (ProgrammeHistory.visitAt source.input ordinal).current <;> rfl
      rw [emitted]
      unfold reportAt
      rw [source.ordinal_exact, raw]
      unfold frameWord
      rw [if_neg (by omega : ordinal + 1 ≠ 0)]
      by_cases first : ordinal + 1 = 1
      · rw [if_pos first, if_pos first]; rfl
      · rw [if_neg first, if_neg first]
        exact Decision.report_word _ _

def actualExecution (depth : Nat) :=
  (ProgrammeLiving.projectionLaw source.input).project .execution
    (ProgrammeSource.emitted source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current) ()

theorem actual_execution_word (depth : Nat) :
    (source.actualExecution depth).submitted =
      source.frameWord (depth + 1) (source.frameAt (depth + 1)) :=
  (source.canonical_frame (depth + 1)).2

theorem actual_execution_before (depth : Nat) :
    (source.actualExecution depth).before = (source.frameAt (depth + 1)).raw :=
  (source.canonical_frame (depth + 1)).1

theorem actual_execution_after (depth : Nat) :
    (source.actualExecution depth).after = (source.frameAt (depth + 2)).raw :=
  (source.actualExecution depth).root_next_exact.trans
    (source.canonical_frame (depth + 2)).1

theorem next_payments_are_actual_update (depth : Nat) :
    (source.frameAt (depth + 2)).payments =
      source.update (source.frameAt (depth + 1)).payments
        (source.actualExecution depth).before (source.actualExecution depth).submitted (depth + 1) := by
  rw [source.actual_execution_before, source.actual_execution_word]
  rfl

theorem next_word_consumes_actual_residual (depth : Nat) :
    (source.actualExecution (depth + 1)).submitted =
      (source.decideAt (source.actualExecution depth).after
        (source.update (source.frameAt (depth + 1)).payments
          (source.actualExecution depth).before (source.actualExecution depth).submitted
            (depth + 1))).word := by
  rw [source.actual_execution_word]
  unfold frameWord
  rw [if_neg (by omega : depth + 1 + 1 ≠ 0),
    if_neg (by omega : depth + 1 + 1 ≠ 1),
    source.actual_execution_after, ← source.next_payments_are_actual_update]

theorem unpaid_carried_iff (depth : Nat) (index : source.Slot)
    (unpaid : (source.frameAt (depth + 1)).payments index = none) :
    (source.frameAt (depth + 2)).payments index = none ↔
      ¬ source.SlotPaid (source.actualExecution depth).before
        (source.actualExecution depth).submitted index := by
  rw [source.next_payments_are_actual_update]
  simp only [update, unpaid, ite_eq_right_iff, reduceCtorEq, imp_false]

theorem payment_preserved (payments : source.Payments) (current) (word)
    (ordinal : Nat) (index : source.Slot) (paid : Nat)
    (settled : payments index = some paid) :
    source.update payments current word ordinal index = some paid := by
  simp only [update, settled]

theorem new_payment_has_actual_service (depth : Nat) (index : source.Slot) (paid : Nat)
    (unpaid : (source.frameAt (depth + 1)).payments index = none)
    (cleared : (source.frameAt (depth + 2)).payments index = some paid) :
    paid = depth + 1 ∧ source.SlotPaid (source.actualExecution depth).before
      (source.actualExecution depth).submitted index := by
  rw [source.next_payments_are_actual_update] at cleared
  simp only [update, unpaid] at cleared
  split at cleared
  next valid => exact ⟨(Option.some.inj cleared).symm, valid⟩
  next => cases cleared

theorem pending_index_iff (payments : source.Payments) (index : source.Slot) :
    index ∈ source.pendingIndices payments ↔ payments index = none := by
  simp only [pendingIndices, List.mem_filter, List.mem_finRange, true_and,
    Option.isNone_iff_eq_none]

theorem pending_slot_has_original_identity (payments : source.Payments) (index : source.Slot)
    (unpaid : payments index = none) :
    source.seed.slot index ∈ source.pendingSlots payments :=
  List.mem_map.mpr ⟨index, (source.pending_index_iff payments index).mpr unpaid, rfl⟩

theorem pending_window_is_original (payments : source.Payments)
    (nonempty : source.pendingSlots payments ≠ []) :
    (source.pendingTask payments nonempty).earliest = source.seed.task.earliest ∧
    (source.pendingTask payments nonempty).deadline = source.seed.task.deadline := ⟨rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingResponsibility

/-! Finite continuation closure of the actual outstanding-task source.
Every original slot is removed exactly after an actual in-window payment;
paid slots stay paid, and completion selects the source's own continuation.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

def ActualSlotPaid (ordinal : Nat) (index : source.Slot) : Prop :=
  source.SlotPaid (source.currentAt ordinal)
    (ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current) index

instance (ordinal : Nat) (index : source.Slot) : Decidable (source.ActualSlotPaid ordinal index) := by
  unfold ActualSlotPaid
  infer_instance

theorem prefix_payment_is_actual (ordinal : Nat) (index : source.Slot) :
    source.SlotPaid (source.frameAt ordinal).raw
        (source.frameWord ordinal (source.frameAt ordinal)) index ↔
      source.ActualSlotPaid ordinal index := by
  rw [← (source.canonical_frame ordinal).1, ← (source.canonical_frame ordinal).2]
  rfl

theorem recorded_payment_preserved (ordinal later : Nat) (index : source.Slot) (paid : Nat)
    (recorded : (source.frameAt ordinal).payments index = some paid) :
    (source.frameAt (ordinal + later)).payments index = some paid := by
  induction later with
  | zero => exact recorded
  | succ later ih =>
      change source.update (source.frameAt (ordinal + later)).payments
        (source.frameAt (ordinal + later)).raw
        (source.frameWord (ordinal + later) (source.frameAt (ordinal + later)))
        (ordinal + later) index = some paid
      simp only [update, ih]

theorem unpaid_iff_no_actual_payment (ordinal : Nat) (index : source.Slot) :
    (source.frameAt ordinal).payments index = none ↔
      ∀ earlier < ordinal, ¬ source.ActualSlotPaid earlier index := by
  induction ordinal with
  | zero => simp [frameAt]
  | succ ordinal ih =>
      constructor
      · intro unpaid earlier bound actual
        have previous : (source.frameAt ordinal).payments index = none := by
          cases prior : (source.frameAt ordinal).payments index with
          | none => rfl
          | some paid =>
              have stays := source.recorded_payment_preserved ordinal 1 index paid prior
              rw [unpaid] at stays
              cases stays
        have last : ¬ source.ActualSlotPaid ordinal index := by
          intro paid
          have native := (source.prefix_payment_is_actual ordinal index).mpr paid
          change source.update (source.frameAt ordinal).payments (source.frameAt ordinal).raw
            (source.frameWord ordinal (source.frameAt ordinal)) ordinal index = none at unpaid
          simp only [update, previous, if_pos native] at unpaid
          cases unpaid
        by_cases before : earlier < ordinal
        · exact ih.mp previous earlier before actual
        · have same : earlier = ordinal := by omega
          exact last (same ▸ actual)
      · intro never
        have previous := ih.mpr (fun earlier bound => never earlier (Nat.lt_succ_of_lt bound))
        have last := never ordinal (Nat.lt_succ_self _)
        have native : ¬ source.SlotPaid (source.frameAt ordinal).raw
            (source.frameWord ordinal (source.frameAt ordinal)) index :=
          fun paid => last ((source.prefix_payment_is_actual ordinal index).mp paid)
        change source.update (source.frameAt ordinal).payments (source.frameAt ordinal).raw
          (source.frameWord ordinal (source.frameAt ordinal)) ordinal index = none
        simp only [update, previous, if_neg native]

/-- The live update is indexed by original slot positions and consumes the
actual event of this visit, rather than a later replacement task. -/
theorem actual_outstanding_update (ordinal : Nat) (index : source.Slot) :
    index ∈ source.pendingIndices (source.frameAt (ordinal + 1)).payments ↔
      index ∈ source.pendingIndices (source.frameAt ordinal).payments ∧
        ¬ source.ActualSlotPaid ordinal index := by
  simp only [source.pending_index_iff, source.unpaid_iff_no_actual_payment]
  constructor
  · intro unpaid
    exact ⟨fun earlier before => unpaid earlier (Nat.lt_succ_of_lt before),
      unpaid ordinal (Nat.lt_succ_self _)⟩
  · rintro ⟨prior, last⟩ earlier before
    by_cases old : earlier < ordinal
    · exact prior earlier old
    · have same : earlier = ordinal := by omega
      exact same ▸ last

theorem unpaid_interval_is_retained (start length : Nat) (index : source.Slot)
    (unpaid : (source.frameAt start).payments index = none)
    (interval : ∀ offset < length, ¬ source.ActualSlotPaid (start + offset) index) :
    (source.frameAt (start + length)).payments index = none := by
  apply (source.unpaid_iff_no_actual_payment _ index).mpr
  intro earlier bound actual
  by_cases before : earlier < start
  · exact (source.unpaid_iff_no_actual_payment start index).mp unpaid earlier before actual
  · have offset : earlier - start < length := by omega
    have address : start + (earlier - start) = earlier := by omega
    apply interval (earlier - start) offset
    simpa only [address] using actual

/-- Without an admitted incoming word, an unpaid original slot forces the
next installed word and ledger report through the residual compiler. -/
theorem unpaid_forces_actual_replanning (depth : Nat) (index : source.Slot)
    (unpaid : (source.frameAt (depth + 2)).payments index = none)
    (quiet : source.incoming? (source.currentAt (depth + 2)) = none := by rfl) :
    ∃ nonempty : source.pendingSlots (source.frameAt (depth + 2)).payments ≠ [],
      (source.actualExecution (depth + 1)).submitted =
        (compile source.seed.law (source.currentAt (depth + 2))
          (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
          (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget).word ∧
      (source.writtenReceipt (depth + 1)).val = .planning source.seed.law
        (source.currentAt (depth + 2))
        (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
        (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget
        (compile source.seed.law (source.currentAt (depth + 2))
          (source.pendingTask (source.frameAt (depth + 2)).payments nonempty)
          (source.seed.actionsAt (source.currentAt (depth + 2))) source.seed.budget) := by
  have nonempty : source.pendingSlots (source.frameAt (depth + 2)).payments ≠ [] := by
    intro empty
    have member := source.pending_slot_has_original_identity _ index unpaid
    rw [empty] at member
    exact List.not_mem_nil member
  refine ⟨nonempty, ?_, ?_⟩
  · rw [source.actual_execution_word]
    unfold frameWord
    rw [if_neg (by omega), if_neg (by omega), ← (source.canonical_frame (depth + 2)).1]
    unfold decideAt
    rw [quiet, dif_neg nonempty]
    rfl
  · rw [source.written_report_exact]
    unfold reportAt
    rw [source.ordinal_exact, if_neg (by omega)]
    unfold decideAt
    rw [quiet, dif_neg nonempty]
    rfl

theorem complete_all_recorded (ordinal : Nat)
    (complete : source.pendingSlots (source.frameAt ordinal).payments = []) (index : source.Slot) :
    ∃ paid, (source.frameAt ordinal).payments index = some paid := by
  cases recorded : (source.frameAt ordinal).payments index with
  | some paid => exact ⟨paid, rfl⟩
  | none =>
      have pending := (source.pending_index_iff _ index).mpr recorded
      have inside : source.seed.slot index ∈ source.pendingSlots (source.frameAt ordinal).payments :=
        List.mem_map.mpr ⟨index, pending, rfl⟩
      rw [complete] at inside
      exact False.elim (List.not_mem_nil inside)

theorem completion_persists (ordinal later : Nat)
    (complete : source.pendingSlots (source.frameAt ordinal).payments = []) :
    source.pendingSlots (source.frameAt (ordinal + later)).payments = [] := by
  cases pending : source.pendingIndices (source.frameAt (ordinal + later)).payments with
  | nil => exact congrArg (List.map source.seed.slot) pending
  | cons index tail =>
      have inside : index ∈ source.pendingIndices (source.frameAt (ordinal + later)).payments := by
        rw [pending]
        exact List.mem_cons_self
      have unpaid := (source.pending_index_iff _ index).mp inside
      obtain ⟨paid, recorded⟩ := source.complete_all_recorded ordinal complete index
      have stays := source.recorded_payment_preserved ordinal later index paid recorded
      rw [unpaid] at stays
      cases stays

theorem completed_word_is_source_continuation (ordinal later : Nat) (started : 2 ≤ ordinal)
    (complete : source.pendingSlots (source.frameAt ordinal).payments = [])
    (quiet : source.incoming? (source.currentAt (ordinal + later)) = none := by rfl) :
    ProgrammeSource.rawEvent source.input
      (ProgrammeHistory.visitAt source.input (ordinal + later)).current =
        (source.completionReport (source.currentAt (ordinal + later))).word := by
  rw [(source.canonical_frame (ordinal + later)).2]
  unfold frameWord
  rw [if_neg (by omega), if_neg (by omega), ← (source.canonical_frame (ordinal + later)).1]
  unfold decideAt
  rw [quiet, dif_pos (source.completion_persists ordinal later complete)]
  rfl

theorem no_requests_after_completion (ordinal later : Nat) (started : 2 ≤ ordinal)
    (complete : source.pendingSlots (source.frameAt ordinal).payments = [])
    (silent : ∀ current, (source.completionReport current).word = [] := by intro current; rfl)
    (quiet : source.incoming? (source.currentAt (ordinal + later)) = none := by rfl) :
    ProgrammeSource.rawEvent source.input
      (ProgrammeHistory.visitAt source.input (ordinal + later)).current = [] := by
  rw [source.completed_word_is_source_continuation ordinal later started complete quiet, silent]

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

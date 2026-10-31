import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeService

/-! A process-generated native lifecycle run over each original service slot.
Every running visit crosses a live obligation; a terminal slot is retained
with its first actual receipt and is never readmitted or reopened.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

def paidArchive (index : source.Slot) (depth : Nat)
    (paid : source.ActualSlotPaid (depth + 1) index) : TerminalArchive (V source) :=
  ⟨obligation source index, ⟨index, depth + 1⟩,
    .fulfilled ⟨rfl, rfl, visitReceipt source index depth, paid⟩⟩

inductive Shape (index : source.Slot) (ordinal : Nat)
    (state : ResponsibilityState (V source)) : Type
  | live (unpaid : (source.frameAt ordinal).payments index = none)
      (slots : state.slots = [.live (obligation source index)])
  | terminal (depth : Nat) (paid : source.ActualSlotPaid (depth + 1) index)
      (recorded : (source.frameAt ordinal).payments index = some (depth + 1))
      (slots : state.slots = [.terminal (paidArchive source index depth paid)])

structure Prefix (index : source.Slot) (depth : Nat) where
  state : ResponsibilityState (V source)
  run : (process source).Run (ResponsibilityState.empty (V source)) state
  shape : Shape source index (depth + 1) state

theorem initial_unpaid (index : source.Slot) :
    (source.frameAt 1).payments index = none := by
  cases recorded : (source.frameAt 1).payments index with
  | none => rfl
  | some paid =>
      have sound := source.frame_payment_sound 1 index paid recorded
      omega

def initialPrefix (index : source.Slot) : Prefix source index 0 where
  state := admittedState source index
  run := .step .nil (admissionEdge source index)
  shape := .live (initial_unpaid source index) rfl

theorem next_paid (index : source.Slot) (ordinal : Nat)
    (unpaid : (source.frameAt ordinal).payments index = none)
    (paid : source.ActualSlotPaid ordinal index) :
    (source.frameAt (ordinal + 1)).payments index = some ordinal := by
  change source.update (source.frameAt ordinal).payments (source.frameAt ordinal).raw
    (source.frameWord ordinal (source.frameAt ordinal)) ordinal index = some ordinal
  simp only [OutstandingSource.update, unpaid,
    if_pos ((source.prefix_payment_is_actual ordinal index).mpr paid)]

theorem next_unpaid (index : source.Slot) (ordinal : Nat)
    (unpaid : (source.frameAt ordinal).payments index = none)
    (notPaid : ¬ source.ActualSlotPaid ordinal index) :
    (source.frameAt (ordinal + 1)).payments index = none := by
  apply (source.unpaid_iff_no_actual_payment _ index).mpr
  intro earlier bound paid
  by_cases before : earlier < ordinal
  · exact (source.unpaid_iff_no_actual_payment ordinal index).mp unpaid earlier before paid
  · have same : earlier = ordinal := by omega
    exact notPaid (same ▸ paid)

def advancePrefix (index : source.Slot) (depth : Nat)
    (prior : Prefix source index depth) : Prefix source index (depth + 1) := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
      have present : state.slots.get address = .live (obligation source index) := by
        simp [slots, address]
      let edge : (process source).Edge state :=
        .cross address (obligation source index) present (review source index depth)
      by_cases paid : source.ActualSlotPaid (depth + 1) index
      · exact {
          state := edge.target
          run := .step run edge
          shape := .terminal depth paid (next_paid source index (depth + 1) unpaid paid)
            (by simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition,
              reviewSource, review, dif_pos paid, slots, address, BoundaryDisposition.targetSlot, paidArchive]) }
      · exact {
          state := edge.target
          run := .step run edge
          shape := .live (next_unpaid source index (depth + 1) unpaid paid)
            (by simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition,
              reviewSource, review, dif_neg paid, slots, address, BoundaryDisposition.targetSlot,
              ActiveCarryDisposition.target]) }
  | terminal paidDepth paid recorded slots =>
      exact {
        state := state
        run := run
        shape := .terminal paidDepth paid
          (source.recorded_payment_preserved (depth + 1) 1 index (paidDepth + 1) recorded) slots }

def historyAt (index : source.Slot) : (depth : Nat) → Prefix source index depth
  | 0 => initialPrefix source index
  | depth + 1 => advancePrefix source index depth (historyAt index depth)

theorem native_live_iff_unpaid (index : source.Slot) (depth : Nat) :
    (historyAt source index depth).state.LiveAt 0 ↔
      (source.frameAt (depth + 1)).payments index = none := by
  cases (historyAt source index depth).shape with
  | live unpaid slots =>
      constructor
      · intro _; exact unpaid
      · intro _; exact ⟨obligation source index, by simp [slots]⟩
  | terminal paidDepth paid recorded slots =>
      constructor
      · rintro ⟨other, live⟩
        simp only [slots, List.getElem?_cons_zero] at live
        cases live
      · intro unpaid
        rw [unpaid] at recorded
        cases recorded

theorem native_terminal_iff_recorded (index : source.Slot) (depth : Nat) :
    (historyAt source index depth).state.TerminalAt 0 ↔
      ∃ paid, (source.frameAt (depth + 1)).payments index = some paid := by
  cases (historyAt source index depth).shape with
  | live unpaid slots =>
      constructor
      · rintro ⟨archive, terminal⟩
        simp only [slots, List.getElem?_cons_zero] at terminal
        cases terminal
      · rintro ⟨paid, recorded⟩
        rw [unpaid] at recorded
        cases recorded
  | terminal paidDepth paid recorded slots =>
      exact ⟨fun _ => ⟨paidDepth + 1, recorded⟩,
        fun _ => ⟨paidArchive source index paidDepth paid, by simp [slots]⟩⟩

theorem terminal_has_original_actual_receipt (index : source.Slot) (depth : Nat)
    (terminal : (historyAt source index depth).state.TerminalAt 0) :
    ∃ (paidDepth : Nat) (paid : source.ActualSlotPaid (paidDepth + 1) index),
      (source.frameAt (depth + 1)).payments index = some (paidDepth + 1) ∧
      (historyAt source index depth).state.slots =
        [.terminal (paidArchive source index paidDepth paid)] ∧
      ProgrammeLedger.transferReceiptOf source.input (source.taskWrite paidDepth).2 =
        some (source.writtenReceipt paidDepth) := by
  cases (historyAt source index depth).shape with
  | live unpaid slots =>
      obtain ⟨paid, recorded⟩ := (native_terminal_iff_recorded source index depth).mp terminal
      rw [unpaid] at recorded
      cases recorded
  | terminal paidDepth paid recorded slots =>
      exact ⟨paidDepth, paid, recorded, slots, source.receipt_is_in_original_task_write paidDepth⟩

theorem task_complete_iff_all_native_terminal (depth : Nat) :
    source.pendingSlots (source.frameAt (depth + 1)).payments = [] ↔
      ∀ index, (historyAt source index depth).state.TerminalAt 0 := by
  constructor
  · intro complete index
    exact (native_terminal_iff_recorded source index depth).mpr
      (source.complete_all_recorded (depth + 1) complete index)
  · intro settled
    cases pending : source.pendingIndices (source.frameAt (depth + 1)).payments with
    | nil => exact congrArg (List.map source.seed.slot) pending
    | cons index tail =>
        have member : index ∈ source.pendingIndices (source.frameAt (depth + 1)).payments := by
          rw [pending]
          exact List.mem_cons_self
        have unpaid := (source.pending_index_iff _ index).mp member
        obtain ⟨paid, recorded⟩ := (native_terminal_iff_recorded source index depth).mp (settled index)
        rw [unpaid] at recorded
        cases recorded

theorem terminal_next_state_is_preserved (index : source.Slot) (depth : Nat)
    (terminal : (historyAt source index depth).state.TerminalAt 0) :
    (historyAt source index (depth + 1)).state = (historyAt source index depth).state := by
  change (advancePrefix source index depth (historyAt source index depth)).state = _
  generalize historyAt source index depth = prior at *
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      obtain ⟨archive, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present
  | terminal paidDepth paid recorded slots => rfl

theorem terminal_state_is_preserved (index : source.Slot) (depth later : Nat)
    (terminal : (historyAt source index depth).state.TerminalAt 0) :
    (historyAt source index (depth + later)).state = (historyAt source index depth).state := by
  induction later with
  | zero => rfl
  | succ later ih =>
      have stillTerminal : (historyAt source index (depth + later)).state.TerminalAt 0 := by
        rw [ih]
        exact terminal
      exact (terminal_next_state_is_preserved source index (depth + later) stillTerminal).trans ih

theorem native_run_history_is_exact (index : source.Slot) (depth : Nat) :
    (historyAt source index depth).state.history = (historyAt source index depth).run.events := by
  simpa [ResponsibilityState.empty] using NativeResponsibilityProcess.Run.history_eq (process source) (historyAt source index depth).run

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.NativeService

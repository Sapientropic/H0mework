import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeService

/-! A process-generated native lifecycle run over each original service slot.
Every running visit crosses a live obligation; a terminal slot is retained
with its first actual receipt and is never readmitted or reopened.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (inputs : List (RawEvent Party Good Port Technology Instrument))

abbrev frameAt (ordinal : Nat) := (OutstandingSource.History.trailAt source inputs ordinal).frame

theorem complete_all_recorded (ordinal : Nat)
    (complete : source.pendingSlots (frameAt source inputs ordinal).payments = []) (index : source.Slot) :
    ∃ paid, (frameAt source inputs ordinal).payments index = some paid := by
  cases recorded : (frameAt source inputs ordinal).payments index with
  | some paid => exact ⟨paid, rfl⟩
  | none =>
      have inside := source.pending_slot_has_original_identity _ index recorded
      rw [complete] at inside
      exact False.elim (List.not_mem_nil inside)

def paidArchive (index : source.Slot) (depth : Nat)
    (paid : (ActualSlotPaid source inputs) (depth + 1) index) : TerminalArchive (V source inputs) :=
  ⟨obligation source inputs index, ⟨index, depth + 1, none⟩,
    .fulfilled ⟨rfl, rfl, visitReceipt source inputs index depth, paid⟩⟩

inductive Shape (index : source.Slot) (ordinal : Nat)
    (state : ResponsibilityState (V source inputs)) : Type
  | live (unpaid : ((frameAt source inputs) ordinal).payments index = none)
      (slots : state.slots = [.live (obligation source inputs index)])
  | terminal (depth : Nat) (paid : (ActualSlotPaid source inputs) (depth + 1) index)
      (recorded : ((frameAt source inputs) ordinal).payments index = some (depth + 1))
      (slots : state.slots = [.terminal (paidArchive source inputs index depth paid)])

structure Prefix (index : source.Slot) (depth : Nat) where
  state : ResponsibilityState (V source inputs)
  run : (process source inputs).Run (ResponsibilityState.empty (V source inputs)) state
  shape : Shape source inputs index (depth + 1) state

theorem initial_unpaid (index : source.Slot) :
    ((frameAt source inputs) 1).payments index = none := by
  cases recorded : ((frameAt source inputs) 1).payments index with
  | none => rfl
  | some paid =>
      have sound := (OutstandingSource.History.recorded_payment_is_own_actual source inputs) 1 index paid recorded
      omega

def initialPrefix (index : source.Slot) : Prefix source inputs index 0 where
  state := admittedState source inputs index
  run := .step .nil (admissionEdge source inputs index)
  shape := .live (initial_unpaid source inputs index) rfl

theorem next_paid (index : source.Slot) (ordinal : Nat)
    (unpaid : (frameAt source inputs ordinal).payments index = none)
    (paid : ActualSlotPaid source inputs ordinal index) :
    (frameAt source inputs (ordinal + 1)).payments index = some ordinal := by
  change source.update (frameAt source inputs ordinal).payments (frameAt source inputs ordinal).raw
    (OutstandingSource.History.word source inputs ordinal (frameAt source inputs ordinal))
    (OutstandingSource.History.trailAt source inputs ordinal).length index = some ordinal
  rw [OutstandingSource.History.length_exact]
  simp only [OutstandingSource.update, unpaid,
    if_pos ((prefix_payment_is_actual source inputs ordinal index).mpr paid)]

theorem next_unpaid (index : source.Slot) (ordinal : Nat)
    (unpaid : (frameAt source inputs ordinal).payments index = none)
    (notPaid : ¬ ActualSlotPaid source inputs ordinal index) :
    (frameAt source inputs (ordinal + 1)).payments index = none := by
  change source.update (frameAt source inputs ordinal).payments (frameAt source inputs ordinal).raw
    (OutstandingSource.History.word source inputs ordinal (frameAt source inputs ordinal))
    (OutstandingSource.History.trailAt source inputs ordinal).length index = none
  rw [OutstandingSource.History.length_exact]
  simp only [OutstandingSource.update, unpaid,
    if_neg (fun paid => notPaid ((prefix_payment_is_actual source inputs ordinal index).mp paid))]

def advancePrefix (index : source.Slot) (depth : Nat)
    (prior : Prefix source inputs index depth) : Prefix source inputs index (depth + 1) := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
      have present : state.slots.get address = .live (obligation source inputs index) := by
        simp [slots, address]
      let edge : (process source inputs).Edge state :=
        .cross address (obligation source inputs index) present (review source inputs index depth)
      by_cases paid : (ActualSlotPaid source inputs) (depth + 1) index
      · exact {
          state := edge.target
          run := .step run edge
          shape := .terminal depth paid (next_paid source inputs index (depth + 1) unpaid paid)
            (by simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition,
              reviewSource, review, dif_pos paid, slots, address, BoundaryDisposition.targetSlot, paidArchive, visitReceipt]) }
      · exact {
          state := edge.target
          run := .step run edge
          shape := .live (next_unpaid source inputs index (depth + 1) unpaid paid)
            (by simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition,
              reviewSource, review, dif_neg paid, slots, address, BoundaryDisposition.targetSlot,
              ActiveCarryDisposition.target]) }
  | terminal paidDepth paid recorded slots =>
      exact {
        state := state
        run := run
        shape := .terminal paidDepth paid
          ((OutstandingSource.History.archive_preserved source inputs) (depth + 1) 1 index (paidDepth + 1) recorded) slots }

def historyAt (index : source.Slot) : (depth : Nat) → Prefix source inputs index depth
  | 0 => initialPrefix source inputs index
  | depth + 1 => advancePrefix source inputs index depth (historyAt index depth)

theorem native_live_iff_unpaid (index : source.Slot) (depth : Nat) :
    (historyAt source inputs index depth).state.LiveAt 0 ↔
      ((frameAt source inputs) (depth + 1)).payments index = none := by
  cases (historyAt source inputs index depth).shape with
  | live unpaid slots =>
      constructor
      · intro _; exact unpaid
      · intro _; exact ⟨obligation source inputs index, by simp [slots]⟩
  | terminal paidDepth paid recorded slots =>
      constructor
      · rintro ⟨other, live⟩
        simp only [slots, List.getElem?_cons_zero] at live
        cases live
      · intro unpaid
        rw [unpaid] at recorded
        cases recorded

theorem native_terminal_iff_recorded (index : source.Slot) (depth : Nat) :
    (historyAt source inputs index depth).state.TerminalAt 0 ↔
      ∃ paid, ((frameAt source inputs) (depth + 1)).payments index = some paid := by
  cases (historyAt source inputs index depth).shape with
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
        fun _ => ⟨paidArchive source inputs index paidDepth paid, by simp [slots]⟩⟩

theorem terminal_has_original_actual_receipt (index : source.Slot) (depth : Nat)
    (terminal : (historyAt source inputs index depth).state.TerminalAt 0) :
    ∃ (paidDepth : Nat) (paid : (ActualSlotPaid source inputs) (paidDepth + 1) index),
      ((frameAt source inputs) (depth + 1)).payments index = some (paidDepth + 1) ∧
      (historyAt source inputs index depth).state.slots =
        [.terminal (paidArchive source inputs index paidDepth paid)] ∧
      ProgrammeLedger.transferReceiptOf (OutstandingSource.History.input source inputs) ((OutstandingSource.History.taskWrite source inputs) paidDepth).2 =
        some ((OutstandingSource.History.writtenReceipt source inputs) paidDepth) := by
  cases (historyAt source inputs index depth).shape with
  | live unpaid slots =>
      obtain ⟨paid, recorded⟩ := (native_terminal_iff_recorded source inputs index depth).mp terminal
      rw [unpaid] at recorded
      cases recorded
  | terminal paidDepth paid recorded slots =>
      exact ⟨paidDepth, paid, recorded, slots, (OutstandingSource.History.receipt_is_in_own_original_write source inputs) paidDepth⟩

theorem task_complete_iff_all_native_terminal (depth : Nat) :
    source.pendingSlots ((frameAt source inputs) (depth + 1)).payments = [] ↔
      ∀ index, (historyAt source inputs index depth).state.TerminalAt 0 := by
  constructor
  · intro complete index
    exact (native_terminal_iff_recorded source inputs index depth).mpr
      ((complete_all_recorded source inputs) (depth + 1) complete index)
  · intro settled
    cases pending : source.pendingIndices ((frameAt source inputs) (depth + 1)).payments with
    | nil => exact congrArg (List.map source.seed.slot) pending
    | cons index tail =>
        have member : index ∈ source.pendingIndices ((frameAt source inputs) (depth + 1)).payments := by
          rw [pending]
          exact List.mem_cons_self
        have unpaid := (source.pending_index_iff _ index).mp member
        obtain ⟨paid, recorded⟩ := (native_terminal_iff_recorded source inputs index depth).mp (settled index)
        rw [unpaid] at recorded
        cases recorded

theorem terminal_next_state_is_preserved (index : source.Slot) (depth : Nat)
    (terminal : (historyAt source inputs index depth).state.TerminalAt 0) :
    (historyAt source inputs index (depth + 1)).state = (historyAt source inputs index depth).state := by
  change (advancePrefix source inputs index depth (historyAt source inputs index depth)).state = _
  generalize historyAt source inputs index depth = prior at *
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      obtain ⟨archive, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present
  | terminal paidDepth paid recorded slots => rfl

theorem terminal_state_is_preserved (index : source.Slot) (depth later : Nat)
    (terminal : (historyAt source inputs index depth).state.TerminalAt 0) :
    (historyAt source inputs index (depth + later)).state = (historyAt source inputs index depth).state := by
  induction later with
  | zero => rfl
  | succ later ih =>
      have stillTerminal : (historyAt source inputs index (depth + later)).state.TerminalAt 0 := by
        rw [ih]
        exact terminal
      exact (terminal_next_state_is_preserved source inputs index (depth + later) stillTerminal).trans ih

theorem native_run_history_is_exact (index : source.Slot) (depth : Nat) :
    (historyAt source inputs index depth).state.history = (historyAt source inputs index depth).run.events := by
  simpa [ResponsibilityState.empty] using NativeResponsibilityProcess.Run.history_eq (process source inputs) (historyAt source inputs index depth).run

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource.History.NativeService

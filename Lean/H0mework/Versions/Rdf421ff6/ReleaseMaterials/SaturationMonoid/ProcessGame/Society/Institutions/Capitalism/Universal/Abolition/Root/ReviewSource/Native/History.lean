import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

def archive (index : Slot code) (depth : Nat) (paid : SlotPaid code depth index) : TerminalArchive (V code) :=
  ⟨obligation code index, ⟨index, depth + 1, none⟩,
    .fulfilled ⟨rfl, rfl, visitReceipt code index depth, ⟨Nat.zero_lt_succ depth, paid⟩⟩⟩

inductive Shape (index : Slot code) (state : ResponsibilityState (V code)) : Type
  | live (slots : state.slots = [.live (obligation code index)])
  | terminal (depth : Nat) (paid : SlotPaid code depth index)
      (slots : state.slots = [.terminal (archive code index depth paid)])

structure Prefix (index : Slot code) where
  private mk ::
  state : (process code).GeneratedState
  shape : Shape code index state.current

def initialPrefix (index : Slot code) : Prefix code index := ⟨admitted code index, .live rfl⟩

def advance (index : Slot code) (depth : Nat) (prior : Prefix code index) : Prefix code index := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | live slots =>
      let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ _⟩
      have present : state.current.slots.get address = .live (obligation code index) := by simp [slots, address]
      let event : Review code (obligation code index) := ⟨index, depth, rfl, rfl, rfl, none⟩
      let edge : (process code).Edge state.current := .cross address (obligation code index) present event
      if paid : SlotPaid code depth index then
        exact ⟨state.step (process code) edge, .terminal depth paid (by
          simp [NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, reviewSource, inputReceipt, event, edge, Event.Paid, paid, slots, address,
            BoundaryDisposition.targetSlot, archive])⟩
      else
        exact ⟨state.step (process code) edge, .live (by
          simp [NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, reviewSource, event, edge, Event.Paid, paid, slots, address,
            BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])⟩
  | terminal paidDepth paid slots => exact ⟨state, .terminal paidDepth paid slots⟩

def advanceRun (index : Slot code) (depth : Nat) (prior : Prefix code index) :
    (process code).Run prior.state.current (advance code index depth prior).state.current := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | live slots => dsimp only [advance]; split <;> exact .step .nil (.cross _ _ _ _)
  | terminal depth paid slots => exact .nil

/-- At ordinal zero this consumes the actual bootstrap task admission;
each successor then consumes that same source's next material occurrence. -/
def historyAt (index : Slot code) : Nat → Prefix code index
  | 0 => initialPrefix code index
  | depth + 1 => advance code index depth (historyAt index depth)

theorem no_later_visit_readmits_a_terminal_task
    (index : Slot code) (depth : Nat) (prior : Prefix code index)
    (terminal : prior.state.current.TerminalAt 0) :
    (advance code index depth prior).state = prior.state := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | live slots =>
      obtain ⟨receipt, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present
  | terminal depth paid slots => rfl

theorem every_original_obligation_is_retained (index : Slot code) (ordinal : Nat) :
    (historyAt code index ordinal).state.current.slots = [.live (obligation code index)] ∨
      ∃ depth paid, (historyAt code index ordinal).state.current.slots = [.terminal (archive code index depth paid)] := by
  cases (historyAt code index ordinal).shape with
  | live slots => exact .inl slots
  | terminal depth paid slots => exact .inr ⟨depth, paid, slots⟩

theorem every_terminal_has_its_own_actual_source_payment (index : Slot code) (ordinal : Nat)
    (terminal : (historyAt code index ordinal).state.current.TerminalAt 0) :
    ∃ depth paid, (historyAt code index ordinal).state.current.slots = [.terminal (archive code index depth paid)] ∧
      ProgrammeLedger.transferReceiptOf code.input (taskWrite code depth).2 = some (writtenReceipt code depth) := by
  cases (historyAt code index ordinal).shape with
  | live slots =>
      obtain ⟨receipt, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present
  | terminal depth paid slots => exact ⟨depth, paid, slots, receipt_is_in_the_original_whole_ledger_write code depth⟩

#print axioms historyAt
#print axioms no_later_visit_readmits_a_terminal_task
#print axioms every_terminal_has_its_own_actual_source_payment

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

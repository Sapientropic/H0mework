import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

inductive ThreadShape (index : Slot code) (state : ResponsibilityState (V code)) : Type
  | live (slots : state.slots = [.live (obligation code index)])
  | terminal (archive : TerminalArchive (V code)) (original : archive.obligation = obligation code index)
      (slots : state.slots = [.terminal archive])

structure Thread (index : Slot code) where
  private mk ::
  state : (process code).GeneratedState
  shape : ThreadShape code index state.current

def Thread.fromPrefix (index : Slot code) (prior : Prefix code index) : Thread code index := by
  refine ⟨prior.state, ?_⟩
  cases prior.shape with
  | live slots => exact .live slots
  | terminal depth paid slots => exact .terminal (archive code index depth paid) rfl slots

theorem Thread.fromPrefix_keeps_the_entire_original_state (index : Slot code) (prior : Prefix code index) :
    (Thread.fromPrefix code index prior).state = prior.state := rfl

def actualArchive (index : Slot code)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (paid : actual.Paid (code := code) index) : TerminalArchive (V code) :=
  ⟨obligation code index, ⟨index, 1, some actual⟩,
    .fulfilled ⟨rfl, rfl, .actual actual rfl actual.receipt, paid⟩⟩

def Thread.advance {index : Slot code} (thread : Thread code index)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) : Thread code index := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live slots =>
      let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ _⟩
      have present : state.current.slots.get address = .live (obligation code index) := by simp [slots, address]
      let event : Review code (obligation code index) := ⟨index, 0, rfl, rfl, rfl, some actual⟩
      let edge : (process code).Edge state.current := .cross address (obligation code index) present event
      if paid : actual.Paid (code := code) index then
        exact ⟨state.step (process code) edge, .terminal (actualArchive code index actual paid) rfl (by
          simp [NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, reviewSource, inputReceipt, event, edge, Event.Paid, paid, slots,
            address, BoundaryDisposition.targetSlot, actualArchive])⟩
      else
        exact ⟨state.step (process code) edge, .live (by
          simp [NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
            process, disposition, reviewSource, event, edge, Event.Paid, paid, slots,
            address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])⟩
  | terminal archive original slots => exact ⟨state, .terminal archive original slots⟩

def Thread.nativeRun {index : Slot code} (thread : Thread code index)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    (process code).Run thread.state.current (thread.advance code actual).state.current := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live slots => dsimp only [Thread.advance]; split <;> exact .step .nil (.cross _ _ _ _)
  | terminal archive original slots => exact .nil

theorem Thread.actual_payment_terminates_the_original_slot
    {index : Slot code} (thread : Thread code index)
    (live : thread.state.current.slots = [.live (obligation code index)])
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (paid : actual.Paid (code := code) index) :
    (thread.advance code actual).state.current.slots = [.terminal (actualArchive code index actual paid)] := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live slots =>
      simp [Thread.advance, paid, NativeResponsibilityProcess.GeneratedState.step,
        NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource, inputReceipt,
        Event.Paid, slots, BoundaryDisposition.targetSlot, actualArchive]
  | terminal archive original slots =>
      have impossible := slots.symm.trans live
      cases impossible

theorem Thread.completed_state_and_archive_are_never_readmitted
    {index : Slot code} (thread : Thread code index)
    (terminal : thread.state.current.TerminalAt 0)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    (thread.advance code actual).state = thread.state := by
  rcases thread with ⟨state, shape⟩
  cases shape with
  | live slots =>
      obtain ⟨archive, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present
  | terminal archive original slots => rfl

theorem Thread.original_obligation_is_always_retained {index : Slot code} (thread : Thread code index) :
    thread.state.current.slots = [.live (obligation code index)] ∨
      ∃ archive, thread.state.current.slots = [.terminal archive] ∧ archive.obligation = obligation code index := by
  cases thread.shape with
  | live slots => exact .inl slots
  | terminal archive original slots => exact .inr ⟨archive, slots, original⟩

#print axioms Thread.fromPrefix_keeps_the_entire_original_state
#print axioms Thread.nativeRun
#print axioms Thread.completed_state_and_archive_are_never_readmitted

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

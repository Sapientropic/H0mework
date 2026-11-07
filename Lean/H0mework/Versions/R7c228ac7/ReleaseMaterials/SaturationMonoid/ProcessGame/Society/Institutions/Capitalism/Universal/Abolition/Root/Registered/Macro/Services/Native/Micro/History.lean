import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.Thread
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.ActualCut

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

open ResponsibilityLifecycle Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (past : List (Compile.RawInput Party Good Port Technology Instrument))

/-- The address is in the actual finite Physical past. The current and target
remain readouts of that same source, including its microstep clock. -/
def sourceAt (position : Fin past.length) : SourceInput source :=
  ⟨inferInstance, depth, count, prefixLimit, renewalLimit, Physical.Prefix.eventCursor past position⟩

theorem source_payment_is_the_original_actual_payment (position : Fin past.length) (index : source.Slot) :
    (sourceAt source depth count prefixLimit renewalLimit past position).Paid index ↔
      PaidOn source depth count prefixLimit renewalLimit past position index := Iff.rfl

variable (index : source.Slot)

abbrev initial := Attached.fromThread (originalThread source depth count index)

/-- This folds the unique existing native process over the already occurred
source prefix. Missing indices generate no lifecycle event. -/
def history : Nat → Attached source (originalWords source depth count) index
  | 0 => initial source depth count index
  | length + 1 =>
      if present : length < past.length then
        (history length).advance (sourceAt source depth count prefixLimit renewalLimit past ⟨length, present⟩)
      else history length

def originalRun : (length : Nat) →
    (OutstandingSource.History.NativeService.threadProcess source (originalWords source depth count)).Run
      (originalThread source depth count index).state.current
      (history source depth count prefixLimit renewalLimit past index length).state.current
  | 0 => .nil
  | length + 1 => by
      unfold history
      split
      · exact (originalRun length).concatRuns _ ((history source depth count prefixLimit renewalLimit past index length).actualRun _)
      · exact originalRun length

def complete := history source depth count prefixLimit renewalLimit past index past.length

theorem live_at_cut_iff_original_and_actual_unpaid (length : Nat) (within : length ≤ past.length) :
    (history source depth count prefixLimit renewalLimit past index length).state.current.LiveAt 0 ↔
      originalPayments source depth count index = none ∧
        ∀ position : Fin past.length, position.val < length → ¬ PaidOn source depth count prefixLimit renewalLimit past position index := by
  induction length with
  | zero =>
      simpa [history, initial, Attached.fromThread] using original_native_slot_and_archive_are_preserved source depth count index
  | succ length prior =>
      have present : length < past.length := by omega
      have earlier := prior (by omega)
      rw [history, dif_pos present, Attached.advance_live_iff, earlier]
      change ((originalPayments source depth count index = none ∧
        ∀ position : Fin past.length, position.val < length → ¬ PaidOn source depth count prefixLimit renewalLimit past position index) ∧
          ¬ PaidOn source depth count prefixLimit renewalLimit past ⟨length, present⟩ index) ↔ _
      constructor
      · rintro ⟨⟨old, before⟩, last⟩
        refine ⟨old, ?_⟩
        intro position bound
        by_cases previous : position.val < length
        · exact before position previous
        · have same : position = ⟨length, present⟩ := by
            apply Fin.ext
            change position.val = length
            omega
          exact same ▸ last
      · rintro ⟨old, all⟩
        exact ⟨⟨old, fun position bound => all position (by omega)⟩, all ⟨length, present⟩ (by simp)⟩

theorem live_iff_the_original_service_readout_is_unpaid :
    (complete source depth count prefixLimit renewalLimit past index).state.current.LiveAt 0 ↔
      payments source depth count prefixLimit renewalLimit past index = none := by
  rw [an_unpaid_slot_has_no_hidden_original_or_actual_receipt]
  have exactPrefix := live_at_cut_iff_original_and_actual_unpaid source depth count prefixLimit renewalLimit past index past.length (Nat.le_refl _)
  simpa only [complete, Fin.isLt, true_implies] using exactPrefix

theorem terminal_iff_the_original_service_readout_is_paid :
    (complete source depth count prefixLimit renewalLimit past index).state.current.TerminalAt 0 ↔
      (payments source depth count prefixLimit renewalLimit past index).isSome = true := by
  classical
  have native := (complete source depth count prefixLimit renewalLimit past index).live_iff_not_terminal
  have actual := live_iff_the_original_service_readout_is_unpaid source depth count prefixLimit renewalLimit past index
  cases paid : payments source depth count prefixLimit renewalLimit past index with
  | none => simp only [paid, Option.isSome_none, Bool.false_eq_true] at actual ⊢; tauto
  | some ordinal => simp only [paid, Option.isSome_some, reduceCtorEq] at actual ⊢; tauto

theorem every_original_native_event_is_retained :
    (originalThread source depth count index).state.current.history <+:
      (complete source depth count prefixLimit renewalLimit past index).state.current.history := by
  have original := (originalRun source depth count prefixLimit renewalLimit past index past.length).history_eq
  unfold complete
  rw [original]
  exact List.prefix_append _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.originalRun
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro.terminal_iff_the_original_service_readout_is_paid

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem an_actual_payment_terminates_or_retains_the_original_archive
    {index : Slot code} (thread : Thread code index)
    (actual : SourceInput (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (paid : actual.Paid (code := code) index) :
    (thread.advance code actual).state.current.TerminalAt 0 := by
  cases original : thread.original_obligation_is_always_retained code with
  | inl live =>
      exact ⟨actualArchive code index actual paid,
        by rw [thread.actual_payment_terminates_the_original_slot code live actual paid]; rfl⟩
  | inr terminal =>
      obtain ⟨archive, slots, _⟩ := terminal
      have finished : thread.state.current.TerminalAt 0 := ⟨archive, by rw [slots]; rfl⟩
      rw [thread.completed_state_and_archive_are_never_readmitted code finished actual]
      exact finished

variable (depth count prefixLimit renewalLimit : Nat)
local notation "Raw" => Compile.RawInput Party Good Port Technology Instrument

theorem a_terminal_native_state_is_preserved_by_the_actual_suffix
    {index : Slot code} (past rest : List Raw) (thread : Thread code index)
    (terminal : thread.state.current.TerminalAt 0) :
    (fold (.source code) depth count prefixLimit renewalLimit past rest thread).state = thread.state := by
  induction rest generalizing past thread with
  | nil => rfl
  | cons raw rest inherited =>
      change (fold (.source code) depth count prefixLimit renewalLimit (past ++ [raw]) rest
        (thread.advance code (actualInput depth count prefixLimit renewalLimit past raw))).state = _
      have same := thread.completed_state_and_archive_are_never_readmitted code terminal
        (actualInput depth count prefixLimit renewalLimit past raw)
      exact (inherited _ _ (same.symm ▸ terminal)).trans same

theorem an_actual_paid_prefix_stays_terminal_after_every_actual_suffix
    {index : Slot code} (past rest : List Raw) (thread : Thread code index)
    (terminal : thread.state.current.TerminalAt 0) :
    (fold (.source code) depth count prefixLimit renewalLimit past rest thread).state.current.TerminalAt 0 := by
  rw [a_terminal_native_state_is_preserved_by_the_actual_suffix code depth count prefixLimit renewalLimit past rest thread terminal]
  exact terminal

#print axioms an_actual_payment_terminates_or_retains_the_original_archive
#print axioms a_terminal_native_state_is_preserved_by_the_actual_suffix

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

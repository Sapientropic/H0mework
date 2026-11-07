import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Transcript
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

namespace OriginalCut

private theorem empty_history_is_original (ordinal : Nat) :
    (OutstandingSource.History.trailAt source [] ordinal).frame = source.frameAt ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal prior =>
      change (⟨source.seed.law.next _ _, source.update _ _ _ _⟩ : source.Frame) = _
      rw [OutstandingSource.History.length_exact, prior]
      have sameWord : OutstandingSource.History.word source [] ordinal (source.frameAt ordinal) =
          source.frameWord ordinal (source.frameAt ordinal) := by
        unfold OutstandingSource.History.word OutstandingSource.History.report OutstandingSource.frameWord
        split_ifs <;> first | rfl | exact OutstandingSource.Decision.report_word source _
      rw [sameWord]
      rfl

def inputs (completed : Nat) := OutstandingSource.History.executedWords source [] completed

theorem input_count (completed : Nat) : (inputs source completed).length = completed :=
  OutstandingSource.History.executedWords_length source [] completed

theorem replay_is_the_original_cut (completed : Nat) :
    (OutstandingSource.History.replay source (inputs source completed)).frame = source.frameAt (completed + 2) :=
  (congrArg OutstandingSource.ExecutionPrefix.frame
    (OutstandingSource.History.executed_words_replay_the_actual_cut source [] completed)).trans
    (empty_history_is_original source (completed + 2))

theorem actual_history_keeps_the_original_raw_and_archive (completed : Nat) :
    (OutstandingSource.History.trailAt source (inputs source completed) ((inputs source completed).length + 2)).frame =
      source.frameAt (completed + 2) := by
  have exactPrefix := OutstandingSource.History.finite_prefix_exact source (inputs source completed)
    (inputs source completed).length (Nat.le_refl _)
  rw [List.take_length] at exactPrefix
  exact (congrArg OutstandingSource.ExecutionPrefix.frame exactPrefix).trans
    (replay_is_the_original_cut source completed)

def thread (completed : Nat) (index : source.Slot) :=
  OutstandingSource.History.NativeService.Thread.initial source (originInputs := inputs source completed) index

theorem native_state_is_the_entire_original_cut (completed : Nat) (index : source.Slot) :
    (thread source completed index).state.current =
      (OutstandingSource.History.NativeService.historyAt source (inputs source completed) index
        ((inputs source completed).length + 1)).state := rfl

theorem native_run_keeps_every_original_event (completed : Nat) (index : source.Slot) :
    (thread source completed index).state.generated.events =
      (OutstandingSource.History.NativeService.historyAt source (inputs source completed) index
        ((inputs source completed).length + 1)).run.events :=
  OutstandingSource.History.NativeService.Thread.initial_preserves_every_original_run_event source index

theorem native_live_iff_original_unpaid (completed : Nat) (index : source.Slot) :
    (thread source completed index).state.current.LiveAt 0 ↔
      (source.frameAt (completed + 2)).payments index = none := by
  rw [(thread source completed index).native_live_iff_unpaid source]
  exact iff_of_eq (congrArg (fun frame : source.Frame => frame.payments index = none)
    (actual_history_keeps_the_original_raw_and_archive source completed))

end OriginalCut
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.OriginalCut.actual_history_keeps_the_original_raw_and_archive
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.OriginalCut.native_run_keeps_every_original_event

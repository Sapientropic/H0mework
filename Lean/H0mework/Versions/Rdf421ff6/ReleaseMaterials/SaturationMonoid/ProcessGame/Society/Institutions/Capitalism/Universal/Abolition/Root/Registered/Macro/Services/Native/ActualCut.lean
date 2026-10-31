import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Cut

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument) (depth count : Nat)

theorem actual_cut_includes_original_request : 2 ≤ originalIndex source depth count := by
  unfold originalIndex Settlement.physicalIndex Settlement.oldCursor Settlement.oldFrame
  rw [Financial.Installation.Runtime.frames_cursor]
  induction count with
  | zero =>
      change 2 ≤ Financial.Installation.Cursor.physicalVisitIndex source.input
        (Financial.Installation.Cursor.next source.input (Financial.Installation.Ingress.start source.input depth))
      rw [Financial.Installation.Cursor.entry_has_one_actual_body source.input _ rfl]
      change 2 ≤ depth + 1 + 1
      omega
  | succ count prior =>
      exact prior.trans (Financial.Installation.Cursor.physical_index_monotone source.input
        (Financial.Installation.Runtime.cursorAt source.input depth count))

def originalWords := OriginalCut.inputs source (originalIndex source depth count - 2)

theorem macro_initial_is_the_exact_native_cut :
    (Actual.initial source.input depth count).raw =
      OutstandingSource.History.currentAt source (originalWords source depth count)
        ((originalWords source depth count).length + 2) := by
  have aligned := OriginalCut.actual_history_keeps_the_original_raw_and_archive source (originalIndex source depth count - 2)
  have enough := actual_cut_includes_original_request source depth count
  rw [Nat.sub_add_cancel enough] at aligned
  have rawAligned := congrArg OutstandingSource.Frame.raw aligned
  exact (source.canonical_frame (originalIndex source depth count)).1.trans
    (((OutstandingSource.History.actual_frame source (originalWords source depth count) _).1.trans rawAligned).symm)

def originalThread (index : source.Slot) :=
  OutstandingSource.History.NativeService.Thread.initial source (originInputs := originalWords source depth count) index

theorem original_native_slot_and_archive_are_preserved (index : source.Slot) :
    (originalThread source depth count index).state.current.LiveAt 0 ↔ originalPayments source depth count index = none := by
  have exactCut := OriginalCut.native_live_iff_original_unpaid source (originalIndex source depth count - 2) index
  rw [Nat.sub_add_cancel (actual_cut_includes_original_request source depth count)] at exactCut
  exact exactCut

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.macro_initial_is_the_exact_native_cut

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Pending

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth start : Nat)

theorem drained_cut_has_no_committed_pending :
    committedPending input depth (drain input depth start).last = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro origin member
  obtain ⟨pending, occurred⟩ := List.mem_filter.mp member
  have sameCursor : Settlement.oldCursor input depth (drain input depth start).last =
      Runtime.cursorAt input depth (drain input depth start).last := Runtime.frames_cursor input depth _
  have same := fresh_pending_is_the_unexecuted_physical_visit input
    (Runtime.cursorAt input depth (drain input depth start).last)
    (Runtime.cursorAt_accounting input depth _) (drain input depth start).stoppedBeforeFresh origin
    (by simpa only [sameCursor] using pending)
  have earlier := of_decide_eq_true occurred
  unfold AlreadyOccurred at earlier
  rw [same, Cursor.physicalVisit, ProgrammeHistory.visit_round] at earlier
  change input.initial.round + Cursor.physicalVisitIndex input (Runtime.cursorAt input depth (drain input depth start).last) <
    input.initial.round + Cursor.physicalVisitIndex input (Settlement.oldCursor input depth (drain input depth start).last) at earlier
  rw [sameCursor] at earlier
  exact (Nat.lt_irrefl _ earlier)

/-- The initial macro account is the actual drained frame's account. An
empty committed queue cannot mint another admission or a replacement GS. -/
theorem macro_initial_account_is_the_literal_drained_account :
    (settleCommitted input depth (drain input depth start).last).after =
      Legacy.generated input depth (drain input depth start).last ((frame input depth start).cursor input).account := by
  rw [empty_pending_keeps_the_literal_inherited_account input depth _
    (drained_cut_has_no_committed_pending input depth start)]
  rfl

#print axioms drained_cut_has_no_committed_pending
#print axioms macro_initial_account_is_the_literal_drained_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

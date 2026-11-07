import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain.Run
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Inherited

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem inventory_origin_is_exact
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (origin : Financial.InstructionOrigin input) (member : origin ∈ Financial.inventoryAt input visit) : origin.visit = visit := by
  cases emission : input.emission? with
  | none =>
      simp only [Financial.inventoryAt, emission, Financial.administrativeInventoryAt] at member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      rfl
  | some emit =>
      simp only [Financial.inventoryAt, emission, List.mem_append] at member
      rcases member with administrative | traced
      · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp administrative; rfl
      · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp traced; rfl

theorem fresh_pending_is_the_unexecuted_physical_visit (cursor : Cursor.State input)
    (accounting : cursor.phase = .accounting) (fresh : Cursor.FreshBody input cursor)
    (origin : Financial.InstructionOrigin input) (member : origin ∈ Cursor.pending input cursor) :
    origin.visit = Cursor.physicalVisit input cursor := by
  have first : cursor.position = 0 ∧ cursor.ahead = 0 := by
    rcases fresh with entering | first
    · rw [accounting] at entering; cases entering
    · exact first
  have current : origin ∈ Financial.inventoryAt input (Cursor.originalVisit input cursor) := by
    simpa only [Cursor.pending, Cursor.currentPending, Cursor.queuedCount, first.1, first.2,
      if_pos rfl, Nat.zero_sub, List.range_zero, List.flatMap_nil, List.append_nil, List.drop_zero] using member
  have original := inventory_origin_is_exact input _ origin current
  simpa [Cursor.originalVisit, Cursor.physicalVisit, Cursor.physicalVisitIndex, first.1, first.2] using original

variable (depth start : Nat)

theorem remaining_requests_are_only_the_unexecuted_visit (origin : Financial.InstructionOrigin input)
    (member : origin ∈ Cursor.pending input ((frame input depth start).cursor input)) :
    origin.visit = Cursor.physicalVisit input ((Runtime.frames input depth start).cursor input) := by
  have same := fresh_pending_is_the_unexecuted_physical_visit input
    (Runtime.cursorAt input depth (drain input depth start).last)
    (Runtime.cursorAt_accounting input depth _) (drain input depth start).stoppedBeforeFresh origin
    (by simpa only [frame, Runtime.frames_cursor] using member)
  exact same.trans (by simpa only [frame, Runtime.frames_cursor] using no_physical_body_is_replayed input depth start)

theorem no_already_occurred_pending_request_remains (origin : Financial.InstructionOrigin input)
    (old : origin ∈ committedPending input depth start) :
    origin ∉ Cursor.pending input ((frame input depth start).cursor input) := by
  intro remained
  have same := remaining_requests_are_only_the_unexecuted_visit input depth start origin remained
  have occurred := of_decide_eq_true (List.mem_filter.mp old).2
  unfold AlreadyOccurred at occurred
  rw [same, Cursor.physicalVisit, ProgrammeHistory.visit_round] at occurred
  change _ < input.initial.round + Cursor.physicalVisitIndex input ((Runtime.frames input depth start).cursor input) at occurred
  omega

#print axioms remaining_requests_are_only_the_unexecuted_visit
#print axioms no_already_occurred_pending_request_remains

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

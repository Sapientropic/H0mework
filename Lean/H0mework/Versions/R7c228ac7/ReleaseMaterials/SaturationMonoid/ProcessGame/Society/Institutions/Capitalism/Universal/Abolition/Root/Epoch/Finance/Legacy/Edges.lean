import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Receipts
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Lifecycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def edge {old : ResponsibilityState (Financial.vocabulary input)} :
    (Financial.process input).Edge old → (process input depth count).Edge (state input depth count old)
  | .admit claim => .admit (.inl claim)
  | .cross position oldObligation present oldBoundary =>
      .cross ⟨position.val, by simpa only [state, List.length_map] using position.isLt⟩
        (obligation input depth count oldObligation) (by
          simpa only [state, List.get_eq_getElem, List.getElem_map, slot]
            using congrArg (slot input depth count) present)
        (boundary input depth count oldBoundary)
  | .reopen _ _ _ impossible => impossible.elim

theorem boundary_target {old : AdmittedObligation (Financial.vocabulary input)}
    (review : Financial.Boundary input old) :
    slot input depth count (Financial.boundaryDisposition input review).targetSlot =
      (boundaryDisposition input depth count (boundary input depth count review)).targetSlot := by
  by_cases cleared : review.event.after input = 0
  · have mapped : (boundary input depth count review).event.after input depth count = 0 := cleared
    simp only [Financial.boundaryDisposition, dif_pos cleared, boundaryDisposition, dif_pos mapped]
    rfl
  · have mapped : ¬ (boundary input depth count review).event.after input depth count = 0 := cleared
    simp only [Financial.boundaryDisposition, dif_neg cleared, boundaryDisposition, dif_neg mapped]
    rfl

theorem edge_event {old : ResponsibilityState (Financial.vocabulary input)}
    (original : (Financial.process input).Edge old) :
    lifecycle input depth count original.lifecycleEvent =
      (edge input depth count original).lifecycleEvent := by
  cases original with
  | admit claim =>
      simp only [edge, NativeResponsibilityProcess.Edge.lifecycleEvent, lifecycle,
        Financial.process, process, Finance.admission, state, List.length_map]
  | cross position oldObligation present oldBoundary =>
      change Financial.Boundary input oldObligation at oldBoundary
      by_cases cleared : oldBoundary.event.after input = 0
      · have mapped : (boundary input depth count oldBoundary).event.after input depth count = 0 := cleared
        simp only [edge, NativeResponsibilityProcess.Edge.lifecycleEvent, Financial.process, process,
          Financial.boundaryDisposition, dif_pos cleared, boundaryDisposition, dif_pos mapped]
        rfl
      · have mapped : ¬ (boundary input depth count oldBoundary).event.after input depth count = 0 := cleared
        simp only [edge, NativeResponsibilityProcess.Edge.lifecycleEvent, Financial.process, process,
          Financial.boundaryDisposition, dif_neg cleared, boundaryDisposition, dif_neg mapped]
        rfl
  | reopen _ _ _ impossible => exact impossible.elim

private theorem state_ext {V : ResponsibilityLifecycle.Vocabulary} {first second : ResponsibilityState V}
    (slots : first.slots = second.slots) (history : first.history = second.history) : first = second := by
  cases first
  cases second
  cases slots
  cases history
  rfl

/-- Both target lists commute, including archived final receipts and the
original ordered lifecycle record. No material operation is interpreted. -/
theorem edge_target {old : ResponsibilityState (Financial.vocabulary input)}
    (original : (Financial.process input).Edge old) :
    (edge input depth count original).target = state input depth count original.target := by
  apply state_ext
  · cases original with
    | admit claim =>
        simp only [edge, NativeResponsibilityProcess.Edge.target, state, List.map_append,
          List.map_cons, List.map_nil, slot, process, Financial.process, Finance.admission, payload_obligation]
    | cross position oldObligation present oldBoundary =>
        change Financial.Boundary input oldObligation at oldBoundary
        simp only [edge, NativeResponsibilityProcess.Edge.target, state, List.map_set, process, Financial.process]
        rw [boundary_target input depth count oldBoundary]
    | reopen _ _ _ impossible => exact impossible.elim
  · rw [NativeResponsibilityProcess.Edge.history_append]
    change _ = List.map (lifecycle input depth count) original.target.history
    rw [original.history_append, List.map_append, List.map_cons, List.map_nil, edge_event]
    rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

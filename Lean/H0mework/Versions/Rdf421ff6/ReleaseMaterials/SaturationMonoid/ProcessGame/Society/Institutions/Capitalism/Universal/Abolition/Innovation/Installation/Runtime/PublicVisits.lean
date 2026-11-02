import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.FirstReview

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

variable (nature : RequestAt) (admission : InitialAdmissionAt (firstOrigin nature))

/-- These are restrictions of the original runtime at its generated raw
boundaries. No new process, input stream or authority is created. -/
def publicVisit : Nat → Macro.Public.Runtime.Frame (firstOrigin nature) admission
  | 0 => (firstPublic nature admission).drained
  | index + 1 => (publicVisit index).next.drained

theorem every_public_visit_is_ready_at_its_original_raw_boundary (index : Nat) :
    ¬ (publicVisit nature admission index).HasWork := by
  cases index <;> exact Macro.Public.Runtime.Frame.drain _ |>.2.2

theorem every_public_visit_is_the_same_original_activated_frame
    (chosen : InitialAdmission.select (firstOrigin nature) = .admitted admission) (index : Nat) :
    boundary nature (index + 1) = .enacted (firstOrigin nature) admission (publicVisit nature admission index) := by
  induction index with
  | zero => exact (the_generated_admission_reaches_its_fully_accounted_actual_public_cut nature admission chosen).1
  | succ index inherited =>
      exact an_actual_public_step_reaches_its_own_next_native_boundary nature
        (publicVisit nature admission index) (boundaryTick nature (index + 1)) inherited

theorem the_same_engine_visits_every_trial_financing_and_observation_boundary
    (chosen : InitialAdmission.select (firstOrigin nature) = .admitted admission) (index : Nat) :
    (Macro.Runtime.run (review := none) input 0 0 datum 0 0 (reader nature)
      (boundaryTick nature (index + 1) + 1)).engine.node =
      .active (publicVisit nature admission index).presentation := by
  have registered := every_boundary_is_visited_by_the_same_original_engine nature (index + 1)
  exact registered.trans (congrArg (fun frame : Macro.Runtime.ActivatedFrame (review := none)
    input 0 count 0 0 0 count => RootInquiryProcessNode.active frame.presentation)
      (every_public_visit_is_the_same_original_activated_frame nature admission chosen index))

theorem every_trial_visit_keeps_the_same_whole_native_history (index : Nat) :
    (publicVisit nature admission index).account.current.history <+:
      (publicVisit nature admission (index + 1)).account.current.history ∧
    (publicVisit nature admission index).account.current.slots.map (Epoch.Finance.slotClaim input 0 count) <+:
      (publicVisit nature admission (index + 1)).account.current.slots.map (Epoch.Finance.slotClaim input 0 count) := by
  let frame := publicVisit nature admission index
  have paid := the_generated_drain_keeps_the_actual_body_and_complete_account_run frame.next
  exact ⟨List.IsPrefix.trans frame.next_keeps_the_complete_original_history paid.2.1,
    List.IsPrefix.trans frame.next_keeps_all_original_claims paid.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

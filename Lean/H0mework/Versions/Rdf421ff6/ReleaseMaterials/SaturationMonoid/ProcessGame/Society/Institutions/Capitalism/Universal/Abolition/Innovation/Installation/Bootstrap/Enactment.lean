import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Selection

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Functions.Revision

noncomputable section

theorem the_original_source_itself_generates_its_first_public_admission (nature : RequestAt) :
    ∃ admission, InitialAdmission.select (firstOrigin nature) = .admitted admission := by
  apply InitialAdmission.a_publicly_available_source_plan_forces_admission
  refine ⟨Control.Scenario.commonWork, ?_, the_first_review_has_its_actual_whole_scope_common_candidate nature⟩
  rw [the_first_actual_candidate_domain_has_no_trial_or_target]
  exact List.mem_cons_self

/-- Read the actual compiler's admission. The failed branch is excluded
by the source-generated common work, not by a supplied successful target. -/
def actualAdmission (nature : RequestAt) : InitialAdmissionAt (firstOrigin nature) :=
  match chosen : InitialAdmission.select (firstOrigin nature) with
  | .admitted admission => admission
  | .obstructed _ => False.elim (by
      obtain ⟨admission, generated⟩ := the_original_source_itself_generates_its_first_public_admission nature
      cases chosen.symm.trans generated)

theorem the_first_admission_is_the_actual_source_compiler_choice (nature : RequestAt) :
    InitialAdmission.select (firstOrigin nature) = .admitted (actualAdmission nature) := by
  unfold actualAdmission
  split
  · rename_i admission selected
    exact selected
  · rename_i failed selected
    obtain ⟨admission, generated⟩ := the_original_source_itself_generates_its_first_public_admission nature
    cases selected.symm.trans generated

theorem every_first_admission_starts_the_actual_original_common_work
    (nature : RequestAt) (admission : InitialAdmissionAt (firstOrigin nature)) :
    InitialAdmission.start admission = Physical.receive Physical.initial (.execute Control.Scenario.commonWork) := by
  cases admission with
  | legacy ready => exact (no_initial_admission_can_relabel_the_old_seeking_current_as_paid_renewal nature ready).elim
  | publicPlan plan selected =>
      change Physical.receive Physical.initial (.execute plan.rawWord) = _
      rw [every_first_public_plan_is_the_original_common_word nature plan]

abbrev actualPublicVisit (nature : RequestAt) (index : Nat) := publicVisit nature (actualAdmission nature) index

theorem the_first_actual_public_visit_keeps_the_literal_source_body (nature : RequestAt) :
    (actualPublicVisit nature 0).snapshot =
      Physical.next (Physical.receive Physical.initial (.execute Control.Scenario.commonWork)) := by
  have same := Observation.the_generated_internal_drain_keeps_the_same_actual_snapshot
    (firstPublic nature (actualAdmission nature))
  refine same.trans ?_
  rw [(firstPublic nature (actualAdmission nature)).snapshot_is_the_literal_after]
  exact congrArg Physical.next (every_first_admission_starts_the_actual_original_common_work nature (actualAdmission nature))

theorem the_first_actual_public_visit_is_installed_by_the_original_engine (nature : RequestAt) :
    boundary nature 1 = .enacted (firstOrigin nature) (actualAdmission nature) (actualPublicVisit nature 0) :=
  every_public_visit_is_the_same_original_activated_frame nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 0

theorem every_actual_trial_visit_is_an_original_root_current (nature : RequestAt) (index : Nat) :
    (Macro.Runtime.run (review := none) input 0 0 datum 0 0 (reader nature)
      (boundaryTick nature (index + 1) + 1)).engine.node =
      .active (actualPublicVisit nature index).presentation :=
  the_same_engine_visits_every_trial_financing_and_observation_boundary nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) index

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

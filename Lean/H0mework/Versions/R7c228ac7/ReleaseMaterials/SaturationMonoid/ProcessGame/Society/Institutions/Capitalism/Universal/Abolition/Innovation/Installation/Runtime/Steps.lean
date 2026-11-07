import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.PublicVisits

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open Functions.Revision

noncomputable section

variable (nature : RequestAt) (admission : InitialAdmissionAt (firstOrigin nature))
  (chosen : InitialAdmission.select (firstOrigin nature) = .admitted admission) (index : Nat)

private theorem the_visit_selects_its_actual_source_input (raw : InputAt)
    (source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (publicVisit nature admission index).snapshot.past) = raw) :
    selected nature (publicVisit nature admission index).actual.readerCursor.past = raw := by
  rw [the_trial_reader_cursor_is_the_literal_absolute_source_prefix]
  exact source

include chosen

theorem the_actual_primitive_visit_has_its_same_next_source_cursor
    (request : RequestAt)
    (source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (publicVisit nature admission index).snapshot.past) = .primitive request) :
    (publicVisit nature admission (index + 1)).snapshot =
      Physical.next (Physical.receive (publicVisit nature admission index).snapshot (.primitive request)) := by
  have actual := every_public_visit_is_the_same_original_activated_frame nature admission chosen index
  have emitted := every_actual_trial_primitive_is_consumed_with_its_literal_next nature
    (publicVisit nature admission index) (boundaryTick nature (index + 1)) actual request
    (the_visit_selects_its_actual_source_input nature admission index _ source)
    (every_public_visit_is_ready_at_its_original_raw_boundary nature admission index)
  exact (the_generated_drain_keeps_the_actual_body_and_complete_account_run
    (publicVisit nature admission index).next).1.trans emitted.2.1

theorem the_actual_code_visit_has_its_same_next_source_cursor
    (word : RawEvent Party Good Bool Nat Unit)
    (source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (publicVisit nature admission index).snapshot.past) = .code ⟨word⟩) :
    (publicVisit nature admission (index + 1)).snapshot =
      Physical.next (Physical.receive (publicVisit nature admission index).snapshot (.code ⟨word⟩)) := by
  have actual := every_public_visit_is_the_same_original_activated_frame nature admission chosen index
  have emitted := every_actual_trial_code_is_consumed_with_its_literal_next nature
    (publicVisit nature admission index) (boundaryTick nature (index + 1)) actual word
    (the_visit_selects_its_actual_source_input nature admission index _ source)
    (every_public_visit_is_ready_at_its_original_raw_boundary nature admission index)
  exact (the_generated_drain_keeps_the_actual_body_and_complete_account_run
    (publicVisit nature admission index).next).1.trans emitted.1

theorem the_actual_guarded_work_visit_has_its_same_next_source_cursor
    (word : RawEvent Party Good Bool Nat Unit)
    (source : selected nature ((firstOrigin nature).germ.snapshot.past ++
      (publicVisit nature admission index).snapshot.past) = .execute word)
    (checked : Macro.Public.Scope.Checks input 0 count 0 0 (firstOrigin nature).germ.snapshot.past
      (publicVisit nature admission index).snapshot (PublicPlan.executable word)) :
    (publicVisit nature admission (index + 1)).snapshot =
      Physical.next (Physical.receive (publicVisit nature admission index).snapshot (.execute word)) := by
  have actual := every_public_visit_is_the_same_original_activated_frame nature admission chosen index
  have emitted := every_actual_trial_period_passes_the_original_scope_before_its_literal_next nature
    (publicVisit nature admission index) (boundaryTick nature (index + 1)) actual word
    (the_visit_selects_its_actual_source_input nature admission index _ source) checked
    (every_public_visit_is_ready_at_its_original_raw_boundary nature admission index)
  exact (the_generated_drain_keeps_the_actual_body_and_complete_account_run
    (publicVisit nature admission index).next).1.trans emitted.1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

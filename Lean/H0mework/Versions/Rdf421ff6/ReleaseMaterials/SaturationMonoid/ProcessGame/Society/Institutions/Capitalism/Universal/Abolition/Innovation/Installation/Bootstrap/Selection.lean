import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Bootstrap.Clock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.PublicVisits
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Readback

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open Functions.Revision

noncomputable section

theorem the_first_completed_prefix_is_the_original_mandatory_opcode (nature : RequestAt) :
    (firstRaw nature).germ.snapshot.past =
      [Mandatory.executionRaw (review := none) input 0 count 0 0 Physical.initial
        (.primitive Control.Scenario.ownerPresent)] := by
  rw [(the_first_raw_cut_keeps_the_original_reader_and_physical_prefix nature).2.1]
  rfl

theorem the_original_first_prefix_has_no_unperformed_public_execution (nature : RequestAt) :
    ∀ raw ∈ (firstRaw nature).germ.snapshot.past, beforePublic raw = true := by
  rw [the_first_completed_prefix_is_the_original_mandatory_opcode]
  intro raw member
  obtain rfl := List.mem_singleton.mp member
  rcases the_initial_opcode_is_an_advance_or_the_original_primitive with advance | primitive
  · rw [advance]; rfl
  · rw [primitive]; rfl

theorem the_first_raw_proposal_is_the_original_common_word (nature : RequestAt) :
    (firstRaw nature).germ.raw = .execute Control.Scenario.commonWork := by
  rw [(the_first_raw_cut_keeps_the_original_reader_and_physical_prefix nature).2.2]
  exact the_empty_actual_public_suffix_selects_only_common_work nature _
    (a_prefix_without_a_public_execution_has_no_public_suffix _
      (the_original_first_prefix_has_no_unperformed_public_execution nature))

theorem the_first_review_source_snapshot_is_the_literal_received_germ (nature : RequestAt) :
    InitialAdmission.sourceSnapshot (firstOrigin nature) =
      Physical.receive (firstRaw nature).germ.snapshot (firstRaw nature).germ.raw := by
  unfold InitialAdmission.sourceSnapshot firstOrigin Macro.Runtime.Frame.controlOrigin Enactment.Inquiry.contextAt
  rfl

theorem the_first_review_has_its_actual_whole_scope_common_candidate (nature : RequestAt) :
    PublicPlan.Checks input 0 count 0 0 (InitialAdmission.sourceSnapshot (firstOrigin nature))
      Control.Scenario.commonWork :=
  the_actual_first_source_pays_the_whole_public_scope _
    (the_first_actual_raw_is_in_its_actual_source_inventory nature)

private theorem candidates_at_a_seeking_common_source (snapshot : CursorAt)
    (raw : snapshot.incoming = .execute Control.Scenario.commonWork)
    (phase : (PublicPlan.oldCurrent input 0 count 0 0 snapshot).phase = .seeking)
    (round : (PublicPlan.oldCurrent input 0 count 0 0 snapshot).raw.round = 2) :
    PublicPlan.candidates input 0 count 0 0 snapshot =
      [Control.Scenario.commonWork,Control.Scenario.commonWork,[]] := by
  have word : ProgrammeSource.wordAt input (PublicPlan.oldCurrent input 0 count 0 0 snapshot).raw =
      Control.Scenario.commonWork := by
    change (if (PublicPlan.oldCurrent input 0 count 0 0 snapshot).raw.round = 1
      then Control.Scenario.capitalWord else Control.Scenario.commonWork) = _
    rw [round]
    rfl
  unfold PublicPlan.candidates PublicPlan.currentWord
  rw [raw, phase, word]
  rfl

theorem the_first_actual_candidate_domain_has_no_trial_or_target (nature : RequestAt) :
    PublicPlan.candidates input 0 count 0 0 (InitialAdmission.sourceSnapshot (firstOrigin nature)) =
      [Control.Scenario.commonWork,Control.Scenario.commonWork,[]] := by
  rw [the_first_review_source_snapshot_is_the_literal_received_germ]
  exact candidates_at_a_seeking_common_source _ (the_first_raw_proposal_is_the_original_common_word nature)
    (the_first_actual_admission_reads_the_seeking_source nature)
    (the_first_actual_scope_still_reads_the_original_round nature)

theorem no_initial_admission_can_relabel_the_old_seeking_current_as_paid_renewal
    (nature : RequestAt) (ready : Trigger.ReadyAt (firstOrigin nature)) : False := by
  have phase := ready.scope.phase
  have seeking := the_first_actual_admission_reads_the_seeking_source nature
  change (Physical.stateAt input 0 count 0 0 (firstRaw nature).germ.snapshot.past).phase =
    .renewal ready.scope.word at phase
  cases seeking.symm.trans phase

theorem the_original_first_scope_cannot_be_paid_by_an_empty_word (nature : RequestAt) :
    ¬ PublicPlan.Checks input 0 count 0 0 (InitialAdmission.sourceSnapshot (firstOrigin nature)) [] := by
  intro checked
  have original : (0 : Party) ∈ Actual.members input 0 count := by
    rw [the_original_member_inventory_is_generated_before_the_trial]
    simp
  have present : (0 : Party) ∈ Epoch.Interface.Actors.Census.parties input 0 count 0 0
      (Physical.Prefix.cursor (firstRaw nature).germ.snapshot.past) :=
    List.mem_dedup.mpr (List.mem_append_left _ original)
  have scope := PublicPlan.every_actual_member_is_checked input 0 count 0 0
    (InitialAdmission.sourceSnapshot (firstOrigin nature)) [] 0 present
  have paid := (checked.2.2.2.1 0 scope).1
  rcases paid with empty | ⟨item, member, _⟩
  · cases empty
  · cases member

theorem every_first_public_plan_is_the_original_common_word
    (nature : RequestAt) (plan : InitialAdmission.PublicPlanAt (firstOrigin nature)) :
    plan.rawWord = Control.Scenario.commonWork := by
  have member := plan.generated
  rw [the_first_actual_candidate_domain_has_no_trial_or_target nature] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | empty
  · exact same
  · exact same
  · exact False.elim (the_original_first_scope_cannot_be_paid_by_an_empty_word nature
      (by simpa only [empty] using plan.checked))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

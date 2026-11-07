import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.Code
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Transition.Past

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section

theorem no_review_is_preinstalled : current.control.review = none := by rw [source_control];rfl

def afterCode := Transition.next current original_complete

theorem the_original_root_really_installs_its_new_finite_programme :
    afterCode.control = ⟨.seeking,submission.requests,none⟩ ∧ afterCode.raw = current.raw :=
  current.the_actual_code_successor_reads_the_new_programme submission
    the_original_source_submits_code_at_this_actual_cut no_review_is_preinstalled
    the_actual_public_source_admits_the_new_code original_complete

theorem the_next_source_compiler_reads_the_new_remaining_code : afterCode.state.remaining = submission.requests :=
  congrArg Control.remaining the_original_root_really_installs_its_new_finite_programme.1

theorem afterCode_ready : ¬ Public.Inquiry.HasWork afterCode.native.frame afterCode.native.actual.actual :=
  current.the_actual_code_registration_is_ready_for_its_own_next_query submission
    the_original_source_submits_code_at_this_actual_cut no_review_is_preinstalled
    the_actual_public_source_admits_the_new_code original_complete

theorem the_next_input_comes_from_the_actual_grown_past : afterCode.proposal = .advance := by
  change (if afterCode.native.actual.readerCursor.past.length = cutLength then _ else _) = _
  apply if_neg
  have grown := Transition.next_reader_length current original_complete
  have before : current.native.actual.readerCursor.past.length = cutLength := rfl
  have afterLength : afterCode.native.actual.readerCursor.past.length = cutLength + 1 :=
    grown.trans (congrArg (fun n => n+1) before)
  intro same
  exact Nat.succ_ne_self cutLength (afterLength.symm.trans same)

theorem the_new_epoch_is_the_same_actual_root_action_and_keeps_every_old_row : Current.ClosedAt current :=
  current.the_source_generates_its_whole_ledger_actual_epoch

theorem the_new_phase_is_consumed_by_the_next_actual_unit_programme : Current.ClosedAt afterCode :=
  afterCode.the_source_generates_its_whole_ledger_actual_epoch

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers

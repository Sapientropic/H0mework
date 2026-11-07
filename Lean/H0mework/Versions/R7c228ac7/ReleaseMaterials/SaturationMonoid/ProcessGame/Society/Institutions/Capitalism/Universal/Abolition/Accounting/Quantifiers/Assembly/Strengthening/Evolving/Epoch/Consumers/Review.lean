import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Boundary
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.Review
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
attribute [local irreducible] Evolution.Ingress.Joint.Execution.Selected.items Evolution.Ingress.Joint.Execution.Selected.after
  Quantifiers.Joint.Planning.selected Quantifiers.Joint.Planning.actualNext

def reviewFee : Request Bool Bool Bool Unit Unit := ⟨false,[true],false,[],.use false [(false,1)] .external⟩
def reviewCode : ReviewSource.Control.Code Bool Bool Bool Unit Unit := ⟨reviewFee,[repair]⟩
def reviewStart := current.requery (fun _ _ => .review reviewCode)

theorem review_control_source : reviewStart.control = current.control :=
  (current.requery_keeps_control_and_complete_account _).1

theorem review_none : reviewStart.control.review = none := by rw [review_control_source,source_control];rfl

theorem review_admitted : boundary (Public.Scope.checkInput reviewStart.native.input)
    (Actual.origin reviewStart.native.input reviewStart.native.depth reviewStart.native.count) reviewStart.members reviewStart.native.depth
    reviewStart.native.count reviewStart.native.prefixLimit reviewStart.native.renewalLimit reviewStart.state := by
  unfold Current.state
  rw [review_control_source]
  exact the_actual_public_source_admits_the_new_code

theorem review_complete : ¬ Public.Inquiry.HasWork reviewStart.native.frame reviewStart.native.actual.actual := original_complete

def afterReview := Transition.next reviewStart review_complete

theorem review_written : afterReview.control =
    {reviewStart.control with review := some (ReviewCursor.initial reviewCode reviewStart.native.prefixLimit reviewStart.native.renewalLimit)} :=
  (Transition.next_reads_the_written_control _ _).trans
    (reviewStart.review_installs_only_the_original_finite_code reviewCode rfl review_none review_admitted)

theorem registration_creates_no_free_fee_payment :
    afterReview.raw = reviewStart.raw ∧ (ReviewCursor.initial reviewCode 0 0).feePaid = false := by
  constructor
  · apply (Transition.next_state_reads_the_same_actual_material_target reviewStart review_complete).trans
    rw [Current.physicalResult,reviewStart.review_execution_is_the_original_registration reviewCode rfl review_none review_admitted]
    rfl
  · rfl

theorem afterReview_ready : ¬ Public.Inquiry.HasWork afterReview.native.frame afterReview.native.actual.actual :=
  reviewStart.the_actual_review_registration_is_ready_for_its_own_next_query reviewCode rfl review_none review_admitted review_complete

theorem the_next_live_query_uses_the_registered_fee_without_private_consent :
    afterReview.executionRaw = .primitive (reviewFee.resign reviewFee.signer) := by
  unfold Current.executionRaw Current.choice
  rw [review_written]
  rfl

theorem review_and_its_fee_attempt_use_the_actual_root_and_all_old_rows : Current.ClosedAt afterReview :=
  afterReview.the_source_generates_its_whole_ledger_actual_epoch

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers

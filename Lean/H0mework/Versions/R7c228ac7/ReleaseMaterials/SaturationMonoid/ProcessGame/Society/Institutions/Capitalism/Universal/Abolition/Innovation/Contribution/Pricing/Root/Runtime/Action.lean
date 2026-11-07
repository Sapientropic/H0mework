import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Request
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Abolition.Accounting.Quantifiers.Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)

def afterBody := (queued source request).advance

theorem the_selected_request_keeps_the_original_scope_route (available : ReviewAvailable source) :
    (queued source request).physicalResult.execution =
        (Physical.Public.compile source.native.input (Evolving.Epoch.Source.originalState source.native) (.primitive request)).execution ∧
      (queued source request).physicalResult.next =
        (Physical.Public.compile source.native.input (Evolving.Epoch.Source.originalState source.native) (.primitive request)).next ∧
      (queued source request).physicalResult.isAccepted =
        (Physical.Public.compile source.native.input (Evolving.Epoch.Source.originalState source.native) (.primitive request)).isAccepted := by
  unfold Evolving.Epoch.Current.physicalResult
  rw [the_available_review_forwards_the_actual_requested_primitive source request available]
  unfold Public.Scope.actualResult Public.Scope.selectedCursor
  rw [(Public.Scope.every_nonperiod_proposal_keeps_its_actual_route _ _ _ _ _ _ _ (.primitive request) rfl).1]
  exact ⟨rfl,rfl,rfl⟩

theorem the_original_root_executes_the_generated_request
    (ready : Ready source) (available : ReviewAvailable source) (noConsents : request.consents = [])
    (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request) :
    (afterBody source request).raw = (Physical.Public.interpreter source.native.input).step source.raw request ∧
      (queued source request).physicalResult.execution.items = [⟨0,source.raw,request⟩] ∧
      (queued source request).physicalResult.isAccepted = true := by
  have actual := Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.one_checked_original_primitive_has_one_actual_material_step
    source.native.input (Evolving.Epoch.Source.originalState source.native) request noConsents valid
  have complete : ¬ Public.Inquiry.HasWork (queued source request).native.frame
      (queued source request).native.actual.actual := ready
  have raw := Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target (queued source request) complete
  rw [← Evolving.Epoch.Current.advance_eq_epoch (queued source request) complete] at raw
  have routed := the_selected_request_keeps_the_original_scope_route source request available
  have rawTarget := congrArg (fun value => value.raw) routed.2.1
  refine ⟨raw.trans (rawTarget.trans (congrArg (fun value => value.raw) actual.2.2)),?_,?_⟩
  · rw [routed.1]
    exact actual.2.1
  · exact routed.2.2.trans actual.1

theorem the_primitive_preserves_the_original_review_coordinate (available : ReviewAvailable source) :
    (queued source request).afterControl.review = source.control.review := by
  unfold Evolving.Epoch.Current.afterControl Evolving.Epoch.Current.choice
  rw [queued_selects_the_same_source_request, (queued_keeps_the_original_control_and_complete_account source request).1]
  unfold Evolving.Epoch.select
  split
  · rfl
  · rename_i cursor observed
    have permission : cursor.recourse = true := by simpa only [ReviewAvailable,observed] using available
    rw [if_pos permission]
    rfl

theorem afterBody_keeps_the_original_review_coordinate (ready : Ready source) (available : ReviewAvailable source) :
    (afterBody source request).control.review = source.control.review := by
  have complete : ¬ Public.Inquiry.HasWork (queued source request).native.frame
      (queued source request).native.actual.actual := ready
  have written := Evolving.Epoch.Transition.next_reads_the_written_control (queued source request) complete
  rw [← Evolving.Epoch.Current.advance_eq_epoch (queued source request) complete] at written
  exact (congrArg (fun control => control.review) written).trans
    (the_primitive_preserves_the_original_review_coordinate source request available)

theorem the_actual_body_is_the_same_root_answer_and_generated_next :
    (afterBody source request).inquiry.erase =
      (RootInquiryProcessNode.answered (queued source request).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (queued source request).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (afterBody source request).inquiry) :=
  (queued source request).advance_is_the_actual_root_successor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

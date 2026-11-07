import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)

def queued := source.requery (fun _ _ => .primitive request)

def Ready : Prop := ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual

def ReviewAvailable : Prop :=
  match source.control.review with
  | none => True
  | some cursor => cursor.recourse = true

instance : Decidable (Ready source) := by unfold Ready; infer_instance
instance : Decidable (ReviewAvailable source) := by unfold ReviewAvailable; split <;> infer_instance

theorem queued_keeps_the_original_control_and_complete_account :
    (queued source request).control = source.control ∧
      (queued source request).native.actual.actual.account = source.native.actual.actual.account :=
  source.requery_keeps_control_and_complete_account _

theorem queued_keeps_the_original_raw_and_census :
    (queued source request).raw = source.raw ∧ (queued source request).members = source.members := ⟨rfl,rfl⟩

theorem queued_selects_the_same_source_request :
    (queued source request).proposal = .primitive request := rfl

theorem queued_is_ready_iff : Ready (queued source request) ↔ Ready source := Iff.rfl

theorem the_available_review_forwards_the_actual_requested_primitive
    (available : ReviewAvailable source) :
    (queued source request).executionRaw = .primitive request := by
  unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
  rw [queued_selects_the_same_source_request, (queued_keeps_the_original_control_and_complete_account source request).1]
  unfold Evolving.Epoch.select
  split
  · rfl
  · rename_i cursor observed
    have permission : cursor.recourse = true := by simpa only [ReviewAvailable,observed] using available
    rw [if_pos permission]
    rfl

theorem each_queued_request_is_an_actual_whole_ledger_root_step :
    Evolving.Epoch.Current.ClosedAt (queued source request) :=
  (queued source request).the_source_generates_its_whole_ledger_actual_epoch

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

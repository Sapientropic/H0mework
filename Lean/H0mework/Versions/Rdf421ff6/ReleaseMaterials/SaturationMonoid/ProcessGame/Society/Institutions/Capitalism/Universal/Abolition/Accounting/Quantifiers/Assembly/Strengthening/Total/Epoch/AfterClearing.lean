import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Deployment

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {fallback : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count fallback) (binding : Evolving.Epoch.Binding source.native)
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

structure ActualEpochAfterClearingAt : Prop where
  actual_clearing : Clearing.Deployment.CompleteAt source resources
  same_native_current : (Evolving.Epoch.AfterNative.resume source binding resources).native =
    Clearing.Deployment.completed source resources
  same_source_control : (Evolving.Epoch.AfterNative.resume source binding resources).control = binding.value
  same_root_occurrence : (Evolving.Epoch.AfterNative.resume source binding resources).inquiry.erase =
    (Clearing.Deployment.completed source resources).erase
  actual_next_epoch : Evolving.Epoch.Current.ClosedAt (Evolving.Epoch.AfterNative.resume source binding resources)

theorem the_original_whole_clearing_resumes_its_same_actual_legal_epoch :
    ActualEpochAfterClearingAt source binding resources where
  actual_clearing := Clearing.Deployment.the_original_current_clears_its_entire_native_ledger_and_continues source resources
  same_native_current := Evolving.Epoch.AfterNative.resume_is_the_literal_completed_native_current source binding resources
  same_source_control := Evolving.Epoch.AfterNative.resume_reads_the_original_source_control source binding resources
  same_root_occurrence := Evolving.Epoch.AfterNative.resume_uses_the_same_completed_root_occurrence source binding resources
  actual_next_epoch := Evolving.Epoch.AfterNative.the_restored_epoch_programme_actually_reads_the_live_control_and_advances
    source binding resources

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Schedule
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {fallback : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count fallback) (binding : Binding source.native)
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

def installed : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ({native := source.native,binding := binding} : Current).requery (Clearing.Deployment.reader source)

def resume := run (Clearing.Deployment.plan source) (Clearing.Deployment.schedule source resources) (installed source binding).binding

theorem resume_is_the_literal_completed_native_current :
    (resume source binding resources).native = Clearing.Deployment.completed source resources :=
  run_native _ _ _

theorem resume_reads_the_original_source_control :
    (resume source binding resources).control = binding.value :=
  run_control _ _ _

theorem resume_uses_the_same_completed_root_occurrence :
    (resume source binding resources).inquiry.erase = (Clearing.Deployment.completed source resources).erase :=
  congrArg NativeCurrent.erase (resume_is_the_literal_completed_native_current source binding resources)

theorem the_restored_epoch_programme_actually_reads_the_live_control_and_advances :
    Current.ClosedAt (resume source binding resources) :=
  (resume source binding resources).the_source_generates_its_whole_ledger_actual_epoch

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative

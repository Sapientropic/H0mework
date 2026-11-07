import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Run
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.RootFace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {oldReader : Macro.Raw.Reader input depth count}
  (source : Position input depth count oldReader)
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (history source) (before source))

def completedPosition : Position input depth count (reader source) := Schedule.run (plan source) (schedule source resources)
abbrev completed := (completedPosition source resources).native

theorem the_whole_clearing_is_the_original_selected_root_history :
    completed source resources = Evolving.History.currentAt (position source).native (2 * (plan source).length) :=
  Schedule.run_is_the_same_finite_actual_root_history _ (schedule source resources)
    (Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.the_complete_source_word_is_a_nonnegative_payment_inventory
      input depth count (Physical.Public.interpreter input) (before source))

theorem the_whole_clearing_has_the_same_original_native_account :
    (completedPosition source resources).actual.actual.account =
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.nextAccount
        input depth count (history source) (before source) :=
  Schedule.run_keeps_the_same_actual_original_native_fold _ (schedule source resources)

theorem the_whole_clearing_has_the_same_original_actual_past :
    (completedPosition source resources).past =
      Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.nextHistory
        input depth count (history source) (before source) :=
  Schedule.run_keeps_the_same_actual_submitted_past _ (schedule source resources)

theorem the_original_reader_is_selected_after_the_finite_plan :
    (completedPosition source resources).actual.proposal (reader source) =
      oldReader (completedPosition source resources).actual.readerCursor
        (completedPosition source resources).actual.actual.account := by
  apply exhaustion_returns_the_same_actual_open_reader
  change (history source).length + (plan source).length ≤ (completedPosition source resources).past.length
  have generated := congrArg List.length (Schedule.run_keeps_the_same_actual_submitted_past _ (schedule source resources))
  change (completedPosition source resources).past.length =
    ((history source) ++ Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.submitted (plan source)).length at generated
  simpa only [Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.submitted,
    List.length_append,List.length_map] using Nat.le_of_eq generated.symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment

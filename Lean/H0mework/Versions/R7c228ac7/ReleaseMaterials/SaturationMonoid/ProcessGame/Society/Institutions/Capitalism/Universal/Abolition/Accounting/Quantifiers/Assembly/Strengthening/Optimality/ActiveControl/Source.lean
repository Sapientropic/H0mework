import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.CommonPast
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Readings
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader) (binding : Evolving.Epoch.Binding source.native)

/-- Install a new observer code while retaining the existing root's live
binding. No bootstrap state replaces an already registered programme. -/
def rival (policy : Macro.Raw.Reader input depth count) :=
  ({native := source.native,binding := binding} : Evolving.Epoch.Current).requery policy

theorem every_policy_keeps_the_original_physical_cut (policy : Macro.Raw.Reader input depth count) :
    Evolving.Epoch.Source.originalState (rival source binding policy).native = Cost.Canonical.before source := by
  change Public.Scope.actualState input depth count 0 0 [] source.actual.snapshot = _
  exact Clearing.Position.raw_state_is_read_from_its_actual_past source

theorem every_policy_keeps_the_actual_input_control_and_complete_account
    (policy : Macro.Raw.Reader input depth count) :
    (rival source binding policy).native.input = input ∧
      (rival source binding policy).control = binding.value ∧
      (rival source binding policy).native.actual.actual.account = source.actual.actual.account := by
  refine ⟨rfl,?_,rfl⟩
  exact (({native := source.native,binding := binding} : Evolving.Epoch.Current).requery_keeps_control_and_complete_account policy).1.trans
    (Evolving.Epoch.Current.control_is_the_actual_root_coordinate _)

def actualCost (policy : Macro.Raw.Reader input depth count) (n : Nat)
    (reading : Cost.LinearReadout Party Good) : ℚ :=
  Cost.value reading input (Cost.Canonical.before source) (Programme.Epoch.programme (rival source binding policy) n)

theorem the_competing_cost_is_the_actual_report_inventory_and_clock
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    actualCost source binding policy n reading =
      ((Programme.Epoch.inventory (rival source binding policy) n).map
        (Cost.itemValue reading (Physical.Public.interpreter input))).sum +
      reading.timeWeight * ((Evolving.Epoch.History.currentAt (rival source binding policy) n).raw.clock -
        (rival source binding policy).raw.clock) := by
  unfold actualCost Cost.value
  rw [← every_policy_keeps_the_original_physical_cut source binding policy]
  have ownInput : (rival source binding policy).native.input = input := rfl
  have actualItems := Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory (rival source binding policy) n
  have actualClock := Programme.Epoch.the_cost_clock_is_the_actual_epoch_clock_difference (rival source binding policy) n
  rw [ownInput] at actualItems actualClock
  rw [actualItems,actualClock]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl

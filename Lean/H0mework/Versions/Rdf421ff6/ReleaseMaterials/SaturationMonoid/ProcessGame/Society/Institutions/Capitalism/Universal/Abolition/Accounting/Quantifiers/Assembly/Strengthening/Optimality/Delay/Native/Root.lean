import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Abolition.Completion.Actual.Dividend
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {oldReader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count oldReader)
  (resources : ArchiveNative.Conditions input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

/-- Each term uses its own actual native item's interpreter and instruction. -/
def actualNativeIncome : Profit.Vector (Party := Party) (Good := Good) :=
  ((Primitive.events input depth count (Clearing.Deployment.history source) (Clearing.Deployment.plan source)).map fun item =>
    Financial.fullChange (item.interpreter input depth count) (item.instruction input depth count).before
      (item.instruction input depth count).request).sum

include resources in
theorem every_actual_native_retirement_keeps_cash_and_the_same_old_asset_together :
    actualNativeIncome source = 0 := by
  unfold actualNativeIncome
  apply List.sum_eq_zero
  intro value original
  obtain ⟨item,listed,rfl⟩ := List.mem_map.mp original
  have actual := Primitive.primitive_resources_generate_the_same_requested_word_and_actual_native_inventory
    input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source) resources
  have requestListed : (item.instruction input depth count).request ∈
      (Primitive.events input depth count (Clearing.Deployment.history source) (Clearing.Deployment.plan source)).map
        (fun item => (item.instruction input depth count).request) := List.mem_map.mpr ⟨item,listed,rfl⟩
  change (item.instruction input depth count).request ∈
    (Primitive.events input depth count (Clearing.Deployment.history source)
      (Primitive.word input depth count (Clearing.Deployment.before source))).map _ at requestListed
  rw [actual.1] at requestListed
  obtain ⟨instrument,debtor,holder,quantity,operation,_⟩ :=
    the_complete_source_word_is_a_nonnegative_payment_inventory input depth count _
      (Clearing.Deployment.before source) _ requestListed
  exact Financial.settlement_is_neutral_for_every_original_bearer
    (item.interpreter input depth count) (item.instruction input depth count).before
    (item.instruction input depth count).request instrument debtor holder quantity operation

theorem the_actual_root_clears_all_original_debts_without_financial_timing_income :
    Clearing.Deployment.CompleteAt source resources ∧
      ∀ (members : Party → Bool) good, Coalition.read members good (actualNativeIncome source) = 0 := by
  refine ⟨Clearing.Deployment.the_original_current_clears_its_entire_native_ledger_and_continues source resources,?_⟩
  intro members good
  rw [every_actual_native_retirement_keeps_cash_and_the_same_old_asset_together source resources,map_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native

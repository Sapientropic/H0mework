import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Settlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Realization
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Deployment.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader)

def before := Physical.Public.stateAt input depth count 0 0 [] source.past
def programme := (Clearing.Deployment.plan source).map Compile.RawInput.primitive

theorem every_chosen_operation_comes_from_the_original_settlement_ledger
    (request : Request Party Good Port Technology Instrument) (listed : request ∈ Clearing.Deployment.plan source) :
    ∃ instrument debtor holder quantity, request.operation = .settle instrument debtor holder quantity := by
  obtain ⟨instrument,debtor,holder,quantity,kind,nonnegative⟩ :=
    Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.the_complete_source_word_is_a_nonnegative_payment_inventory
      input depth count (Physical.Public.interpreter input) (Clearing.Deployment.before source) request listed
  exact ⟨instrument,debtor,holder,quantity,kind⟩

theorem the_original_source_plan_has_zero_additional_resource_cost
    (channel : Channel) (party : Party) (good : Good) :
    resource input (before source) (programme source) channel party good = 0 :=
  all_source_settlement_programmes_have_zero_resource_cost input (before source) (Clearing.Deployment.plan source)
    (every_chosen_operation_comes_from_the_original_settlement_ledger source) channel party good

theorem the_original_source_plan_has_zero_actual_elapsed_cost :
    Programme.clockCost input (before source) (programme source) = 0 :=
  Programme.pure_microsteps_have_zero_elapsed_cost input (before source) (Clearing.Deployment.plan source)

/-- The comparison quantifier is all source syntax, even a strict superset
of admitted clearing alternatives. No canonical-menu coverage is assumed. -/
theorem no_alternative_programme_has_less_real_resource_or_time_cost
    (rival : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (channel : Channel) (party : Party) (good : Good) :
    resource input (before source) (programme source) channel party good ≤ resource input (before source) rival channel party good ∧
      Programme.clockCost input (before source) (programme source) ≤ Programme.clockCost input (before source) rival := by
  rw [the_original_source_plan_has_zero_additional_resource_cost,the_original_source_plan_has_zero_actual_elapsed_cost]
  exact ⟨all_programmes_have_nonnegative_real_resource_costs input _ rival channel party good,
    Programme.clockCost_nonnegative input _ rival⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Consumers.Example
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Pricing

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Novel

open Source.Program
open Example (Party Good)

abbrev mechanism := Example.mechanism 12 1
def actualNewEvent : mechanism.Nature := Example.shock 2
def actuallyProductive : Bool := match mechanism.generate actualNewEvent with
  | .accepted _ => true | _ => false
def actuallyUnpriced : Bool := match mechanism.pricingStatus actualNewEvent with
  | .unpriced _ => true | _ => false

theorem an_unlisted_technology_really_executes_and_is_locally_learned :
    actuallyProductive = true ∧ actuallyUnpriced = true ∧
      (mechanism.after actualNewEvent).technology = 2 ∧ mechanism.paidSignal actualNewEvent = some 1 ∧
      mechanism.proposal actualNewEvent = Example.work ∧
      (mechanism.after actualNewEvent).stock 0 .material = 13 ∧
      (mechanism.after actualNewEvent).claims () 0 1 = 5 := by
  decide +kernel

theorem the_unlisted_actual_event_keeps_every_persons_life_and_maintenance_budget :
    Safety.Safe mechanism actualNewEvent ∧
      Exit.Necessity.AllNeedsPaid mechanism.code.law mechanism.code.initial mechanism.code.parties
        (mechanism.word actualNewEvent) := by
  decide +kernel

def actualBudgetShock : mechanism.Nature := Example.request 0 (.use 0 [(.life, 2)] .external)
def budgetFailureVisible : Bool := match mechanism.generate actualBudgetShock with
  | .failed (.budgetViolation _) => true | _ => false

theorem an_unquoted_actual_disaster_keeps_its_exact_unpaid_life_residual :
    budgetFailureVisible = true ∧ (mechanism.after actualBudgetShock).stock 0 .life = 0 ∧
      mechanism.investmentLoss 0 .material = 3 ∧ (mechanism.after actualBudgetShock).claims () 0 1 = 5 := by
  decide +kernel

#print axioms an_unlisted_technology_really_executes_and_is_locally_learned
#print axioms the_unlisted_actual_event_keeps_every_persons_life_and_maintenance_budget
#print axioms an_unquoted_actual_disaster_keeps_its_exact_unpaid_life_residual

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Novel

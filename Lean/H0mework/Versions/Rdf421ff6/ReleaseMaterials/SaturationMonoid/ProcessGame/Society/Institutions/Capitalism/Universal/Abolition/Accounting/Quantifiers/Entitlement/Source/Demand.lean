import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Grant

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

open Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- Gross custody/reconciliation demand. The original financial claims are
not subtracted or retired by this read. Actual clearing must do that work. -/
structure Demand where
  private mk ::
  leg : window.Leg
  controlled : ControlledReturn leg
  noExercisedGrant : ¬ Nonempty (ExercisedGrant window leg)
  originalBasis : Classification window leg

def readDemand (leg : window.Leg) : Option (Demand window) := by
  letI : Decidable (ControlledReturn (law := window.input.law) (before := window.before) (word := window.word) leg) :=
    instDecidableControlledReturn (law := window.input.law) (before := window.before) (word := window.word) leg
  exact if controlled : ControlledReturn leg then
    some ⟨leg,controlled,an_unconsented_control_return_has_no_exercised_financial_grant window leg controlled,
      classify window leg⟩
  else none

def demands : List (Demand window) := window.legs.filterMap (readDemand window)

namespace Demand
variable {window} (demand : Demand window)

def quantity : ℚ := demand.leg.quantity
def key : Nat × Good := (demand.leg.item.val.index,demand.leg.good)

theorem quantity_is_the_original_victim_debit :
    demand.quantity = flowAt (window.input.law.actualDebit demand.leg.item.val.before demand.leg.item.val.request)
      demand.leg.sender demand.leg.good := demand.leg.original_debit_and_credit.1.symm

theorem quantity_is_the_original_recipient_credit :
    demand.quantity = flowAt (window.input.law.actualCredit demand.leg.item.val.before demand.leg.item.val.request)
      demand.leg.recipient demand.leg.good := demand.leg.original_debit_and_credit.2.symm

theorem the_source_quantity_has_a_real_original_bearer :
    0 < demand.quantity ∧
    (window.input.law.step demand.leg.item.val.before demand.leg.item.val.request).stock
        demand.leg.sender demand.leg.good = demand.leg.item.val.before.stock demand.leg.sender demand.leg.good - demand.quantity :=
  ⟨demand.leg.quantity_positive,demand.leg.the_original_victim_and_recipient_have_opposite_actual_stock_changes.1⟩

end Demand

structure Claim : Type where
  private mk ::
  accounted : window.Accounted
  nonempty : demands window ≠ []

def assess : Option (Claim window) :=
  if accounted : window.Accounted then
    if actual : demands window ≠ [] then some ⟨accounted,actual⟩ else none
  else none

theorem a_claim_does_not_take_a_caller_quantity (claim : Claim window) :
    ∃ demand ∈ demands window, 0 < demand.quantity := by
  cases original : demands window with
  | nil => exact (claim.nonempty original).elim
  | cons first rest => exact ⟨first,List.mem_cons_self,first.the_source_quantity_has_a_real_original_bearer.1⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source

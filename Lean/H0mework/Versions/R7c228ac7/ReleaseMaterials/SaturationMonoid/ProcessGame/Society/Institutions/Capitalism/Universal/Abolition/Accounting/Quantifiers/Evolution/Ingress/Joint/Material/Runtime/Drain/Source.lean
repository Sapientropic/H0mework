import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.State
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Claims

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def budget : Nat := 1 + (Execution.Selected.items seed claim).length
def stateAt (steps : Nat) := (Runtime.next seed claim)^[steps] (Runtime.initial seed)
def completed := stateAt seed claim (budget seed claim)

theorem the_source_inventory_is_the_same_selected_occurrence :
    Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) =
      Execution.Selected.items seed claim := rfl

theorem no_original_position_requests_another_loan
    (item : Epoch.Finance.ActualItem seed.input seed.depth seed.count)
    (original : item ∈ Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)) :
    Epoch.Finance.readNewClaim seed.input seed.depth seed.count item = none := by
  rw [the_source_inventory_is_the_same_selected_occurrence] at original
  have absent := Execution.Selected.no_actual_financial_item_can_mint_a_new_loan seed claim item original
  cases operation : (item.instruction seed.input seed.depth seed.count).request.operation <;>
    simp_all [Execution.Selected.NotIssue,Epoch.Finance.readNewClaim]

theorem every_budget_has_the_original_body_step : 0 < budget seed claim := by
  unfold budget
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

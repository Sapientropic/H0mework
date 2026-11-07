import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Payment
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem an_actual_settlement_does_not_issue_another_claim
    (item : ActualItem input depth count) (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity) :
    readNewClaim input depth count item = none := by
  unfold readNewClaim
  split
  · rename_i observed
    cases operation.symm.trans observed
  · rfl

theorem the_actual_settlement_next_is_the_same_original_allocator
    (item : ActualItem input depth count) (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (state : (process input depth count).GeneratedState) (movement : Movement input depth count item)
    (parsed : readMovement input depth count item = some movement) :
    (consume input depth count item state).next input depth count =
      (allocate input depth count item movement state).after := by
  have absent := an_actual_settlement_does_not_issue_another_claim input depth count item instrument debtor holder quantity operation
  unfold consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i claim found
    cases absent.symm.trans found
  · rw [parsed]
    rfl

theorem the_original_consumer_pays_the_whole_funded_share
    (item : ActualItem input depth count) (instrument observed : Instrument) (debtor holder bearer creditor : Party)
    (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation = .settle instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request)
    (state : (process input depth count).GeneratedState)
    (funded : quantity ≤ ledgerClaims input depth count state.current instrument debtor holder) :
    ledgerClaims input depth count ((consume input depth count item state).next input depth count).current observed bearer creditor =
      ledgerClaims input depth count state.current observed bearer creditor +
        paymentDelta instrument debtor holder quantity observed bearer creditor ∧
    ((consume input depth count item state).next input depth count).current.slots.map (slotClaim input depth count) =
      state.current.slots.map (slotClaim input depth count) := by
  obtain ⟨movement,parsed,_,_,effect⟩ := one_actual_payment_clears_exactly_its_original_aggregate_share
    input depth count item instrument observed debtor holder bearer creditor quantity operation accepted state funded
  rw [the_actual_settlement_next_is_the_same_original_allocator input depth count item instrument debtor holder quantity operation accepted state movement parsed]
  exact ⟨effect,(allocate input depth count item movement state).original_claims⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

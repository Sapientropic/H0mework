import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument)
  (payer provider : Party) (instrument : Instrument) (purpose : Port) (net : ℚ)

local notation "paidWord" => [issue law payer provider instrument purpose net,
  settle law payer provider instrument purpose net]

variable (issued : law.Valid before (issue law payer provider instrument purpose net))
  (settled : law.Valid (afterIssue law payer provider instrument purpose net before)
    (settle law payer provider instrument purpose net))

include issued settled in
theorem a_paid_price_has_zero_complete_financial_delta :
    Financial.inventoryClaims law (law.rawItems before paidWord) = 0 := by
  ext ⟨code,oldDebtor,oldCreditor⟩
  rw [Financial.inventory_claims_are_the_original_financial_delta]
  have balance := law.execute_financial_balance before 0 paidWord code oldDebtor oldCreditor
  change (afterPayment law payer provider instrument purpose net before).claims code oldDebtor oldCreditor = _ at balance
  rw [actual_payment_retains_the_entire_original_claim_matrix law before payer provider instrument purpose net issued settled] at balance
  change law.totalFinancialDelta (law.execute before 0 paidWord).items code oldDebtor oldCreditor = 0
  linarith

include issued settled in
theorem a_paid_price_has_its_exact_original_full_account (person : Party) (good : Good) :
    Accounting.Profit.fullIncome law (law.rawItems before paidWord) (person,good) =
      (afterPayment law payer provider instrument purpose net before).stock person good - before.stock person good := by
  rw [Accounting.Profit.fullIncome, a_paid_price_has_zero_complete_financial_delta law before payer provider instrument purpose net issued settled,
    map_zero,add_zero,Financial.inventory_material_is_the_original_net_flow]
  have balance := law.execute_material_balance before 0 paidWord person good
  change (afterPayment law payer provider instrument purpose net before).stock person good + _ = _ at balance
  change law.totalCredit (law.execute before 0 paidWord).items person good -
    law.totalDebit (law.execute before 0 paidWord).items person good = _
  linarith

include issued settled in
theorem the_generated_price_enters_both_original_full_accounts
    (positive : 0 < law.settlementRate instrument) (different : payer ≠ provider) :
    Accounting.Profit.fullIncome law (law.rawItems before paidWord) (provider,law.settlementUnit instrument) = net ∧
      Accounting.Profit.fullIncome law (law.rawItems before paidWord) (payer,law.settlementUnit instrument) = -net := by
  have changed := actual_payment_pays_the_generated_signed_net law before payer provider instrument purpose net issued settled positive different
  rw [a_paid_price_has_its_exact_original_full_account law before payer provider instrument purpose net issued settled,
    a_paid_price_has_its_exact_original_full_account law before payer provider instrument purpose net issued settled,
    changed.1,changed.2]
  constructor <;> ring

include issued settled in
theorem every_other_original_full_account_has_zero_price_change
    (positive : 0 < law.settlementRate instrument) (person : Party) (good : Good)
    (outside : good ≠ law.settlementUnit instrument ∨ (person ≠ payer ∧ person ≠ provider)) :
    Accounting.Profit.fullIncome law (law.rawItems before paidWord) (person,good) = 0 := by
  rw [a_paid_price_has_its_exact_original_full_account law before payer provider instrument purpose net issued settled,
    every_other_original_material_coordinate_is_retained law before payer provider instrument purpose net issued settled positive person good outside,
    sub_self]

theorem original_raw_final_is_independent_of_the_inventory_index
    (word : RawEvent Party Good Port Technology Instrument) (first second : Nat) :
    (law.execute before first word).final = (law.execute before second word).final := by
  induction word generalizing before first second with
  | nil => rfl
  | cons request tail inherited => exact inherited (law.step before request) (first+1) (second+1)

theorem appended_price_uses_the_literal_original_body_endpoint
    (body : RawEvent Party Good Port Technology Instrument) :
    (law.execute before 0 (body ++ paidWord)).final =
      afterPayment law payer provider instrument purpose net (law.execute before 0 body).final := by
  rw [RawLaw.execute_append]
  change (law.execute (law.execute before 0 body).final (0+body.length) paidWord).final = _
  rw [original_raw_final_is_independent_of_the_inventory_index law _ paidWord (0+body.length) 0]
  rfl

theorem appended_price_keeps_every_original_body_inventory_item
    (body : RawEvent Party Good Port Technology Instrument) :
    (law.execute before 0 body).items.IsPrefix (law.execute before 0 (body ++ paidWord)).items := by
  rw [RawLaw.execute_append]
  exact List.prefix_append _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

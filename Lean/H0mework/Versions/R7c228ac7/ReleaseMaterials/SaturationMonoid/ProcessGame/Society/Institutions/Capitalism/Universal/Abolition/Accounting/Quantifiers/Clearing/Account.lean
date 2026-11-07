import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Read

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

open Source.Program
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (before : RawCurrent Party Good Technology Instrument) (controller victim : Party)
  (good : Good) (quantity : ℚ) (instrument : Instrument) (principal : ℚ)
  (resources : Resources law before controller victim good quantity instrument principal)

local notation "reader" => PublicFunction.physicalLaw law
local notation "returned" => refund law controller victim good quantity instrument
local notation "paid" => payment law controller victim instrument principal

include resources

theorem the_actual_payment_retires_only_the_original_claim :
    ((reader).next before (word law controller victim good quantity instrument principal)).claims =
      fun code debtor creditor => before.claims code debtor creditor -
        if (code,debtor,creditor) = (instrument,victim,controller) then principal else 0 := by
  change ((reader).step ((reader).step before returned) paid).claims = _
  rw [RawLaw.step,if_pos (primitive_resources_authorize_the_actual_old_claim_payment
    law before controller victim good quantity instrument principal resources)]
  change RawLaw.nextClaims ((reader).step before returned) paid = _
  simp only [RawLaw.nextClaims,payment]
  rw [the_return_preserves_the_entire_original_claim_matrix law before controller victim good quantity instrument principal resources]

omit resources [DecidableEq Instrument] in
private theorem income_as_actual_steps (interpreter : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    Profit.fullIncome interpreter items =
      (items.map fun item => Financial.fullChange interpreter item.before item.request).sum := by
  simp only [Profit.fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,
    Financial.fullChange,map_list_sum,List.map_map,Function.comp_def]
  rw [← List.sum_map_add]

theorem the_full_actual_clearing_income_is_exactly_the_material_return :
    Profit.fullIncome reader ((reader).rawItems before (word law controller victim good quantity instrument principal)) =
      Finsupp.single (victim,good) quantity - Finsupp.single (controller,good) quantity := by
  rw [income_as_actual_steps]
  simp only [RawLaw.rawItems,RawLaw.execute,word,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [Financial.settlement_is_neutral_for_every_original_bearer reader ((reader).step before returned) paid
    instrument victim controller principal rfl,add_zero]
  have accepted := primitive_resources_authorize_the_actual_return law before controller victim good quantity instrument principal resources
  simp only [Financial.fullChange,Financial.materialChange,Financial.claimChange,
    RawLaw.actualDebit,RawLaw.actualCredit,if_pos accepted]
  simp [Financial.rawClaimChange,Financial.flowVector,RawLaw.credit,RawLaw.debit,refund,locate]

/-- A payment of the finite old right cannot cancel the return in the full
account: its actual cash leg and its retired native position cancel instead. -/
theorem every_coalition_keeps_the_entire_return_in_its_full_account
    (members : Party → Bool) (unit : Good) :
    Coalition.read members unit
      (Profit.fullIncome reader ((reader).rawItems before (word law controller victim good quantity instrument principal))) =
        Coalition.read members unit
          (Finsupp.single (victim,good) quantity - Finsupp.single (controller,good) quantity) := by
  rw [the_full_actual_clearing_income_is_exactly_the_material_return law before controller victim good quantity instrument principal resources]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Clearing

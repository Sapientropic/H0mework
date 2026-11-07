import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Primitive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement.Accounting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

open Source.Program Abolition.Completion.Actual.Dividend
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : PhysicalCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (word : RawEvent Party Good Port Technology Instrument)
  (same : ∀ request ∈ word, request.resign request.signer = request)

local notation "law" => Physical.Public.interpreter input
local notation "submissions" => word.map Compile.RawInput.primitive

include same in
omit [DecidableEq Port] in
theorem original_primitive_reports_keep_the_complete_financial_change :
    Financial.inventoryClaims law (traceItems input before submissions) =
      Financial.inventoryClaims law ((law).rawItems before.raw word) := by
  ext ⟨instrument,debtor,creditor⟩
  have reported := Financial.the_actual_public_prefix_has_its_exact_original_claim_change
    input before submissions instrument debtor creditor
  have raw := (law).execute_financial_balance before.raw 0 word instrument debtor creditor
  have rawSame := every_submitted_primitive_keeps_the_original_raw_execution input before word same 0
  change (primitiveNext input before word).raw.claims instrument debtor creditor = _ at reported
  rw [rawSame] at reported
  change ((law).execute before.raw 0 word).final.claims instrument debtor creditor =
    before.raw.claims instrument debtor creditor + Financial.inventoryClaims law _ (instrument,debtor,creditor) at reported
  rw [← Financial.inventory_claims_are_the_original_financial_delta law _ instrument debtor creditor] at raw
  change Financial.inventoryClaims law (traceItems input before submissions) (instrument,debtor,creditor) =
    Financial.inventoryClaims law ((law).execute before.raw 0 word).items (instrument,debtor,creditor)
  linarith

include same in
omit [DecidableEq Port] in
theorem original_primitive_reports_keep_the_complete_material_change :
    Financial.inventoryMaterial law (traceItems input before submissions) =
      Financial.inventoryMaterial law ((law).rawItems before.raw word) := by
  ext ⟨person,good⟩
  have reported := actual_prefix_stock_is_exactly_its_complete_net_flow input before submissions person good
  have raw := (law).execute_material_balance before.raw 0 word person good
  have rawSame := every_submitted_primitive_keeps_the_original_raw_execution input before word same 0
  change (primitiveNext input before word).raw.stock person good = _ at reported
  rw [rawSame,complete_net_flow_counts_each_original_debit_and_credit_once] at reported
  rw [Financial.inventory_material_is_the_original_net_flow,
    Financial.inventory_material_is_the_original_net_flow]
  change (law).totalCredit _ person good - (law).totalDebit _ person good =
    (law).totalCredit ((law).execute before.raw 0 word).items person good -
      (law).totalDebit ((law).execute before.raw 0 word).items person good
  linarith

include same in
omit [DecidableEq Port] in
theorem original_primitive_reports_keep_the_complete_full_account :
    Accounting.Profit.fullIncome law (traceItems input before submissions) =
      Accounting.Profit.fullIncome law ((law).rawItems before.raw word) := by
  rw [Accounting.Profit.fullIncome,
    original_primitive_reports_keep_the_complete_financial_change input before word same,
    original_primitive_reports_keep_the_complete_material_change input before word same]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Settlement

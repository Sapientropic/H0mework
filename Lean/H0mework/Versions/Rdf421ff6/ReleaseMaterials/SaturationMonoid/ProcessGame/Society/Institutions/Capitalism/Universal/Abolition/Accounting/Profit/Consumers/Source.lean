import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Society
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Valuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Public
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Consumers

open Source.Program ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root
open Abolition.Completion.Actual.Dividend

noncomputable section

abbrev claimItem := Innovation.Control.Scenario.capitalItem ⟨0,by decide +kernel⟩

theorem the_original_capital_claim_has_positive_holder_income_without_new_production :
    Financial.fullChange Innovation.Control.Scenario.law claimItem.val.before claimItem.val.request
        (2,.material) = 2 ∧
      productionAt Innovation.Control.Scenario.law claimItem.val = 0 ∧
      societyRead .material
        (Financial.fullChange Innovation.Control.Scenario.law claimItem.val.before claimItem.val.request) = 0 := by
  have operation : claimItem.val.request.operation = .issue () 0 2 1 := rfl
  have actual : Innovation.Control.Scenario.law.Valid claimItem.val.before claimItem.val.request := by decide +kernel
  have income := Financial.issue_creates_the_original_creditor_asset_and_debtor_liability
    Innovation.Control.Scenario.law claimItem.val.before claimItem.val.request () 0 2 1 operation actual
  refine ⟨?_,?_,?_⟩
  · rw [income]
    simp [Innovation.Control.Scenario.law,Innovation.Trials.Example.law]
  · simp only [productionAt,operation]
  · rw [income,map_sub,society_read_single,society_read_single]
    norm_num

theorem the_original_capital_claim_is_marked_at_its_actual_controller :
    sourceOwnerMarked Innovation.Control.Scenario.law Innovation.Control.Scenario.start
      Innovation.Control.Scenario.capitalWord 0 2 = true := by decide +kernel

theorem the_original_capital_word_has_the_same_paid_account_without_control :
    let source := Innovation.Control.Scenario.law
    let initial := Innovation.Control.Scenario.start
    let word := Innovation.Control.Scenario.capitalWord
    (PublicFunction.physicalLaw source).next initial word = source.next initial word ∧
      fullIncome (PublicFunction.physicalLaw source) ((PublicFunction.physicalLaw source).rawItems initial word) =
        fullIncome source (source.rawItems initial word) ∧
      controlIncome (PublicFunction.physicalLaw source) initial word = 0 := by
  have actual : ∀ item ∈ Innovation.Control.Scenario.law.rawItems Innovation.Control.Scenario.start
      Innovation.Control.Scenario.capitalWord, Innovation.Control.Scenario.law.Valid item.before item.request := by decide +kernel
  have result := every_original_lawful_contribution_keeps_its_effect_and_full_account_without_control
    Innovation.Control.Scenario.law Innovation.Control.Scenario.start Innovation.Control.Scenario.capitalWord actual
  exact ⟨result.1,result.2.2.2.1,result.2.2.2.2⟩

def quote (price : ℚ) : Quotation (Party := Innovation.Installation.Party)
    (Good := Innovation.Installation.Good) (Technology := Nat) (Instrument := Unit) where
  unitPrice := fun _ _ => price
  rightsValue := fun _ _ _ => 0

abbrev openingAccount := NativeResponsibilityProcess.GeneratedState.initial
  (Epoch.Finance.process Innovation.Installation.input 0 0)

theorem a_market_repricing_can_report_profit_without_a_single_productive_request :
    bookIncome Innovation.Installation.input 0 0 Innovation.Installation.input.law Innovation.Installation.input.initial openingAccount []
        (quote 1) (quote 2) 2 .material = 2 ∧
      production Innovation.Installation.input.law
        (Innovation.Installation.input.law.rawItems Innovation.Installation.input.initial []) = 0 := by
  constructor
  · simp only [bookIncome,closingPosition,openingPosition,nativePosition,openingAccount,
      NativeResponsibilityProcess.GeneratedState.initial,ResponsibilityState.empty,List.map_nil,List.sum_nil,
      fullIncome,Financial.inventoryMaterial,Financial.inventoryClaims,RawLaw.rawItems,RawLaw.execute,
      map_zero,Finsupp.zero_apply,add_zero,quote]
    have distinct : (2 : Innovation.Installation.Party) ≠ 1 := by decide +kernel
    norm_num [Innovation.Installation.input,Innovation.Control.Scenario.genesis,distinct]
  · rfl

theorem repricing_does_not_duplicate_actual_source_income :
    bookIncome Innovation.Installation.input 0 0 Innovation.Installation.input.law Innovation.Installation.input.initial openingAccount []
      (quote 1) (quote 2) 2 .material =
        revaluation Innovation.Installation.input 0 0 Innovation.Installation.input.law Innovation.Installation.input.initial openingAccount []
          (quote 1) (quote 2) 2 .material :=
  (holding_without_any_new_request_has_only_valuation_income Innovation.Installation.input 0 0
    Innovation.Installation.input.law Innovation.Installation.input.initial openingAccount (quote 1) (quote 2) 2 .material).1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Consumers

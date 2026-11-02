import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Events

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Preparation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

abbrev Account := (Epoch.Finance.process input 0 count).GeneratedState
abbrev Claim := Epoch.Finance.NewClaim input 0 count

local instance (operation : Source.Program.Operation Party Good Nat Unit) : Decidable (Payment.NonFinancial operation) := by
  unfold Payment.NonFinancial
  cases operation <;> infer_instance

local instance (raw : InputAt) : Decidable (Payment.NonFinancialInput raw) := by
  unfold Payment.NonFinancialInput
  cases raw <;> infer_instance

def middle (oldPast : List InputAt) (version : Nat) : List InputAt :=
  [.primitive Control.Scenario.payout,.primitive quotedMechanism.investmentRequest,
   .primitive (Control.Scenario.discovery version),.primitive (Control.Scenario.production 0),
   .primitive rule.request,.code ⟨observedCode oldPast (Control.Scenario.discovery version)⟩]

def riskDebtor (version : Nat) : Party := if version = 0 then 1 else 0
def riskHolder (version : Nat) : Party := if version = 0 then 0 else 1
def riskUnits (version : Nat) : ℚ :=
  if version = 0 then Control.Scenario.coverageUnits else Control.Scenario.premiumUnits

theorem the_risk_is_the_original_signed_source_issue (version : Nat) :
    riskLiability version = Control.Scenario.request (riskDebtor version)
      (.issue () (riskDebtor version) (riskHolder version) (riskUnits version)) := by
  by_cases zero : version = 0 <;>
    simp only [riskLiability,riskDebtor,riskHolder,riskUnits,zero,if_true,if_false,
      Control.Scenario.successLiability,Control.Scenario.failureLiability]

theorem original_risk_units_are_positive (version : Nat) : 0 < riskUnits version := by
  unfold riskUnits
  split
  · rw [Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.2]
    norm_num
  · rw [Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.1]
    norm_num

theorem the_preparation_is_its_literal_original_financial_layout (oldPast : List InputAt) (version : Nat) :
    submittedInputs oldPast (Control.Scenario.discovery version) ++
        [.primitive (riskLiability version),.execute Control.Scenario.commonWork] =
      [.execute Control.Scenario.commonWork] ++ [.primitive Control.Scenario.issue] ++ middle oldPast version ++
        [.primitive (riskLiability version)] ++ [.execute Control.Scenario.commonWork] := by
  rw [submittedInputs,readInputs,the_pre_read_source_inventory_is_the_original_five_requests]
  rfl

theorem the_intermediate_requests_and_work_have_no_new_financial_instruction
    (oldPast : List InputAt) (version : Nat) :
    (∀ raw ∈ middle oldPast version, Payment.NonFinancialInput raw) ∧
      (∀ raw ∈ ([.execute Control.Scenario.commonWork] : List InputAt), Payment.NonFinancialInput raw) := by
  constructor
  · intro raw member
    simp only [middle,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · decide +kernel

theorem the_original_preparation_generates_its_two_exact_native_claims
    (origin : Functions.Revision.Context (input := input) (review := none) 0 count 0 0 0 count)
    (version : Nat) (before : Account) :
    ∃ loan risk : Claim,
      loan.instrument = () ∧ loan.debtor = 0 ∧ loan.holder = 1 ∧ loan.quantity = 3 ∧
      risk.instrument = () ∧ risk.debtor = riskDebtor version ∧ risk.holder = riskHolder version ∧
        risk.quantity = riskUnits version ∧
      Epoch.Finance.PublicPast.account input 0 count 0 0
          origin.germ.snapshot.past
          (submittedInputs origin.germ.snapshot.past
              (Control.Scenario.discovery version) ++
            [.primitive (riskLiability version),.execute Control.Scenario.commonWork]) before =
        (before.step (Epoch.Finance.process input 0 count) (.admit (.inr loan))).step
          (Epoch.Finance.process input 0 count) (.admit (.inr risk)) := by
  let oldPast := origin.germ.snapshot.past
  let loanWord : List InputAt := [.primitive Control.Scenario.issue]
  let work : List InputAt := [.execute Control.Scenario.commonWork]
  let afterLoan (loan : Claim) := before.step (Epoch.Finance.process input 0 count) (.admit (.inr loan))
  have kinds := the_intermediate_requests_and_work_have_no_new_financial_instruction oldPast version
  obtain ⟨loan,loanInstrument,loanDebtor,loanHolder,loanQuantity,loanPaid⟩ :=
    Events.a_signed_source_issue_generates_the_original_claim_and_native_admission
      (input := input) (depth := 0) (count := count) (prefixLimit := 0) (renewalLimit := 0)
      (origin := origin) work before () 0 1 3 false (by norm_num)
  obtain ⟨risk,riskInstrument,riskDebtorEq,riskHolderEq,riskQuantity,riskPaid⟩ :=
    Events.a_signed_source_issue_generates_the_original_claim_and_native_admission
      (input := input) (depth := 0) (count := count) (prefixLimit := 0) (renewalLimit := 0)
      (origin := origin) (work ++ loanWord ++ middle oldPast version) (afterLoan loan)
      () (riskDebtor version) (riskHolder version) (riskUnits version) false
      (original_risk_units_are_positive version).le
  refine ⟨loan,risk,loanInstrument,loanDebtor,loanHolder,loanQuantity,
    riskInstrument,riskDebtorEq,riskHolderEq,riskQuantity,?_⟩
  have first := Events.the_nonfinancial_source_prefix_preserves_the_original_native_state
    (origin := origin) [] work before kinds.2
  have middlePaid := Events.the_nonfinancial_source_prefix_preserves_the_original_native_state
    (origin := origin) (work ++ loanWord) (middle oldPast version) (afterLoan loan) kinds.1
  have final := Events.the_nonfinancial_source_prefix_preserves_the_original_native_state
    (origin := origin) (work ++ loanWord ++ middle oldPast version ++ [.primitive (riskLiability version)]) work
    ((afterLoan loan).step (Epoch.Finance.process input 0 count) (.admit (.inr risk))) kinds.2
  have loanExact : Epoch.Finance.PublicPast.foldFrom input 0 count 0 0 oldPast work loanWord before = afterLoan loan := loanPaid
  have riskExact : Epoch.Finance.PublicPast.foldFrom input 0 count 0 0 oldPast
      (work ++ loanWord ++ middle oldPast version) [.primitive (riskLiability version)] (afterLoan loan) =
        (afterLoan loan).step (Epoch.Finance.process input 0 count) (.admit (.inr risk)) := by
    simpa only [the_risk_is_the_original_signed_source_issue,Control.Scenario.request] using riskPaid
  change Epoch.Finance.PublicPast.account input 0 count 0 0 oldPast _ before = _
  rw [the_preparation_is_its_literal_original_financial_layout]
  change Epoch.Finance.PublicPast.foldFrom input 0 count 0 0 oldPast []
    (work ++ loanWord ++ middle oldPast version ++ [.primitive (riskLiability version)] ++ work) before = _
  simp only [the_original_public_fold_splits_at_its_actual_source_cut,List.nil_append,List.append_assoc]
  simp only [List.append_assoc] at riskExact final
  with_unfolding_all rw [first,loanExact,middlePaid,riskExact,final]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Preparation

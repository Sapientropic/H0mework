import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Forecast
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Envelope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Accounts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Rebind the proposed code to the original cut; neither its old initial
inventory nor its old permission interpreter supplies the quote. -/
def atCut (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (mechanism : Trials.Mechanism Party Good Port Technology Instrument) :=
  { mechanism with code := { mechanism.code with law := input.law, initial := current } }

variable (mechanism : Trials.Mechanism Party Good Port Technology Instrument)

def income (nature : mechanism.QuotedNature) (person : Party) (good : Good) : ℚ :=
  Arithmetic.completeIncome mechanism.code.law
    (mechanism.code.law.rawItems mechanism.code.initial (mechanism.word nature.val)) person good

theorem the_branch_income_is_its_complete_original_account
    (nature : mechanism.QuotedNature) (person : Party) (good : Good) :
    income mechanism nature person good = Accounting.Profit.fullIncome mechanism.code.law
      (mechanism.code.law.rawItems mechanism.code.initial (mechanism.word nature.val)) (person,good) :=
  Arithmetic.complete_income_is_the_original_full_account _ _ _ _

def signalDomain (signal : Fin mechanism.code.signals) : List mechanism.QuotedNature :=
  (natureDomain mechanism).filter fun nature => mechanism.paidSignal nature.val = some signal

theorem signalDomain_mem_iff (signal : Fin mechanism.code.signals) (nature : mechanism.QuotedNature) :
    nature ∈ signalDomain mechanism signal ↔ mechanism.paidSignal nature.val = some signal := by
  simp only [signalDomain,List.mem_filter,decide_eq_true_eq]
  exact and_iff_right (every_declared_nature_is_in_the_forecast_domain mechanism nature)

def riskRows (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals) : List (ℚ × ℚ) :=
  (signalDomain mechanism signal).map fun nature =>
    (providerOutside - income mechanism nature mechanism.terms.lender
      (mechanism.code.law.settlementUnit mechanism.terms.instrument),
     income mechanism nature mechanism.terms.borrower
      (mechanism.code.law.settlementUnit mechanism.terms.instrument) - payerOutside)

def accountsSafe (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals)
    (transfer : ℚ) : Prop :=
  ∀ nature : mechanism.QuotedNature, mechanism.paidSignal nature.val = some signal →
    providerOutside ≤ income mechanism nature mechanism.terms.lender
        (mechanism.code.law.settlementUnit mechanism.terms.instrument) + transfer ∧
      payerOutside ≤ income mechanism nature mechanism.terms.borrower
        (mechanism.code.law.settlementUnit mechanism.terms.instrument) - transfer

theorem the_original_branch_accounts_are_exactly_the_generated_intervals
    (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals) (transfer : ℚ) :
    accountsSafe mechanism providerOutside payerOutside signal transfer ↔
      ∀ row ∈ riskRows mechanism providerOutside payerOutside signal,
        row.1 ≤ transfer ∧ transfer ≤ row.2 := by
  unfold accountsSafe riskRows
  constructor
  · intro safe row member
    obtain ⟨nature,original,rfl⟩ := List.mem_map.mp member
    exact (Arithmetic.both_accounts_meet_their_baselines_iff _ _ _ _ _).mp
      (safe nature ((signalDomain_mem_iff mechanism signal nature).mp original))
  · intro safe nature observed
    apply (Arithmetic.both_accounts_meet_their_baselines_iff _ _ _ _ _).mpr
    exact safe _ (List.mem_map.mpr
      ⟨nature,(signalDomain_mem_iff mechanism signal nature).mpr observed,rfl⟩)

theorem every_priced_branch_keeps_both_original_accounts
    (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals)
    (plan : Quote (riskRows mechanism providerOutside payerOutside signal)) :
    accountsSafe mechanism providerOutside payerOutside signal plan.transfer :=
  (the_original_branch_accounts_are_exactly_the_generated_intervals mechanism _ _ _ _).mpr plan.all_branches

theorem every_safe_branch_rule_pays_at_least_the_generated_compensation
    (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals)
    (plan : Quote (riskRows mechanism providerOutside payerOutside signal)) (other : ℚ)
    (safe : accountsSafe mechanism providerOutside payerOutside signal other) :
    |plan.transfer| ≤ |other| :=
  plan.least_actual_payment other
    ((the_original_branch_accounts_are_exactly_the_generated_intervals mechanism _ _ _ _).mp safe)

theorem a_safe_different_amount_is_an_independent_surplus_distribution
    (providerOutside payerOutside : ℚ) (signal : Fin mechanism.code.signals)
    (plan : Quote (riskRows mechanism providerOutside payerOutside signal)) (other : ℚ)
    (safe : accountsSafe mechanism providerOutside payerOutside signal other)
    (different : other ≠ plan.transfer) : |plan.transfer| < |other| :=
  plan.unique_least_payment other
    ((the_original_branch_accounts_are_exactly_the_generated_intervals mechanism _ _ _ _).mp safe) different

def localTransfer (providerOutside payerOutside : ℚ)
    (signal : Fin mechanism.code.signals) : Option ℚ :=
  match quote (riskRows mechanism providerOutside payerOutside signal) with
  | .priced plan => some plan.transfer
  | .obstructed _ => none

theorem branches_with_the_same_paid_local_signal_receive_the_same_quote
    (providerOutside payerOutside : ℚ) (first second : mechanism.QuotedNature)
    (same : mechanism.paidSignal first.val = mechanism.paidSignal second.val) :
    (mechanism.paidSignal first.val).bind (localTransfer mechanism providerOutside payerOutside) =
      (mechanism.paidSignal second.val).bind (localTransfer mechanism providerOutside payerOutside) := by rw [same]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

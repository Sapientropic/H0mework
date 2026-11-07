import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Issues
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.NonFinancial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw.Members
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument) (members : List Party)

def Checks (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  Material.PeriodChecks input current members word ∧
    Root.Settlement.NonFinancial word

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks input current members word) := by unfold Checks; infer_instance

def words (budget : Nat) :=
  (Material.Migration.sourceWords input current budget).filter (Checks input current members)

def value (person : Party) (good : Good) (word : RawEvent Party Good Port Technology Instrument) : ℚ :=
  input.law.totalCredit (input.law.rawItems current word) person good -
    input.law.totalDebit (input.law.rawItems current word) person good

theorem word_mem_iff (budget : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    word ∈ words input current members budget ↔
      word ∈ Material.Migration.sourceWords input current budget ∧ Checks input current members word := by
  simp only [words,List.mem_filter,decide_eq_true_eq]

theorem every_generated_word_keeps_the_complete_original_claims
    (budget : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ words input current members budget) :
    (input.law.next current word).claims = current.claims :=
  ((word_mem_iff input current members budget word).mp generated).2.2.next_claims input.law current word

theorem every_generated_word_pays_each_original_member
    (budget : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ words input current members budget) (person : Party)
    (present : person ∈ members) :
    Exit.Necessity.BundlePaid input.law current word person (input.law.necessities current person) .necessity ∧
      Exit.Necessity.BundlePaid input.law current word person (input.law.mandatoryMaintenance current person) .maintenance :=
  ((word_mem_iff input current members budget word).mp generated).2.1.2.1 person present

theorem a_checked_value_is_its_complete_original_account
    (word : RawEvent Party Good Port Technology Instrument) (safe : Checks input current members word)
    (person : Party) (good : Good) :
    value input current person good word =
      Accounting.Profit.fullIncome input.law (input.law.rawItems current word) (person,good) := by
  let items := input.law.rawItems current word
  have zero : Abolition.Completion.Actual.Dividend.Financial.inventoryClaims input.law items = 0 := by
    ext address
    rcases address with ⟨instrument, debtor, creditor⟩
    rw [Abolition.Completion.Actual.Dividend.Financial.inventory_claims_are_the_original_financial_delta]
    have original := input.law.execute_financial_balance current 0 word instrument debtor creditor
    have same := safe.2.execute_claims input.law current 0 word
    rw [same] at original
    change current.claims instrument debtor creditor = current.claims instrument debtor creditor +
      input.law.totalFinancialDelta items instrument debtor creditor at original
    change input.law.totalFinancialDelta items instrument debtor creditor = 0
    linarith
  rw [Accounting.Profit.fullIncome,zero,map_zero,add_zero,
    Abolition.Completion.Actual.Dividend.Financial.inventory_material_is_the_original_net_flow]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

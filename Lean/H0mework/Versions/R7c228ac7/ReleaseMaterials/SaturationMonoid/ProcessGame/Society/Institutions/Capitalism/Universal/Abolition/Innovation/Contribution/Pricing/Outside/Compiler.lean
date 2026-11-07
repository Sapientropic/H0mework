import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside.Maximum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

open Source.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (budget : Nat) (person : Party) (good : Good)

structure Witness where
  word : RawEvent Party Good Port Technology Instrument
  generated : word ∈ Material.Migration.sourceWords input current budget
  checked : Checks input current members word
  maximal : ∀ other ∈ Material.Migration.sourceWords input current budget,
    Checks input current members other → value input current person good other ≤ value input current person good word

def Witness.amount (result : Witness input current members budget person good) : ℚ :=
  value input current person good result.word

inductive Issue (word : RawEvent Party Good Port Technology Instrument) : Type
  | period (failure : Material.PeriodIssue input current members word)
  | financial (request : Request Party Good Port Technology Instrument) (original : request ∈ word)
      (unsupported : ¬ Root.Settlement.NonFinancialRequest request)

theorem Issue.refutes {word : RawEvent Party Good Port Technology Instrument}
    (issue : Issue input current members word) : ¬ Checks input current members word := by
  intro safe
  cases issue with
  | period failure => exact failure.refutes input current members word safe.1
  | financial request original unsupported => exact unsupported (safe.2 request original)

def rejection (word : RawEvent Party Good Port Technology Instrument)
    (failed : ¬ Checks input current members word) : Issue input current members word :=
  match Material.checkPeriod input current members word with
  | .rejected failure => .period failure
  | .accepted paid =>
      match Root.Settlement.checkFinancial word with
      | .rejected request original unsupported => .financial request original unsupported
      | .accepted nonfinancial => False.elim (failed ⟨paid,nonfinancial⟩)

inductive Outcome : Type
  | found (result : Witness input current members budget person good)
  | obstructed (failures : ∀ word ∈ Material.Migration.sourceWords input current budget,
      Issue input current members word)

/-- A missing alternative retains every original source failure; it never
substitutes a cost-free holding option for the standing payments. -/
def generate : Outcome input current members budget person good :=
  match maximum (value input current person good) (words input current members budget) with
  | .empty empty => .obstructed (fun word original => rejection input current members word (by
      intro safe
      have inside := (word_mem_iff input current members budget word).mpr ⟨original,safe⟩
      rw [empty] at inside
      exact List.not_mem_nil inside))
  | .attained word inside dominates =>
      let original := (word_mem_iff input current members budget word).mp inside
      .found ⟨word,original.1,original.2,fun other available safe =>
        dominates other ((word_mem_iff input current members budget other).mpr ⟨available,safe⟩)⟩

def sourceOutside : Option (Witness input current members budget person good) :=
  match generate input current members budget person good with
  | .found result => some result
  | .obstructed _ => none

theorem Witness.amount_is_actually_attained_in_the_complete_account
    (result : Witness input current members budget person good) :
    result.amount = Accounting.Profit.fullIncome input.law
      (input.law.rawItems current result.word) (person,good) :=
  a_checked_value_is_its_complete_original_account input current members result.word result.checked person good

theorem Witness.every_original_feasible_alternative_is_below_the_attained_amount
    (result : Witness input current members budget person good)
    (other : RawEvent Party Good Port Technology Instrument)
    (available : other ∈ Material.Migration.sourceWords input current budget)
    (safe : Checks input current members other) :
    Accounting.Profit.fullIncome input.law (input.law.rawItems current other) (person,good) ≤ result.amount := by
  rw [← a_checked_value_is_its_complete_original_account input current members other safe person good]
  exact result.maximal other available safe

theorem Witness.the_selected_alternative_has_no_fresh_or_erased_financial_claim
    (result : Witness input current members budget person good) :
    (input.law.next current result.word).claims = current.claims :=
  result.checked.2.next_claims input.law current result.word

theorem every_obstruction_excludes_every_feasible_original_alternative
    (failures : ∀ word ∈ Material.Migration.sourceWords input current budget,
      Issue input current members word) :
    ∀ word ∈ Material.Migration.sourceWords input current budget, ¬ Checks input current members word :=
  fun word original => (failures word original).refutes input current members

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

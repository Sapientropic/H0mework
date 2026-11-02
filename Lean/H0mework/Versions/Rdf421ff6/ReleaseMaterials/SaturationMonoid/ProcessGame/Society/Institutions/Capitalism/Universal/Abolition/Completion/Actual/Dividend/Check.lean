import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

local notation "first" => seed input depth count prefixLimit renewalLimit oldPast
local notation "actual" => publicCurrent input depth count prefixLimit renewalLimit oldPast current
local notation "reference" => oldEndpoint input depth count prefixLimit renewalLimit oldPast current
local notation "periods" => baselineWords input (Root.Actual.Current.raw (seed input depth count prefixLimit renewalLimit oldPast))
  (horizon input depth count prefixLimit renewalLimit oldPast current)
local notation "items" => traceItems input first current.past
local notation "gain" => delta input depth count prefixLimit renewalLimit oldPast current
local notation "support" => comparisonCells input depth count prefixLimit renewalLimit oldPast current

def ActualNonFinancial : Prop := ∀ item ∈ items, Root.Settlement.NonFinancialRequest item.request

instance : Decidable (ActualNonFinancial input depth count prefixLimit renewalLimit oldPast current) := by
  unfold ActualNonFinancial
  infer_instance

def Checks : Prop :=
  Material.Dividend.NonFinancial periods ∧
    ActualNonFinancial input depth count prefixLimit renewalLimit oldPast current ∧
    (first).raw.clock < (actual).raw.clock ∧ (actual).raw.clock = (reference).clock ∧
    (∀ cell ∈ support, 0 ≤ gain cell.1 cell.2) ∧ ∃ cell ∈ support, 0 < gain cell.1 cell.2

instance : Decidable (Checks input depth count prefixLimit renewalLimit oldPast current) := by
  unfold Checks
  infer_instance

inductive Issue : Type
  | referenceFinancial (word : RawEvent Party Good Port Technology Instrument) (period : word ∈ periods)
      (request : Request Party Good Port Technology Instrument) (present : request ∈ word)
      (valuation : ¬ Root.Settlement.NonFinancialRequest request)
  | actualFinancial (item : ExecutionItem Party Good Port Technology Instrument) (original : item ∈ items)
      (valuation : ¬ Root.Settlement.NonFinancialRequest item.request)
  | noPositiveActualWindow (zero : (actual).raw.clock ≤ (first).raw.clock)
  | differentActualWindow (different : (actual).raw.clock ≠ (reference).clock)
  | originalBearerLoses (cell : Party × Good) (affected : cell ∈ support) (loss : gain cell.1 cell.2 < 0)
  | noStrictMaterialIncrease (nonpositive : ∀ cell ∈ support, gain cell.1 cell.2 ≤ 0)

theorem Issue.refutes (issue : Issue input depth count prefixLimit renewalLimit oldPast current) :
    ¬ Checks input depth count prefixLimit renewalLimit oldPast current := by
  intro checked
  cases issue with
  | referenceFinancial word period request present valuation => exact valuation (checked.1 word period request present)
  | actualFinancial item original valuation => exact valuation (checked.2.1 item original)
  | noPositiveActualWindow zero => exact (not_lt_of_ge zero) checked.2.2.1
  | differentActualWindow different => exact different checked.2.2.2.1
  | originalBearerLoses cell affected loss => exact (not_le_of_gt loss) (checked.2.2.2.2.1 cell affected)
  | noStrictMaterialIncrease nonpositive =>
    obtain ⟨cell, affected, positive⟩ := checked.2.2.2.2.2
    exact (not_lt_of_ge (nonpositive cell affected)) positive

inductive Decision : Type
  | accepted (checked : Checks input depth count prefixLimit renewalLimit oldPast current)
  | rejected (issue : Issue input depth count prefixLimit renewalLimit oldPast current)

/-- Financial changes require their original claims valuation before this
material-only order can admit them. They are never reported as a stock loss. -/
def check : Decision input depth count prefixLimit renewalLimit oldPast current :=
  match Material.inspectList Root.Settlement.NonFinancial periods with
  | .failure word period absent =>
    match Root.Settlement.checkFinancial word with
    | .accepted safe => False.elim (absent safe)
    | .rejected request present valuation => .rejected (.referenceFinancial word period request present valuation)
  | .clear nonfinancial =>
    match Material.inspectList (fun item : ExecutionItem Party Good Port Technology Instrument =>
        Root.Settlement.NonFinancialRequest item.request) items with
    | .failure item original valuation => .rejected (.actualFinancial item original valuation)
    | .clear actualSafe =>
      if positive : (first).raw.clock < (actual).raw.clock then
        if same : (actual).raw.clock = (reference).clock then
          match Material.inspectList (fun cell : Party × Good => 0 ≤ gain cell.1 cell.2) support with
          | .failure cell affected loss => .rejected (.originalBearerLoses cell affected (lt_of_not_ge loss))
          | .clear noLoss =>
            match Material.inspectList (fun cell : Party × Good => gain cell.1 cell.2 ≤ 0) support with
            | .clear noGain => .rejected (.noStrictMaterialIncrease noGain)
            | .failure cell affected strict => .accepted
                ⟨nonfinancial, actualSafe, positive, same, noLoss, cell, affected, lt_of_not_ge strict⟩
        else .rejected (.differentActualWindow same)
      else .rejected (.noPositiveActualWindow (le_of_not_gt positive))

theorem all_original_bearers_and_goods_have_no_material_loss
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current) (person : Party) (good : Good) :
    (reference).stock person good ≤ (actual).raw.stock person good := by
  have positive : 0 ≤ gain person good := by
    by_cases affected : (person, good) ∈ support
    · exact checked.2.2.2.2.1 _ affected
    · rw [no_unlisted_bearer_or_good_has_a_hidden_dividend input depth count prefixLimit renewalLimit oldPast current
        person good affected]
  rw [the_dividend_is_the_actual_public_stock_minus_its_frozen_reference] at positive
  exact sub_nonneg.mp positive

theorem one_literal_material_unit_strictly_increases
    (checked : Checks input depth count prefixLimit renewalLimit oldPast current) :
    ∃ person good, (reference).stock person good < (actual).raw.stock person good := by
  obtain ⟨cell, _affected, positive⟩ := checked.2.2.2.2.2
  rw [the_dividend_is_the_actual_public_stock_minus_its_frozen_reference] at positive
  exact ⟨cell.1, cell.2, sub_pos.mp positive⟩

#print axioms check
#print axioms Issue.refutes
#print axioms all_original_bearers_and_goods_have_no_material_loss
#print axioms one_literal_material_unit_strictly_increases

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

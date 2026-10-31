import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Settled.Account
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Account

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Evolution.Sparse
open Abolition.Completion.Actual.Dividend

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (proposal : RawEvent Party Good Port Technology Instrument)

local notation "before" => Current.state claim current
local notation "after" => Current.state claim (nextCurrent claim current proposal)

def items := current.actualLaw.rawItems (before).raw (Gate.executableWord claim current proposal)

theorem the_native_financial_delta_is_zero_on_the_actual_whole_ledger :
    Financial.inventoryClaims current.actualLaw (items claim current proposal) = 0 := by
  ext key
  rcases key with ⟨instrument,debtor,holder⟩
  unfold items
  rw [Profit.the_original_financial_component_is_the_actual_claim_matrix_change,
    ← the_actual_raw_interpreter_is_executed,every_old_claim_is_literal]
  exact sub_self _

theorem the_full_income_is_the_actual_stock_delta (person : Party) (good : Good) :
    Profit.fullIncome current.actualLaw (items claim current proposal) (person,good) =
      (after).raw.stock person good - (before).raw.stock person good := by
  have zero := the_native_financial_delta_is_zero_on_the_actual_whole_ledger claim current proposal
  unfold items at zero ⊢
  rw [Profit.the_original_full_account_uses_its_actual_stock_and_financial_changes,
    ← the_actual_raw_interpreter_is_executed,zero,map_zero,Finsupp.zero_apply,add_zero]

theorem the_paid_actual_row_cannot_increase_any_retained_stock
    (paid : Responsibility.Family.State.isPaid claim (before)) (person : Party) (good : Good) :
    (after).raw.stock person good ≤ (before).raw.stock person good := by
  rw [the_actual_raw_interpreter_is_executed,Gate.executableWord_eq]
  exact Settled.the_paid_source_gate_prevents_actual_gain_for_every_original_bearer claim (before)
    current.actualLaw current.members proposal paid person good

/-- The old ledger and its source-event fibre can be infinite or proof
relevant. The coalition restricts this actual action's finite effect only. -/
theorem every_coalition_has_nonpositive_full_income_on_the_paid_actual_row
    (paid : Responsibility.Family.State.isPaid claim (before))
    (members : Party → Bool) (good : Good) :
    Coalition.read members good (Profit.fullIncome current.actualLaw (items claim current proposal)) ≤ 0 := by
  apply read_nonpositive
  intro key
  rw [the_full_income_is_the_actual_stock_delta]
  exact sub_nonpos.mpr (the_paid_actual_row_cannot_increase_any_retained_stock claim current proposal paid key.1 key.2)

theorem every_coalition_keeps_its_actual_consumption_in_the_full_income
    (paid : Responsibility.Family.State.isPaid claim (before))
    (members : Party → Bool) (good : Good) :
    Coalition.read members good (Profit.fullIncome current.actualLaw (items claim current proposal)) +
      Coalition.read members good (Settled.consumed current.actualLaw (items claim current proposal)) = 0 := by
  unfold items
  rw [Gate.executableWord_eq]
  exact Settled.every_coalition_has_zero_unbacked_income_on_the_paid_original_row claim (before)
    current.actualLaw current.members proposal paid members good

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse

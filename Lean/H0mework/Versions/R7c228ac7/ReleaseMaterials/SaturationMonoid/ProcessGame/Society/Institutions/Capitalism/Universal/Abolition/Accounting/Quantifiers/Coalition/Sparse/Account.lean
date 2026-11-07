import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse.Balance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Evolution.Sparse

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)

/-- This is a fold of the actual finite action trace, independent of the
size of the old ledger and of the source's occurrence or open fibres. -/
def income {source target : Current (oldN := oldN) claim} :
    History.Actual claim source target → Profit.Vector (Party := Party) (Good := Good)
  | .empty _ => 0
  | .step current programme input later =>
    Profit.fullIncome current.actualLaw (items claim (Mechanism.native claim current programme input)
      (Mechanism.word claim current programme input)) + income later

def consumed {source target : Current (oldN := oldN) claim} :
    History.Actual claim source target → Profit.Vector (Party := Party) (Good := Good)
  | .empty _ => 0
  | .step current programme input later =>
    Settled.consumed current.actualLaw (items claim (Mechanism.native claim current programme input)
      (Mechanism.word claim current programme input)) + consumed later

variable {source target : Current (oldN := oldN) claim}

theorem the_history_full_income_is_its_actual_stock_delta
    (history : History.Actual claim source target) (person : Party) (good : Good) :
    income claim history (person,good) =
      (Current.state claim target).raw.stock person good - (Current.state claim source).raw.stock person good := by
  induction history with
  | empty => simp only [income,Finsupp.zero_apply,sub_self]
  | step current programme input later inherited =>
    have first := the_full_income_is_the_actual_stock_delta claim (Mechanism.native claim current programme input)
      (Mechanism.word claim current programme input) person good
    rw [Mechanism.source_state_is_the_same_original_row] at first
    change Profit.fullIncome current.actualLaw (items claim (Mechanism.native claim current programme input)
        (Mechanism.word claim current programme input)) (person,good) =
      (Current.state claim (Mechanism.next claim current programme input)).raw.stock person good -
        (Current.state claim current).raw.stock person good at first
    change _ + income claim later (person,good) = _
    rw [first,inherited]
    ring

theorem every_coalition_has_nonpositive_income_along_every_paid_row_history
    (history : History.Actual claim source target)
    (paid : Responsibility.Family.State.isPaid claim (Current.state claim source))
    (members : Party → Bool) (good : Good) : Coalition.read members good (income claim history) ≤ 0 := by
  apply read_nonpositive
  intro key
  rw [the_history_full_income_is_its_actual_stock_delta]
  exact sub_nonpos.mpr (every_history_keeps_each_actual_stock_nonincreasing_after_payment claim history paid key.1 key.2)

theorem every_coalition_keeps_its_actual_consumption_along_every_history
    (history : History.Actual claim source target) :
    Responsibility.Family.State.isPaid claim (Current.state claim source) →
      ∀ (members : Party → Bool) good,
        Coalition.read members good (income claim history) + Coalition.read members good (consumed claim history) = 0 := by
  induction history with
  | empty => exact fun _ _ _ => by simp only [income,consumed,map_zero,add_zero]
  | step current programme input later inherited =>
    intro paid members good
    have nativePaid : Responsibility.Family.State.isPaid claim (Current.state claim (Mechanism.native claim current programme input)) := by
      rw [Mechanism.source_state_is_the_same_original_row]
      exact paid
    have first := every_coalition_keeps_its_actual_consumption_in_the_full_income claim
      (Mechanism.native claim current programme input) (Mechanism.word claim current programme input) nativePaid members good
    change Coalition.read members good (Profit.fullIncome current.actualLaw
        (items claim (Mechanism.native claim current programme input) (Mechanism.word claim current programme input))) +
      Coalition.read members good (Settled.consumed current.actualLaw
        (items claim (Mechanism.native claim current programme input) (Mechanism.word claim current programme input))) = 0 at first
    have tail := inherited (a_new_mechanism_keeps_an_actual_paid_row_paid claim current programme input paid) members good
    simp only [income,consumed,map_add]
    linarith

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse

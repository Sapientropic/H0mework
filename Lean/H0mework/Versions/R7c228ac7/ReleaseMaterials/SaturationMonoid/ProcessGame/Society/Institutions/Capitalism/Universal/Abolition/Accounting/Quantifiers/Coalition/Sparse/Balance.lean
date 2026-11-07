import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse.Current
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.History.Open

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

theorem a_new_mechanism_keeps_an_actual_paid_row_paid
    (current : Current (oldN := oldN) claim) (programme : Mechanism.Programme claim)
    (input : Request Party Good Port Technology Instrument)
    (paid : Responsibility.Family.State.isPaid claim (Current.state claim current)) :
    Responsibility.Family.State.isPaid claim (Current.state claim (Mechanism.next claim current programme input)) := by
  intro key original
  exact le_antisymm (by simpa only [paid key original] using
    Mechanism.no_original_cell_is_refilled claim current programme input key)
    ((Current.state claim (Mechanism.next claim current programme input)).nonnegative key)

theorem a_new_mechanism_cannot_increase_stock_from_the_paid_row
    (current : Current (oldN := oldN) claim) (programme : Mechanism.Programme claim)
    (input : Request Party Good Port Technology Instrument)
    (paid : Responsibility.Family.State.isPaid claim (Current.state claim current)) (person : Party) (good : Good) :
    (Current.state claim (Mechanism.next claim current programme input)).raw.stock person good ≤
      (Current.state claim current).raw.stock person good := by
  have nativePaid : Responsibility.Family.State.isPaid claim
      (Current.state claim (Mechanism.native claim current programme input)) := by
    rw [Mechanism.source_state_is_the_same_original_row]
    exact paid
  have actual := the_paid_actual_row_cannot_increase_any_retained_stock claim
    (Mechanism.native claim current programme input) (Mechanism.word claim current programme input) nativePaid person good
  rw [Mechanism.source_state_is_the_same_original_row] at actual
  exact actual

variable {source target : Current (oldN := oldN) claim}

theorem every_history_keeps_the_actual_paid_row_paid
    (history : History.Actual claim source target)
    (paid : Responsibility.Family.State.isPaid claim (Current.state claim source)) :
    Responsibility.Family.State.isPaid claim (Current.state claim target) := by
  intro key original
  exact le_antisymm (by simpa only [paid key original] using
    History.every_history_preserves_each_original_liability claim history key) ((Current.state claim target).nonnegative key)

theorem every_history_keeps_each_actual_stock_nonincreasing_after_payment
    (history : History.Actual claim source target) :
    Responsibility.Family.State.isPaid claim (Current.state claim source) →
      ∀ person good, (Current.state claim target).raw.stock person good ≤ (Current.state claim source).raw.stock person good := by
  induction history with
  | empty => exact fun _ _ _ => le_rfl
  | step current programme input later inherited =>
    intro paid person good
    exact (inherited (a_new_mechanism_keeps_an_actual_paid_row_paid claim current programme input paid) person good).trans
      (a_new_mechanism_cannot_increase_stock_from_the_paid_row claim current programme input paid person good)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Sparse
